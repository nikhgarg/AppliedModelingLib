#!/usr/bin/env python3
"""Validate a historical selected-review plus overlay composition.

This is a deliberately narrow recovery adapter.  It does not make an old
selected attestation current, and it does not infer an obligation match from a
judgment key, declaration name, or binder spelling.  Instead it replays the
two historical evidence lanes against an archived raw receipt and requires a
new, current-protocol full parent attestation before exposing an in-memory
normal-form attestation to a later consumer.

The historical selected-sidecar byte preimage may be unavailable after a
materialized composition replaced the canonical sidecar.  In that case the
selected response *content* is replayed from the immutable base sidecar and
selected attestation.  Every generated group still has to be covered exactly
once by the selected-or-overlay partition, with a complete generator-derived
descriptor receipt.  Storage keys only locate the response slot within this
one archived ledger; descriptor multisets establish completeness, and each
slot is additionally pinned to its raw descriptor before a response is read.
"""

from __future__ import annotations

import copy
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in focused tests.
    from scripts import source_record_current_revalidation as CURRENT
    from scripts import source_record_differential_revalidation as DIFFERENTIAL
    from scripts import source_record_obligation_groups as OBLIGATIONS
    from scripts.formalization_protocol import (
        FORMALIZATION_REVIEW_PROTOCOL_FIELD,
        formalization_protocol_receipt_matches,
    )
    from scripts.source_record_integrity import canonical_digest_payload
except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
    import source_record_current_revalidation as CURRENT
    import source_record_differential_revalidation as DIFFERENTIAL
    import source_record_obligation_groups as OBLIGATIONS
    from formalization_protocol import (
        FORMALIZATION_REVIEW_PROTOCOL_FIELD,
        formalization_protocol_receipt_matches,
    )
    from source_record_integrity import canonical_digest_payload


SCHEMA = 1
ARTIFACT_KIND = "source_record_historical_authenticated_composition_attestation"
POLICY_VERSION = (
    "source-record-v10-historical-selected-overlay-composition-attestation-v1"
)
INTEGRITY_FIELD = "source_record_historical_composition_attestation_sha256"
COMPOSITION_FIELD = "historical_authenticated_composition"
COMPOSITION_SCHEMA = 1
COMPOSITION_POLICY_VERSION = (
    "source-record-v10-historical-selected-overlay-composition-replay-v1"
)
ARCHIVED_RAW_REPLAY_MODE = "semantic_receipt_equivalent_archive"
SELECTED_SIDECAR_REPLAY_MODE = "projected_composed_ledger"
REVIEW_SCOPE = "all_current_generated_judgment_keys"
SEMANTIC_SCOPE = "all_current_semantic_model_judgment_groups"
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)


class SourceRecordHistoricalCompositionAttestationError(ValueError):
    """Raised when a historical selected-plus-overlay composition is inadmissible."""


@dataclass(frozen=True)
class ValidatedHistoricalCompositionAttestation:
    """A replayed composition plus a normal-form full-attestation projection.

    ``normalized_full_attestation`` is intentionally in-memory only.  A
    future ``source_record_semantic_rebind`` integration must invoke this
    validator first; serializing the projection alone would discard the
    composition provenance that made the special recovery route admissible.
    """

    normalized_full_attestation: dict[str, Any]
    archived_raw_audit: dict[str, Any]
    composed_sidecar: dict[str, Any]
    selected_descriptor_multiset: tuple[str, ...]
    overlay_descriptor_multiset: tuple[str, ...]
    complete_descriptor_multiset: tuple[str, ...]


def _canonical_digest(payload: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(payload), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _read_json_object_with_sha256(path: Path, *, label: str) -> tuple[dict[str, Any], str]:
    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordHistoricalCompositionAttestationError(
            f"could not read {label} at {path}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceRecordHistoricalCompositionAttestationError(
            f"{label} at {path} is not a JSON object"
        )
    return payload, hashlib.sha256(contents).hexdigest()


def _relative_paper_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordHistoricalCompositionAttestationError(
            f"{path} must remain inside {paper_dir}"
        ) from exc


def _resolve_paper_relative_path(value: object, paper_dir: Path, *, label: str) -> Path:
    text = str(value or "").strip()
    pure = PurePosixPath(text)
    if (
        not text
        or pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise SourceRecordHistoricalCompositionAttestationError(
            f"{label} must be a normalized paper-relative path"
        )
    path = (paper_dir / Path(*pure.parts)).resolve()
    if _relative_paper_path(path, paper_dir) != text:
        raise SourceRecordHistoricalCompositionAttestationError(
            f"{label} is not canonical"
        )
    return path


def _snapshot_matches(
    path: Path, supplied: Mapping[str, Any], *, label: str
) -> tuple[dict[str, Any], str]:
    saved, digest = _read_json_object_with_sha256(path, label=label)
    if canonical_digest_payload(saved) != canonical_digest_payload(supplied):
        raise SourceRecordHistoricalCompositionAttestationError(
            f"supplied {label} does not match immutable snapshot bytes"
        )
    return saved, digest


def _non_evidence(payload: Mapping[str, Any]) -> bool:
    if any(
        bool(payload.get(marker))
        for marker in (
            "candidate_only",
            "not_evidence",
            "must_not_be_written_to_repository_sidecar",
            "non_evidence_scaffold",
        )
    ):
        return True
    kind = str(payload.get("artifact_kind") or "").strip().lower()
    validator_type = str(payload.get("validator_type") or "").strip().lower()
    return any(token in value for token in ("candidate", "proposal") for value in (kind, validator_type))


def _descriptor_multiset(ledger: Mapping[str, str]) -> tuple[str, ...]:
    """Return descriptor occurrences, retaining equal descriptors in distinct slots."""

    return tuple(sorted(str(value) for value in ledger.values()))


def descriptor_multiset_sha256(ledger: Mapping[str, str]) -> str:
    """Digest descriptor occurrences rather than a set of descriptor values."""

    return _canonical_digest(list(_descriptor_multiset(ledger)))


def _require_snapshot_record(
    record: object,
    *,
    path: Path,
    digest: str,
    paper_dir: Path,
    label: str,
    payload: Mapping[str, Any] | None = None,
) -> None:
    if not isinstance(record, Mapping):
        raise SourceRecordHistoricalCompositionAttestationError(
            f"parent composition has no {label} snapshot record"
        )
    if str(record.get("path") or "").strip() != _relative_paper_path(path, paper_dir):
        raise SourceRecordHistoricalCompositionAttestationError(
            f"parent composition names a different {label} path"
        )
    if _sha256(record.get("file_sha256")) != digest:
        raise SourceRecordHistoricalCompositionAttestationError(
            f"parent composition {label} bytes do not match"
        )
    if payload is None:
        return
    aggregate = _sha256(payload.get("source_record_audit_sha256"))
    integrity = _sha256(payload.get("source_record_audit_integrity_sha256"))
    if _sha256(record.get("source_record_audit_sha256")) != aggregate:
        raise SourceRecordHistoricalCompositionAttestationError(
            f"parent composition {label} aggregate raw receipt does not match"
        )
    if _sha256(record.get("source_record_audit_integrity_sha256")) != integrity:
        raise SourceRecordHistoricalCompositionAttestationError(
            f"parent composition {label} integrity receipt does not match"
        )


def _archived_statement_map_snapshot(
    composition: Mapping[str, Any],
    *,
    raw_audit: Mapping[str, Any],
    paper: str,
    paper_dir: Path,
) -> Mapping[str, Any] | None:
    """Load an optional map snapshot needed for historic corrected targets.

    A raw audit carries a map *digest* but not necessarily a complete map.  A
    historical receipt may therefore validate literal source routes from its
    embedded raw context alone, while an approved corrected target needs this
    separately byte-pinned map snapshot.  The snapshot is never a fallback to
    the live map: it must be the exact map bytes named by the archived raw
    receipt.
    """

    record = composition.get("archived_statement_map")
    if record is None:
        return None
    if not isinstance(record, Mapping) or set(record) != {
        "path",
        "file_sha256",
        "paper_statement_map_sha256",
    }:
        raise SourceRecordHistoricalCompositionAttestationError(
            "parent composition archived statement-map snapshot is malformed"
        )
    path = _resolve_paper_relative_path(
        record.get("path"), paper_dir, label="archived statement-map path"
    )
    statement_map, file_sha256 = _read_json_object_with_sha256(
        path, label="archived statement map"
    )
    raw_map_sha256 = _sha256(raw_audit.get("paper_statement_map_sha256"))
    if not raw_map_sha256:
        raise SourceRecordHistoricalCompositionAttestationError(
            "archived raw audit has no paper-statement-map receipt"
        )
    if (
        _sha256(record.get("file_sha256")) != file_sha256
        or _sha256(record.get("paper_statement_map_sha256")) != raw_map_sha256
        or file_sha256 != raw_map_sha256
    ):
        raise SourceRecordHistoricalCompositionAttestationError(
            "archived statement-map snapshot bytes do not match the archived raw receipt"
        )
    if statement_map.get("paper") not in {None, paper}:
        raise SourceRecordHistoricalCompositionAttestationError(
            "archived statement-map snapshot belongs to another paper"
        )
    return statement_map


def _descriptor_ledger(value: object, *, label: str) -> dict[str, str]:
    try:
        return CURRENT._descriptor_ledger(value, field=label)
    except CURRENT.SourceRecordCurrentRevalidationError as exc:
        raise SourceRecordHistoricalCompositionAttestationError(str(exc)) from exc


def _raw_descriptor_ledger(
    raw_audit: Mapping[str, Any], *, label: str
) -> tuple[dict[str, str], dict[str, dict[str, object]]]:
    groups, errors = OBLIGATIONS.raw_source_record_obligation_groups(raw_audit)
    if errors:
        examples = ", ".join(sorted(errors)[:5])
        raise SourceRecordHistoricalCompositionAttestationError(
            f"{label} raw audit has malformed semantic groups: {examples}"
        )
    ledger: dict[str, str] = {}
    for raw_key, group in groups.items():
        key = str(raw_key or "").strip()
        descriptor = _sha256(group.get("descriptor_sha256"))
        if not key or not descriptor or key in ledger:
            raise SourceRecordHistoricalCompositionAttestationError(
                f"{label} raw audit has an empty, duplicate, or unpinned descriptor group"
            )
        ledger[key] = descriptor
    if not ledger:
        raise SourceRecordHistoricalCompositionAttestationError(
            f"{label} raw audit has no generated semantic groups"
        )
    return ledger, groups


def _expected_pins(
    current_groups: Mapping[str, list[tuple[str, Mapping[str, Any]]]], key: str
) -> frozenset[tuple[str, int, str]]:
    try:
        records = CURRENT._current_item_pins(current_groups[key])
    except (KeyError, CURRENT.SourceRecordCurrentRevalidationError) as exc:
        raise SourceRecordHistoricalCompositionAttestationError(
            f"raw group `{key}` has invalid current item pins: {exc}"
        ) from exc
    return frozenset(
        (
            str(record["kind"]),
            CURRENT.SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            str(record["source_record_item_sha256"]),
        )
        for record in records
    )


def _check_item_pins(
    item: Mapping[str, Any],
    *,
    current_groups: Mapping[str, list[tuple[str, Mapping[str, Any]]]],
    key: str,
    label: str,
) -> None:
    expected = _expected_pins(current_groups, key)
    actual = CURRENT.REPOSITORY.source_record_judgment_item_digest_pins(item)
    if expected and actual != expected:
        raise SourceRecordHistoricalCompositionAttestationError(
            f"{label} `{key}` has stale or incomplete current item pins"
        )
    if not expected and actual:
        raise SourceRecordHistoricalCompositionAttestationError(
            f"{label} `{key}` has a partial item pin"
        )


def _selected_attestation_error(
    selected_attestation: Mapping[str, Any],
    *,
    paper: str,
    raw_audit: Mapping[str, Any],
    base_path: Path,
    base_sha256: str,
    overlay_logical_path: Path,
    overlay_sha256: str,
    selected_ledger: Mapping[str, str],
    overlay_ledger: Mapping[str, str],
    selected_metadata: Mapping[str, Any],
    paper_dir: Path,
) -> str:
    """Validate the historical selected reviewer evidence below the new parent.

    The child may predate the scoped protocol field.  A present scoped receipt
    must still be current, but an absent one is handled only because the
    *parent* below carries a new current-protocol full-attestation receipt.
    This function is intentionally private to this special recovery module.
    """

    if selected_attestation.get("schema") != CURRENT.SELECTED_CURRENT_REVALIDATION_SCHEMA:
        return "historical selected attestation has an unsupported schema"
    if selected_attestation.get("artifact_kind") != CURRENT.SELECTED_CURRENT_REVALIDATION_ATTESTATION_KIND:
        return "historical selected attestation has the wrong artifact kind"
    if selected_attestation.get("policy_version") != CURRENT.SELECTED_CURRENT_REVALIDATION_POLICY_VERSION:
        return "historical selected attestation has the wrong policy version"
    if selected_attestation.get("paper") != paper:
        return "historical selected attestation belongs to another paper"
    if _non_evidence(selected_attestation):
        return "historical selected attestation is marked non-evidence"
    if FORMALIZATION_REVIEW_PROTOCOL_FIELD in selected_attestation and not formalization_protocol_receipt_matches(
        selected_attestation, scope="review"
    ):
        return "historical selected attestation carries a stale review-protocol receipt"
    if selected_attestation.get("reviewed_current_semantics") is not True:
        return "historical selected attestation does not affirm semantic review"
    if str(selected_attestation.get("review_scope") or "").strip() != CURRENT.SELECTED_CURRENT_REVALIDATION_SCOPE:
        return "historical selected attestation has the wrong review scope"
    if not str(selected_attestation.get("reviewer") or "").strip() or not str(
        selected_attestation.get("validated_at") or ""
    ).strip():
        return "historical selected attestation lacks reviewer or validation time"
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    if _sha256(selected_attestation.get("current_source_record_audit_sha256")) != raw_digest:
        return "historical selected attestation is not bound to the archived raw receipt"
    if _sha256(selected_attestation.get("generated_judgment_keys_sha256")) != CURRENT.generated_judgment_keys_sha256(raw_audit):
        return "historical selected attestation has stale generated-key coverage"
    if _sha256(selected_attestation.get("generated_judgment_surface_sha256")) != CURRENT.generated_judgment_surface_sha256(raw_audit):
        return "historical selected attestation has stale generated-surface coverage"
    if str(selected_attestation.get("prior_judgment_sidecar_path") or "").strip() != _relative_paper_path(base_path, paper_dir):
        return "historical selected attestation names a different base sidecar"
    if _sha256(selected_attestation.get("prior_judgment_sidecar_sha256")) != base_sha256:
        return "historical selected attestation base-sidecar bytes do not match"
    if str(selected_attestation.get("differential_overlay_path") or "").strip() != _relative_paper_path(overlay_logical_path, paper_dir):
        return "historical selected attestation names a different overlay"
    if _sha256(selected_attestation.get("differential_overlay_sha256")) != overlay_sha256:
        return "historical selected attestation overlay bytes do not match"

    try:
        attested_selected = _descriptor_ledger(
            selected_attestation.get("selected_current_group_descriptors"),
            label="historical selected attestation selected descriptor ledger",
        )
        attested_overlay = _descriptor_ledger(
            selected_attestation.get("differential_overlay_current_group_descriptors"),
            label="historical selected attestation overlay descriptor ledger",
        )
        metadata_selected = _descriptor_ledger(
            selected_metadata.get("selected_current_group_descriptors"),
            label="historical selected metadata selected descriptor ledger",
        )
        metadata_overlay = _descriptor_ledger(
            selected_metadata.get("differential_overlay_current_group_descriptors"),
            label="historical selected metadata overlay descriptor ledger",
        )
    except SourceRecordHistoricalCompositionAttestationError as exc:
        return str(exc)
    if dict(selected_ledger) != attested_selected or dict(overlay_ledger) != attested_overlay:
        return "historical selected attestation descriptor partition differs from the composed ledger"
    if metadata_selected != attested_selected or metadata_overlay != attested_overlay:
        return "historical selected metadata descriptor partition differs from its attestation"
    for payload, prefix in (
        (selected_attestation, "historical selected attestation"),
        (selected_metadata, "historical selected metadata"),
    ):
        if _sha256(payload.get("selected_current_group_descriptors_sha256")) != _canonical_digest(attested_selected):
            return f"{prefix} selected descriptor-ledger digest is stale"
        if _sha256(payload.get("differential_overlay_current_group_descriptors_sha256")) != _canonical_digest(attested_overlay):
            return f"{prefix} overlay descriptor-ledger digest is stale"
    if selected_metadata.get("schema") != CURRENT.SELECTED_CURRENT_REVALIDATION_SCHEMA:
        return "historical selected metadata has an unsupported schema"
    if selected_metadata.get("policy_version") != CURRENT.SELECTED_CURRENT_REVALIDATION_POLICY_VERSION:
        return "historical selected metadata has the wrong policy version"
    if _sha256(selected_metadata.get("current_source_record_audit_sha256")) != raw_digest:
        return "historical selected metadata is not bound to the archived raw receipt"
    if _sha256(selected_metadata.get("generated_judgment_keys_sha256")) != CURRENT.generated_judgment_keys_sha256(raw_audit):
        return "historical selected metadata has stale generated-key coverage"
    if _sha256(selected_metadata.get("generated_judgment_surface_sha256")) != CURRENT.generated_judgment_surface_sha256(raw_audit):
        return "historical selected metadata has stale generated-surface coverage"
    if str(selected_metadata.get("review_scope") or "").strip() != CURRENT.SELECTED_CURRENT_REVALIDATION_SCOPE:
        return "historical selected metadata has the wrong review scope"
    return ""


def _selected_projection_error(
    selected_items: Mapping[str, Mapping[str, Any]],
    *,
    selected_attestation: Mapping[str, Any],
    selected_attestation_sha256: str,
    selected_metadata: Mapping[str, Any],
    base_sidecar: Mapping[str, Any],
    raw_audit: Mapping[str, Any],
    selected_ledger: Mapping[str, str],
    current_groups: Mapping[str, list[tuple[str, Mapping[str, Any]]]],
    paper_dir: Path,
    archived_statement_map: Mapping[str, Any],
) -> str:
    if set(selected_items) != set(selected_ledger):
        return "composed sidecar selected projection does not cover its descriptor ledger"
    try:
        base_items = CURRENT._sidecar_items(base_sidecar, paper=selected_attestation["paper"])
        expected_items = CURRENT._selected_expected_semantic_items(
            base_items,
            selected_attestation,
            selected_keys=set(selected_ledger),
            current_raw_audit=raw_audit,
            selected_descriptors=selected_ledger,
            paper_dir=paper_dir,
        )
        # Match the ordinary selected-rebind replay: source association pins
        # are regenerated from the exact raw group, never taken from a name.
        # This is historical evidence, so use the byte-pinned source map that
        # generated the archived raw association rather than the live map.
        CURRENT._reproject_current_generated_association_credentials(
            raw_audit,
            expected_items,
            paper_dir=paper_dir,
            source_target_statement_map=archived_statement_map,
        )
    except (CURRENT.SourceRecordCurrentRevalidationError, KeyError) as exc:
        return "historical selected responses cannot be replayed: " + str(exc)
    if _canonical_digest(CURRENT._selected_semantic_judgment_ledger(selected_items)) != _canonical_digest(
        CURRENT._selected_semantic_judgment_ledger(expected_items)
    ):
        return "historical selected response semantic ledger does not replay from base evidence and attestation"

    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    reviewer = str(selected_attestation.get("reviewer") or "").strip()
    validated_at = str(selected_attestation.get("validated_at") or "").strip()
    for key, item in selected_items.items():
        if _sha256(item.get("source_record_audit_sha256")) != raw_digest:
            return f"historical selected response `{key}` is not bound to the archived raw receipt"
        if str(item.get("validator") or "").strip() != reviewer or str(
            item.get("validated_at") or ""
        ).strip() != validated_at:
            return f"historical selected response `{key}` reviewer metadata does not match its attestation"
        marker = item.get(CURRENT.SELECTED_CURRENT_REVALIDATION_ITEM_FIELD)
        if not isinstance(marker, Mapping):
            return f"historical selected response `{key}` lacks per-item attestation metadata"
        if marker.get("schema") != CURRENT.SELECTED_CURRENT_REVALIDATION_SCHEMA:
            return f"historical selected response `{key}` has an unsupported per-item schema"
        if _sha256(marker.get("attestation_sha256")) != selected_attestation_sha256:
            return f"historical selected response `{key}` is bound to different attestation bytes"
        if _sha256(marker.get("current_group_semantic_descriptor_sha256")) != selected_ledger[key]:
            return f"historical selected response `{key}` has a stale descriptor receipt"
        try:
            _check_item_pins(item, current_groups=current_groups, key=key, label="historical selected response")
        except SourceRecordHistoricalCompositionAttestationError as exc:
            return str(exc)
    if _sha256(selected_metadata.get("response_semantic_ledger_sha256")) != _canonical_digest(
        CURRENT._selected_semantic_judgment_ledger(selected_items)
    ):
        return "historical selected metadata response semantic-ledger digest is stale"
    return ""


def _expected_overlay_items(
    loaded_overlay: Mapping[str, Mapping[str, Any]],
    *,
    raw_audit: Mapping[str, Any],
    current_groups: Mapping[str, list[tuple[str, Mapping[str, Any]]]],
    overlay_ledger: Mapping[str, str],
    overlay_sha256: str,
) -> dict[str, dict[str, Any]]:
    """Replay the materializer's overlay transformation from checked evidence."""

    if set(loaded_overlay) != set(overlay_ledger):
        raise SourceRecordHistoricalCompositionAttestationError(
            "authenticated overlay does not cover exactly its descriptor ledger"
        )
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    out: dict[str, dict[str, Any]] = {}
    for key, raw_value in loaded_overlay.items():
        if not isinstance(raw_value, Mapping):
            raise SourceRecordHistoricalCompositionAttestationError(
                f"authenticated overlay response `{key}` is not an object"
            )
        value = copy.deepcopy(dict(raw_value))
        prior_digest = _sha256(value.get("source_record_audit_sha256"))
        historical_receipt = CURRENT._historical_item_receipt(value)
        if historical_receipt:
            existing = value.get(CURRENT.PRIOR_ITEM_RECEIPT_FIELD)
            if isinstance(existing, Mapping):
                value[CURRENT.PRIOR_ITEM_RECEIPT_FIELD] = {
                    "prior": copy.deepcopy(dict(existing)),
                    "differential": historical_receipt,
                }
            else:
                value[CURRENT.PRIOR_ITEM_RECEIPT_FIELD] = historical_receipt
        value["source_record_audit_sha256"] = raw_digest
        pins = CURRENT._current_item_pins(current_groups[key])
        if pins:
            value["source_record_item_digest_schema"] = CURRENT.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
            value["source_record_item_sha256s"] = pins
            value["source_record_item_sha256"] = pins[0]["source_record_item_sha256"]
        value[CURRENT.AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD] = {
            "schema": CURRENT.AUTHENTICATED_EVIDENCE_COMPOSITION_SCHEMA,
            "prior_source_record_audit_sha256": prior_digest,
            "current_source_record_audit_sha256": raw_digest,
            "current_group_semantic_descriptor_sha256": overlay_ledger[key],
            "differential_overlay_sha256": overlay_sha256,
        }
        out[key] = value
    return out


def _composition_parent_error(
    attestation: Mapping[str, Any],
    *,
    paper: str,
    raw_audit: Mapping[str, Any],
    composed_sidecar_path: Path,
    composed_sidecar_sha256: str,
    paper_dir: Path,
) -> Mapping[str, Any]:
    if attestation.get("schema") != SCHEMA:
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent has an unsupported schema"
        )
    if attestation.get("artifact_kind") != ARTIFACT_KIND:
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent has the wrong artifact kind"
        )
    if attestation.get("policy_version") != POLICY_VERSION:
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent has the wrong policy version"
        )
    if attestation.get("paper") != paper:
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent belongs to another paper"
        )
    if _non_evidence(attestation):
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent is marked non-evidence"
        )
    if not formalization_protocol_receipt_matches(attestation, scope="review"):
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent lacks a current review-protocol receipt"
        )
    if str(attestation.get("review_scope") or "").strip() != REVIEW_SCOPE or str(
        attestation.get("scope") or ""
    ).strip() != SEMANTIC_SCOPE:
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent has incomplete full-review scope"
        )
    if attestation.get("reviewed_current_semantics") is not True:
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent does not affirm full semantic review"
        )
    if not str(attestation.get("reviewer") or "").strip() or not str(
        attestation.get("validated_at") or ""
    ).strip() or not str(attestation.get("review_notes") or "").strip():
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent lacks reviewer, timestamp, or review notes"
        )
    if _sha256(attestation.get("current_source_record_audit_sha256")) != _sha256(
        raw_audit.get("source_record_audit_sha256")
    ):
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent is not bound to the archived raw receipt"
        )
    if _sha256(attestation.get("generated_judgment_keys_sha256")) != CURRENT.generated_judgment_keys_sha256(raw_audit):
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent has stale generated-key coverage"
        )
    if _sha256(attestation.get("generated_judgment_surface_sha256")) != CURRENT.generated_judgment_surface_sha256(raw_audit):
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent has stale generated-surface coverage"
        )
    if str(attestation.get("prior_judgment_sidecar_path") or "").strip() != _relative_paper_path(
        composed_sidecar_path, paper_dir
    ) or _sha256(attestation.get("prior_judgment_sidecar_sha256")) != composed_sidecar_sha256:
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent is not bound to the composed sidecar bytes"
        )
    if _sha256(attestation.get(INTEGRITY_FIELD)) != historical_composition_attestation_sha256(attestation):
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent integrity receipt does not match"
        )
    composition = attestation.get(COMPOSITION_FIELD)
    if not isinstance(composition, Mapping):
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent lacks composition provenance"
        )
    if composition.get("schema") != COMPOSITION_SCHEMA or composition.get("policy_version") != COMPOSITION_POLICY_VERSION:
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent has unsupported composition provenance"
        )
    if composition.get("archived_raw_replay_mode") != ARCHIVED_RAW_REPLAY_MODE:
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent does not explicitly authorize receipt-replayed archive bytes"
        )
    if composition.get("selected_sidecar_replay_mode") != SELECTED_SIDECAR_REPLAY_MODE:
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition parent does not explicitly authorize projected selected evidence"
        )
    return composition


def historical_composition_attestation_sha256(payload: Mapping[str, Any]) -> str:
    """Return the self-receipt for a special historical composition parent."""

    stripped = {str(key): value for key, value in payload.items() if str(key) != INTEGRITY_FIELD}
    return _canonical_digest(stripped)


def stamp_historical_composition_attestation(payload: dict[str, Any]) -> None:
    """Stamp a completed human parent attestation after all provenance is present."""

    payload[INTEGRITY_FIELD] = historical_composition_attestation_sha256(payload)


def validate_historical_composition_attestation(
    *,
    paper: str,
    paper_dir: Path,
    archived_raw_audit: Mapping[str, Any],
    archived_raw_audit_path: Path,
    composed_sidecar: Mapping[str, Any],
    composed_sidecar_path: Path,
    parent_attestation: Mapping[str, Any],
    parent_attestation_path: Path,
) -> ValidatedHistoricalCompositionAttestation:
    """Replay a complete historical composition and validate its new parent.

    The function checks caller objects against the supplied immutable files,
    then returns an in-memory normal-form full-attestation projection.  It
    performs no source scan and no Lean invocation.
    """

    paper_dir = paper_dir.resolve()
    archived_raw_audit_path = _resolve_paper_relative_path(
        _relative_paper_path(archived_raw_audit_path, paper_dir), paper_dir, label="archived raw audit path"
    )
    composed_sidecar_path = _resolve_paper_relative_path(
        _relative_paper_path(composed_sidecar_path, paper_dir), paper_dir, label="composed sidecar path"
    )
    parent_attestation_path = _resolve_paper_relative_path(
        _relative_paper_path(parent_attestation_path, paper_dir), paper_dir, label="parent attestation path"
    )
    raw, raw_file_sha256 = _snapshot_matches(
        archived_raw_audit_path, archived_raw_audit, label="archived raw audit"
    )
    sidecar, sidecar_sha256 = _snapshot_matches(
        composed_sidecar_path, composed_sidecar, label="composed sidecar"
    )
    parent, _parent_sha256 = _snapshot_matches(
        parent_attestation_path, parent_attestation, label="historical composition parent"
    )
    if error := CURRENT._raw_audit_error(raw, paper=paper):
        raise SourceRecordHistoricalCompositionAttestationError(error)
    if sidecar.get("schema") != 1 or sidecar.get("paper") not in {None, paper}:
        raise SourceRecordHistoricalCompositionAttestationError(
            "composed sidecar has an invalid schema or paper identity"
        )
    if _non_evidence(sidecar):
        raise SourceRecordHistoricalCompositionAttestationError(
            "composed sidecar is marked non-evidence"
        )
    if str(sidecar.get("prompt_version") or "").strip() != CURRENT.SOURCE_RECORD_V10_PROMPT_VERSION:
        raise SourceRecordHistoricalCompositionAttestationError(
            "composed sidecar does not use the v10 prompt"
        )

    parent_composition = _composition_parent_error(
        parent,
        paper=paper,
        raw_audit=raw,
        composed_sidecar_path=composed_sidecar_path,
        composed_sidecar_sha256=sidecar_sha256,
        paper_dir=paper_dir,
    )
    _require_snapshot_record(
        parent_composition.get("archived_raw_audit"),
        path=archived_raw_audit_path,
        digest=raw_file_sha256,
        paper_dir=paper_dir,
        label="archived raw audit",
        payload=raw,
    )
    _require_snapshot_record(
        parent_composition.get("composed_sidecar"),
        path=composed_sidecar_path,
        digest=sidecar_sha256,
        paper_dir=paper_dir,
        label="composed sidecar",
    )
    archived_statement_map = _archived_statement_map_snapshot(
        parent_composition,
        raw_audit=raw,
        paper=paper,
        paper_dir=paper_dir,
    )

    raw_ledger, _raw_groups = _raw_descriptor_ledger(raw, label="archived")
    try:
        current_groups = CURRENT.generated_judgment_items(raw)
        sidecar_items = CURRENT._sidecar_items(sidecar, paper=paper)
        selected_metadata = sidecar.get(CURRENT.SELECTED_CURRENT_REVALIDATION_FIELD)
        composition_metadata = sidecar.get(CURRENT.AUTHENTICATED_EVIDENCE_COMPOSITION_FIELD)
        if not isinstance(selected_metadata, Mapping) or not isinstance(composition_metadata, Mapping):
            raise SourceRecordHistoricalCompositionAttestationError(
                "composed sidecar lacks selected-rebind or composition provenance"
            )
        selected_ledger = _descriptor_ledger(
            composition_metadata.get("selected_current_group_descriptors"),
            label="composed selected descriptor ledger",
        )
        overlay_ledger = _descriptor_ledger(
            composition_metadata.get("differential_overlay_current_group_descriptors"),
            label="composed overlay descriptor ledger",
        )
    except CURRENT.SourceRecordCurrentRevalidationError as exc:
        raise SourceRecordHistoricalCompositionAttestationError(str(exc)) from exc

    if set(current_groups) != set(raw_ledger):
        raise SourceRecordHistoricalCompositionAttestationError(
            "archived generated item ledger differs from its semantic descriptor ledger"
        )
    if set(selected_ledger) & set(overlay_ledger):
        raise SourceRecordHistoricalCompositionAttestationError(
            "selected and overlay descriptor ledgers overlap in a response slot"
        )
    if set(selected_ledger) | set(overlay_ledger) != set(raw_ledger):
        raise SourceRecordHistoricalCompositionAttestationError(
            "selected and overlay descriptor ledgers do not cover every archived group"
        )
    if set(sidecar_items) != set(raw_ledger):
        raise SourceRecordHistoricalCompositionAttestationError(
            "composed sidecar does not cover every archived generated group"
        )
    for key, descriptor in {**selected_ledger, **overlay_ledger}.items():
        if raw_ledger.get(key) != descriptor:
            raise SourceRecordHistoricalCompositionAttestationError(
                f"composed response slot `{key}` is not pinned to its archived raw descriptor"
            )

    raw_digest = _sha256(raw.get("source_record_audit_sha256"))
    if _sha256(sidecar.get("source_record_audit_sha256")) != raw_digest:
        raise SourceRecordHistoricalCompositionAttestationError(
            "composed sidecar is not bound to the archived raw receipt"
        )
    if composition_metadata.get("schema") != CURRENT.AUTHENTICATED_EVIDENCE_COMPOSITION_SCHEMA or composition_metadata.get("policy_version") != CURRENT.AUTHENTICATED_EVIDENCE_COMPOSITION_POLICY_VERSION:
        raise SourceRecordHistoricalCompositionAttestationError(
            "composed sidecar has unsupported selected-overlay composition provenance"
        )
    if _sha256(composition_metadata.get("historical_raw_audit_sha256")) != raw_digest:
        raise SourceRecordHistoricalCompositionAttestationError(
            "composition provenance is not bound to the archived raw receipt"
        )
    if not _sha256(composition_metadata.get("historical_raw_audit_file_sha256")):
        raise SourceRecordHistoricalCompositionAttestationError(
            "composition provenance has no historical raw byte receipt"
        )
    if not _sha256(composition_metadata.get("selected_current_sidecar_sha256")):
        raise SourceRecordHistoricalCompositionAttestationError(
            "composition provenance has no selected-sidecar byte receipt"
        )
    if _sha256(composition_metadata.get("generated_judgment_keys_sha256")) != CURRENT.generated_judgment_keys_sha256(raw):
        raise SourceRecordHistoricalCompositionAttestationError(
            "composition provenance has stale generated-key coverage"
        )
    if _sha256(composition_metadata.get("generated_judgment_surface_sha256")) != CURRENT.generated_judgment_surface_sha256(raw):
        raise SourceRecordHistoricalCompositionAttestationError(
            "composition provenance has stale generated-surface coverage"
        )

    selected_attestation_path = _resolve_paper_relative_path(
        selected_metadata.get("attestation_path"), paper_dir, label="selected attestation path"
    )
    selected_attestation, selected_attestation_sha256 = _read_json_object_with_sha256(
        selected_attestation_path, label="selected attestation"
    )
    if _sha256(selected_metadata.get("attestation_sha256")) != selected_attestation_sha256:
        raise SourceRecordHistoricalCompositionAttestationError(
            "composed sidecar selected-attestation bytes do not match"
        )
    base_path = _resolve_paper_relative_path(
        selected_metadata.get("prior_judgment_sidecar_path"), paper_dir, label="base sidecar path"
    )
    base_sidecar, base_sha256 = _read_json_object_with_sha256(base_path, label="base sidecar")
    if _non_evidence(base_sidecar):
        raise SourceRecordHistoricalCompositionAttestationError(
            "base sidecar is marked non-evidence"
        )
    if _sha256(selected_metadata.get("prior_judgment_sidecar_sha256")) != base_sha256:
        raise SourceRecordHistoricalCompositionAttestationError(
            "composed sidecar base-sidecar bytes do not match"
        )
    overlay_logical_path = _resolve_paper_relative_path(
        selected_metadata.get("differential_overlay_path"), paper_dir, label="overlay path"
    )
    overlay_path = _resolve_paper_relative_path(
        parent_composition.get("differential_overlay", {}).get("path")
        if isinstance(parent_composition.get("differential_overlay"), Mapping)
        else None,
        paper_dir,
        label="parent overlay path",
    )
    _overlay_payload, overlay_sha256 = _read_json_object_with_sha256(overlay_path, label="overlay")
    if _sha256(selected_metadata.get("differential_overlay_sha256")) != overlay_sha256:
        raise SourceRecordHistoricalCompositionAttestationError(
            "composed sidecar overlay bytes do not match selected provenance"
        )
    if str(composition_metadata.get("differential_overlay_path") or "").strip() != _relative_paper_path(overlay_logical_path, paper_dir):
        raise SourceRecordHistoricalCompositionAttestationError(
            "composition provenance names a different logical overlay"
        )
    if _sha256(composition_metadata.get("differential_overlay_sha256")) != overlay_sha256:
        raise SourceRecordHistoricalCompositionAttestationError(
            "composition provenance overlay bytes do not match"
        )

    _require_snapshot_record(
        parent_composition.get("selected_attestation"),
        path=selected_attestation_path,
        digest=selected_attestation_sha256,
        paper_dir=paper_dir,
        label="selected attestation",
    )
    _require_snapshot_record(
        parent_composition.get("base_sidecar"),
        path=base_path,
        digest=base_sha256,
        paper_dir=paper_dir,
        label="base sidecar",
    )
    _require_snapshot_record(
        parent_composition.get("differential_overlay"),
        path=overlay_path,
        digest=overlay_sha256,
        paper_dir=paper_dir,
        label="differential overlay",
    )
    if _sha256(parent_composition.get("reported_historical_raw_audit_file_sha256")) != _sha256(
        composition_metadata.get("historical_raw_audit_file_sha256")
    ):
        raise SourceRecordHistoricalCompositionAttestationError(
            "parent composition does not preserve the historical raw byte receipt"
        )
    if _sha256(parent_composition.get("reported_selected_current_sidecar_sha256")) != _sha256(
        composition_metadata.get("selected_current_sidecar_sha256")
    ):
        raise SourceRecordHistoricalCompositionAttestationError(
            "parent composition does not preserve the selected-sidecar byte receipt"
        )

    if error := _selected_attestation_error(
        selected_attestation,
        paper=paper,
        raw_audit=raw,
        base_path=base_path,
        base_sha256=base_sha256,
        overlay_logical_path=overlay_logical_path,
        overlay_sha256=overlay_sha256,
        selected_ledger=selected_ledger,
        overlay_ledger=overlay_ledger,
        selected_metadata=selected_metadata,
        paper_dir=paper_dir,
    ):
        raise SourceRecordHistoricalCompositionAttestationError(error)

    selected_items = {key: sidecar_items[key] for key in selected_ledger}
    if error := _selected_projection_error(
        selected_items,
        selected_attestation=selected_attestation,
        selected_attestation_sha256=selected_attestation_sha256,
        selected_metadata=selected_metadata,
        base_sidecar=base_sidecar,
        raw_audit=raw,
        selected_ledger=selected_ledger,
        current_groups=current_groups,
        paper_dir=paper_dir,
        archived_statement_map=archived_statement_map,
    ):
        raise SourceRecordHistoricalCompositionAttestationError(error)

    # The archived overlay is authenticated against the logical raw-audit path
    # recorded when it was issued, not against its own overlay path.  The
    # immutable archived copy above supplies the bytes; this coordinate only
    # restores the historical provenance string checked by the differential
    # loader.
    historical_raw_logical_path = _resolve_paper_relative_path(
        composition_metadata.get("historical_raw_audit_path"),
        paper_dir,
        label="composition historical raw-audit path",
    )
    loaded_overlay = DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
        paper_dir,
        paper,
        raw,
        path=overlay_path,
        current_raw_audit_path=archived_raw_audit_path,
        current_raw_audit_provenance_path=historical_raw_logical_path,
    )
    expected_overlay = _expected_overlay_items(
        loaded_overlay,
        raw_audit=raw,
        current_groups=current_groups,
        overlay_ledger=overlay_ledger,
        overlay_sha256=overlay_sha256,
    )
    for key, expected in expected_overlay.items():
        actual = sidecar_items.get(key)
        if not isinstance(actual, Mapping) or _canonical_digest(actual) != _canonical_digest(expected):
            raise SourceRecordHistoricalCompositionAttestationError(
                f"composed overlay response `{key}` no longer replays from authenticated overlay evidence"
            )
        marker = actual.get(CURRENT.AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD)
        if not isinstance(marker, Mapping) or _sha256(
            marker.get("current_group_semantic_descriptor_sha256")
        ) != overlay_ledger[key]:
            raise SourceRecordHistoricalCompositionAttestationError(
                f"composed overlay response `{key}` has a stale descriptor marker"
            )
        _check_item_pins(actual, current_groups=current_groups, key=key, label="composed overlay response")

    selected_multiset = _descriptor_multiset(selected_ledger)
    overlay_multiset = _descriptor_multiset(overlay_ledger)
    complete_multiset = _descriptor_multiset(raw_ledger)
    if tuple(sorted(selected_multiset + overlay_multiset)) != complete_multiset:
        raise SourceRecordHistoricalCompositionAttestationError(
            "selected and overlay descriptor occurrences do not form the archived complete descriptor multiset"
        )
    receipt_values = {
        "selected_descriptor_count": len(selected_multiset),
        "overlay_descriptor_count": len(overlay_multiset),
        "complete_descriptor_count": len(complete_multiset),
        "selected_descriptor_multiset_sha256": _canonical_digest(list(selected_multiset)),
        "overlay_descriptor_multiset_sha256": _canonical_digest(list(overlay_multiset)),
        "complete_descriptor_multiset_sha256": _canonical_digest(list(complete_multiset)),
        "full_response_semantic_ledger_sha256": _canonical_digest(
            CURRENT._semantic_judgment_ledger(sidecar_items)
        ),
    }
    for field, expected in receipt_values.items():
        supplied = parent_composition.get(field)
        if isinstance(expected, int):
            valid = supplied == expected
        else:
            valid = _sha256(supplied) == expected
        if not valid:
            raise SourceRecordHistoricalCompositionAttestationError(
                f"parent composition has a stale `{field}` receipt"
            )
    if _sha256(composition_metadata.get("response_semantic_ledger_sha256")) != receipt_values[
        "full_response_semantic_ledger_sha256"
    ]:
        raise SourceRecordHistoricalCompositionAttestationError(
            "composition provenance response semantic-ledger digest is stale"
        )

    disposition_errors = CURRENT._target_disposition_errors(
        raw,
        sidecar,
        paper_dir=paper_dir,
        historical_receipt_only=True,
        historical_statement_map=archived_statement_map,
    ) + CURRENT._boundary_classification_errors(raw, sidecar)
    if disposition_errors:
        raise SourceRecordHistoricalCompositionAttestationError(
            "historical composition target/classification replay failed: "
            + "; ".join(disposition_errors[:5])
        )

    normalized = {
        "schema": 1,
        "artifact_kind": "source_record_current_semantic_revalidation_attestation",
        "policy_version": "historical-composition-parent-projection-v1",
        "paper": paper,
        FORMALIZATION_REVIEW_PROTOCOL_FIELD: str(
            parent.get(FORMALIZATION_REVIEW_PROTOCOL_FIELD) or ""
        ).strip(),
        "review_scope": REVIEW_SCOPE,
        "scope": SEMANTIC_SCOPE,
        "reviewed_current_semantics": True,
        "reviewer": str(parent.get("reviewer") or "").strip(),
        "validated_at": str(parent.get("validated_at") or "").strip(),
        "review_notes": str(parent.get("review_notes") or "").strip(),
        "current_source_record_audit_sha256": raw_digest,
        "generated_judgment_keys_sha256": CURRENT.generated_judgment_keys_sha256(raw),
        "generated_judgment_surface_sha256": CURRENT.generated_judgment_surface_sha256(raw),
        "prior_judgment_sidecar_path": _relative_paper_path(composed_sidecar_path, paper_dir),
        "prior_judgment_sidecar_sha256": sidecar_sha256,
        "validated_historical_composition_parent_path": _relative_paper_path(
            parent_attestation_path, paper_dir
        ),
        "validated_historical_composition_parent_sha256": _parent_sha256,
    }
    return ValidatedHistoricalCompositionAttestation(
        normalized_full_attestation=normalized,
        archived_raw_audit=copy.deepcopy(raw),
        composed_sidecar=copy.deepcopy(sidecar),
        selected_descriptor_multiset=selected_multiset,
        overlay_descriptor_multiset=overlay_multiset,
        complete_descriptor_multiset=complete_multiset,
    )
