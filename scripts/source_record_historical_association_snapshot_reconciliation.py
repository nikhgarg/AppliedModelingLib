#!/usr/bin/env python3
"""Reconcile an archived raw audit to an immutable statement-map witness.

This is a deliberately narrow historical facility.  A source-record raw audit
records the byte SHA-256 of the statement map it was generated against.  In a
small number of old archives that top-level receipt was recorded incorrectly,
even though every generated source association still contains a full digest of
the individual source-map item it used.  This module can attest that fact only
when an immutable witness map contains one *and only one* item for every one
of those full item digests.

It does not amend, reissue, or otherwise make the archived aggregate raw
receipt current.  The serialized reconciliation is not authority on its own:
the loader rereads both immutable inputs, recomputes the exhaustive association
ledger, and returns a private loaded marker only after that replay succeeds.

Matching deliberately never uses a source-map key, Lean declaration, function
name, source location, or free-form similarity.  The sole cross-map selector is
the complete ``source_map_item_sha256`` pin present in the archived raw item.
Locations, source kinds, and semantic contracts are then checked as exact
contents of the selected witness item.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import sys
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in focused tests.
    from scripts.formalization_protocol import CURRENT_SOURCE_RECORD_PROMPT_VERSION
    from scripts.source_coverage_scope import (
        source_record_source_item_record_sha256,
        source_record_source_item_semantic_sha256,
    )
    from scripts.source_record_integrity import (
        canonical_digest_payload,
        source_record_audit_receipt_error,
    )
    from scripts.source_record_target_disposition import (
        source_contract_association_record_digest,
    )
except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
    from formalization_protocol import CURRENT_SOURCE_RECORD_PROMPT_VERSION
    from source_coverage_scope import (
        source_record_source_item_record_sha256,
        source_record_source_item_semantic_sha256,
    )
    from source_record_integrity import (
        canonical_digest_payload,
        source_record_audit_receipt_error,
    )
    from source_record_target_disposition import (
        source_contract_association_record_digest,
    )


SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_SCHEMA = 1
SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_POLICY_VERSION = (
    "source-record-v10-historical-association-snapshot-reconciliation-v1"
)
SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_ARTIFACT_KIND = (
    "source_record_v10_historical_association_snapshot_reconciliation"
)
SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_FILENAME = (
    "source_record_historical_association_snapshot_reconciliation.json"
)
SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_INTEGRITY_FIELD = (
    "source_record_historical_association_snapshot_reconciliation_sha256"
)

# These are generator-owned raw sections.  The reconciliation deliberately
# covers every source association in every one of them, irrespective of whether
# the item has a judgment key or a sidecar response.  Judgment-derived summary
# fields such as ``unresolved_conclusion_dependency_items`` are excluded: they
# are volatile views of these sections, not additional generated associations.
SOURCE_RECORD_REUSABLE_ITEM_SECTIONS = (
    "boundary_input_items",
    "theorem_facing_input_items",
    "conclusion_dependency_items",
    "type_valued_certificate_result_items",
    "recursive_field_items",
    "semantic_model_items",
    "source_premise_consistency_items",
)

# These are evidence inputs or the ordinary human-review sidecar.  A snapshot
# writer must not use one of their canonical locations as a destination even
# when a test fixture or a partially initialized paper does not yet contain
# the target file.  The root-level spellings preserve the legacy layout's
# protection while the audit-directory spellings are the current canonical
# locations.
_RESERVED_OUTPUT_PATHS = frozenset(
    {
        "audit/source_record_audit.json",
        "audit/paper_statement_map.json",
        "audit/source_record_match_llm.json",
        "source_record_audit.json",
        "paper_statement_map.json",
        "source_record_match_llm.json",
    }
)

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_LOADED_RECONCILIATION_SENTINEL = object()


class SourceRecordHistoricalAssociationSnapshotReconciliationError(ValueError):
    """Raised when a historical association snapshot is not admissible."""


class _LoadedHistoricalAssociationSnapshotReconciliation(dict[str, Any]):
    """A replayed reconciliation, distinguished from a parsed JSON mapping."""

    __slots__ = ("_source_record_historical_association_snapshot_loader_token",)

    def __init__(self, value: Mapping[str, Any]) -> None:
        super().__init__(value)
        self._source_record_historical_association_snapshot_loader_token = (
            _LOADED_RECONCILIATION_SENTINEL
        )


def is_loaded_historical_association_snapshot_reconciliation(value: object) -> bool:
    """Return true only for an object returned by this module's replay loader.

    A JSON field claiming that an artifact was loaded is intentionally
    irrelevant.  Callers that need this exceptional evidence lane must use the
    replay loader and this private in-memory token, never a serialized marker.
    """

    return bool(
        isinstance(value, _LoadedHistoricalAssociationSnapshotReconciliation)
        and getattr(
            value,
            "_source_record_historical_association_snapshot_loader_token",
            None,
        )
        is _LOADED_RECONCILIATION_SENTINEL
    )


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _canonical_digest(value: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(value), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _read_json_object(path: Path, *, label: str) -> tuple[dict[str, Any], bytes]:
    def no_duplicate_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON object key `{key}`")
            result[key] = value
        return result

    try:
        contents = path.read_bytes()
        value = json.loads(contents, object_pairs_hook=no_duplicate_object)
    except (OSError, ValueError) as exc:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"could not read {label} at {path}: {exc}"
        ) from exc
    if not isinstance(value, dict):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{label} at {path} is not a JSON object"
        )
    return value, contents


def _payload_is_non_evidence(payload: Mapping[str, Any]) -> bool:
    """Recognize only explicit non-evidence markers, never a filename hint."""

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
    artifact_kind = str(payload.get("artifact_kind") or "").strip().lower()
    validator_type = str(payload.get("validator_type") or "").strip().lower()
    return (
        "candidate" in artifact_kind
        or "proposal" in artifact_kind
        or "candidate" in validator_type
        or "proposal" in validator_type
    )


def _relative_paper_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{path} must remain inside {paper_dir}"
        ) from exc


def _resolve_paper_path(value: object, paper_dir: Path, *, label: str) -> Path:
    text = str(value or "").strip()
    pure = PurePosixPath(text)
    if (
        not text
        or pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{label} must be a normalized paper-relative path"
        )
    candidate = (paper_dir / Path(*pure.parts)).resolve()
    if _relative_paper_path(candidate, paper_dir) != text:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{label} is not canonical"
        )
    return candidate


def _atomic_write(path: Path, contents: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent, prefix=f".{path.name}.", delete=False
    ) as handle:
        handle.write(contents)
        temporary = Path(handle.name)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def _reserved_output_error(output_path: Path, paper_dir: Path) -> str:
    relative = _relative_paper_path(output_path, paper_dir)
    if relative in _RESERVED_OUTPUT_PATHS:
        return (
            f"refusing to use reserved evidence path `{relative}` as a "
            "historical reconciliation output"
        )
    return ""


def _raw_audit_error(raw: object, *, paper: str) -> str:
    """Validate archived evidence without treating its map receipt as current."""

    if not isinstance(raw, Mapping):
        return "archived raw audit is not an object"
    if _payload_is_non_evidence(raw):
        return "archived raw audit is explicitly marked non-evidence"
    if raw.get("paper") != paper:
        return "archived raw audit records a different paper"
    if (
        raw.get("prompt_version") != CURRENT_SOURCE_RECORD_PROMPT_VERSION
        or raw.get("source_record_policy_version")
        != CURRENT_SOURCE_RECORD_PROMPT_VERSION
    ):
        return "archived raw audit does not use the supported v10 source-record policy"
    if not _sha256(raw.get("paper_statement_map_sha256")):
        return "archived raw audit lacks a valid paper_statement_map_sha256"
    if error := source_record_audit_receipt_error(raw):
        return f"archived raw audit receipt is invalid: {error}"
    lean_check = raw.get("lean_check")
    if not isinstance(lean_check, Mapping) or lean_check.get("returncode") != 0:
        return "archived raw audit lacks a successful Lean check"
    try:
        recursion_failure_count = int(raw.get("recursion_failure_count") or 0)
    except (TypeError, ValueError):
        return "archived raw audit has a malformed recursion failure count"
    if recursion_failure_count != 0:
        return "archived raw audit has recursion failures"
    return ""


def _witness_map_items(witness: object) -> Mapping[str, Any]:
    if not isinstance(witness, Mapping):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "witness paper statement map is not an object"
        )
    if _payload_is_non_evidence(witness):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "witness paper statement map is explicitly marked non-evidence"
        )
    items = witness.get("items")
    if not isinstance(items, Mapping):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "witness paper statement map has no items object"
        )
    for key, item in items.items():
        if not isinstance(key, str) or not key.strip() or not isinstance(item, Mapping):
            raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
                "witness paper statement map has a malformed item"
            )
    return items


def _association_walk(
    value: object,
    *,
    path: tuple[str, ...],
) -> Iterable[tuple[tuple[str, ...], Mapping[str, Any]]]:
    """Yield every association-like mapping in one generator-owned raw item.

    Looking for both fields catches an incomplete map-pin object rather than
    silently skipping it.  The traversal is structural and makes no use of a
    judgment key, Lean name, or association field name.
    """

    if isinstance(value, Mapping):
        if (
            "source_item_identities" in value
            or "source_map_item_sha256_by_key" in value
        ):
            yield path, value
        for key, child in value.items():
            yield from _association_walk(child, path=path + (str(key),))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from _association_walk(child, path=path + (str(index),))


def _source_associations(raw: Mapping[str, Any]) -> list[tuple[tuple[str, ...], Mapping[str, Any]]]:
    """Collect all source associations in the complete reusable raw surface."""

    associations: list[tuple[tuple[str, ...], Mapping[str, Any]]] = []
    for section in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        section_items = raw.get(section)
        if section_items is None:
            continue
        if not isinstance(section_items, list):
            raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
                f"archived raw audit section `{section}` is not a list"
            )
        for index, item in enumerate(section_items):
            if not isinstance(item, Mapping):
                raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
                    f"archived raw audit section `{section}` has a non-object item"
                )
            associations.extend(
                _association_walk(item, path=(section, str(index)))
            )
    return sorted(associations, key=lambda entry: entry[0])


def _complete_map_pin(value: object, *, label: str) -> str:
    digest = _sha256(value)
    if not digest:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{label} has no complete source-map item SHA-256 pin"
        )
    return digest


def _identity_from_raw(
    identity: object,
    *,
    label: str,
) -> tuple[str, str, str, Mapping[str, Any], str, str | None]:
    """Return the complete archived source identity without dereferencing it."""

    if not isinstance(identity, Mapping):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{label} is not an object"
        )
    source_key = str(identity.get("source_key") or "").strip()
    source_location = str(identity.get("source_location") or "").strip()
    source_kind = str(identity.get("source_kind") or "").strip()
    contract = identity.get("semantic_contract")
    if (
        not source_key
        or not source_location
        or not source_kind
        or not isinstance(contract, Mapping)
        or not contract
    ):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{label} has an incomplete source identity"
        )
    map_item_digest = _complete_map_pin(
        identity.get("source_map_item_sha256"), label=label
    )
    raw_semantic = identity.get("source_semantic_sha256")
    if raw_semantic is None:
        semantic_digest: str | None = None
    else:
        semantic_digest = _sha256(raw_semantic)
        if not semantic_digest:
            raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
                f"{label} has a malformed source semantic SHA-256 pin"
            )
    return (
        source_key,
        source_location,
        source_kind,
        contract,
        map_item_digest,
        semantic_digest,
    )


def _association_identity_pins(
    association: Mapping[str, Any], *, label: str
) -> list[tuple[str, str, str, Mapping[str, Any], str, str | None]]:
    """Validate complete per-identity pins and optional by-key redundancies."""

    identities = association.get("source_item_identities")
    if not isinstance(identities, list) or not identities:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{label} has no complete source_item_identities ledger"
        )
    parsed = [
        _identity_from_raw(identity, label=f"{label}.source_item_identities[{index}]")
        for index, identity in enumerate(identities)
    ]
    keys = [value[0] for value in parsed]
    if len(set(keys)) != len(keys):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{label} has duplicate source keys in one association"
        )
    map_digests = [value[4] for value in parsed]
    if len(set(map_digests)) != len(map_digests):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{label} has duplicate source-map item digests in one association"
        )
    if "association_sha256" in association and _sha256(
        association.get("association_sha256")
    ) != source_contract_association_record_digest(association):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{label} has a stale association digest"
        )

    by_key = association.get("source_map_item_sha256_by_key")
    keys_field = association.get("source_map_item_keys")
    if by_key is None:
        if keys_field is not None:
            raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
                f"{label} has source-map keys without their complete digest map"
            )
        return parsed
    if not isinstance(by_key, Mapping) or not by_key:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{label} has a malformed source_map_item_sha256_by_key ledger"
        )
    normalized_by_key: dict[str, str] = {}
    for raw_key, raw_digest in by_key.items():
        key = str(raw_key or "").strip()
        if not key or key in normalized_by_key:
            raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
                f"{label} has a malformed source-map key ledger"
            )
        normalized_by_key[key] = _complete_map_pin(
            raw_digest, label=f"{label}.source_map_item_sha256_by_key[{key!r}]"
        )
    expected_by_key = {value[0]: value[4] for value in parsed}
    if normalized_by_key != expected_by_key:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{label} source-map digest ledger does not exactly match its identities"
        )
    if keys_field is not None:
        normalized_keys = (
            [str(key or "").strip() for key in keys_field]
            if isinstance(keys_field, list)
            else []
        )
        if (
            not isinstance(keys_field, list)
            or not normalized_keys
            or any(not key for key in normalized_keys)
            or len(normalized_keys) != len(set(normalized_keys))
            or set(normalized_keys) != set(expected_by_key)
        ):
            raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
                f"{label} source-map key list does not exactly match its identities"
            )
    return parsed


def _witness_items_by_full_digest(
    items: Mapping[str, Any],
) -> dict[str, list[Mapping[str, Any]]]:
    """Index witness items only by their complete record digest.

    The map key remains outside the result on purpose.  It can never select a
    witness item or break a tie between two otherwise identical full records.
    """

    index: dict[str, list[Mapping[str, Any]]] = {}
    for item in items.values():
        assert isinstance(item, Mapping)  # Checked by `_witness_map_items`.
        # Raw source-record associations pin the source-record projection of a
        # map item.  The generic map-record digest also includes refreshable
        # Lean closure receipts, so it cannot resolve a raw association after
        # a valid correspondence receipt refresh.
        digest = source_record_source_item_record_sha256(item)
        if not _sha256(digest):
            raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
                "witness paper statement map has an undigestible item"
            )
        index.setdefault(digest, []).append(item)
    return index


def _same(left: object, right: object) -> bool:
    return canonical_digest_payload(left) == canonical_digest_payload(right)


def _source_identity_ledger_row(
    *,
    association_path: tuple[str, ...],
    association: Mapping[str, Any],
    identity_index: int,
    raw_identity: tuple[str, str, str, Mapping[str, Any], str, str | None],
    witness_index: Mapping[str, list[Mapping[str, Any]]],
) -> dict[str, Any]:
    """Resolve one complete raw pin and record a replayable ledger row."""

    (
        _source_key,
        source_location,
        source_kind,
        source_contract,
        map_item_digest,
        supplied_semantic_digest,
    ) = raw_identity
    matches = witness_index.get(map_item_digest, [])
    if len(matches) != 1:
        detail = "no" if not matches else "multiple"
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{'.'.join(association_path)} source-map item digest resolves to {detail} "
            "witness items"
        )
    witness = matches[0]
    witness_location = str(witness.get("source_location") or "").strip()
    witness_kind = str(witness.get("source_kind") or "").strip()
    witness_contract = witness.get("semantic_contract")
    if (
        not witness_location
        or not witness_kind
        or not isinstance(witness_contract, Mapping)
        or not witness_contract
    ):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "selected witness item has an incomplete source identity"
        )
    if source_location != witness_location:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{'.'.join(association_path)} source location differs from witness item"
        )
    if source_kind != witness_kind:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{'.'.join(association_path)} source kind differs from witness item"
        )
    if not _same(source_contract, witness_contract):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{'.'.join(association_path)} semantic contract differs from witness item"
        )
    witness_semantic_digest = source_record_source_item_semantic_sha256(
        dict(witness), ""
    )
    if not _sha256(witness_semantic_digest):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "selected witness item has no canonical source semantic digest"
        )
    if (
        supplied_semantic_digest is not None
        and supplied_semantic_digest != witness_semantic_digest
    ):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"{'.'.join(association_path)} source semantic digest differs from witness item"
        )
    if source_record_source_item_record_sha256(witness) != map_item_digest:
        # This should be impossible after index lookup, but retaining the
        # assertion makes this row self-contained under future index changes.
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "selected witness item no longer has the resolved full map-item digest"
        )
    return {
        "raw_association_path": "/".join(association_path),
        "raw_association_sha256": _canonical_digest(association),
        "raw_identity_index": identity_index,
        "raw_source_identity_sha256": _canonical_digest(
            {
                "source_location": source_location,
                "source_kind": source_kind,
                "semantic_contract": copy.deepcopy(source_contract),
                "source_map_item_sha256": map_item_digest,
                "source_semantic_sha256": supplied_semantic_digest,
            }
        ),
        "source_map_item_sha256": map_item_digest,
        "witness_item_identity": {
            "source_map_item_sha256": map_item_digest,
            "source_item_semantic_sha256": witness_semantic_digest,
            "source_location": witness_location,
            "source_kind": witness_kind,
            "semantic_contract_sha256": _canonical_digest(witness_contract),
        },
    }


def _reconciliation_ledger(raw: Mapping[str, Any], witness: Mapping[str, Any]) -> dict[str, Any]:
    items = _witness_map_items(witness)
    witness_index = _witness_items_by_full_digest(items)
    rows: list[dict[str, Any]] = []
    for association_path, association in _source_associations(raw):
        parsed_identities = _association_identity_pins(
            association, label=".".join(association_path)
        )
        for identity_index, raw_identity in enumerate(parsed_identities):
            rows.append(
                _source_identity_ledger_row(
                    association_path=association_path,
                    association=association,
                    identity_index=identity_index,
                    raw_identity=raw_identity,
                    witness_index=witness_index,
                )
            )
    rows.sort(
        key=lambda row: (
            str(row["raw_association_path"]),
            int(row["raw_identity_index"]),
        )
    )
    if not rows:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "archived raw audit has no source association identities in reusable sections"
        )
    return {
        "schema": 1,
        "covered_raw_sections": list(SOURCE_RECORD_REUSABLE_ITEM_SECTIONS),
        "identity_count": len(rows),
        "identity_ledger_sha256": _canonical_digest(rows),
        "identity_rows": rows,
    }


def _reconciliation_payload(
    *,
    paper_dir: Path,
    paper: str,
    raw_audit_path: Path,
    raw_audit: Mapping[str, Any],
    raw_audit_bytes: bytes,
    witness_map_path: Path,
    witness_map: Mapping[str, Any],
    witness_map_bytes: bytes,
) -> dict[str, Any]:
    if error := _raw_audit_error(raw_audit, paper=paper):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(error)
    if _payload_is_non_evidence(witness_map):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "witness paper statement map is explicitly marked non-evidence"
        )
    if witness_map.get("paper") != paper:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "witness paper statement map records a different paper"
        )
    _witness_map_items(witness_map)

    reported_map_sha = _sha256(raw_audit.get("paper_statement_map_sha256"))
    raw_bytes_sha = hashlib.sha256(raw_audit_bytes).hexdigest()
    if _file_sha256(raw_audit_path) != raw_bytes_sha:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "archived raw-audit byte receipt changed during reconciliation"
        )
    witness_bytes_sha = hashlib.sha256(witness_map_bytes).hexdigest()
    # The source-record generator's `paper_statement_map_sha256` is a full
    # map-byte SHA.  Keep a separately named actual receipt in the artifact so
    # consumers cannot mistake the archived reported value for the witness.
    actual_witness_map_sha = _file_sha256(witness_map_path)
    if witness_bytes_sha != actual_witness_map_sha:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "witness statement-map byte receipt changed during reconciliation"
        )
    if reported_map_sha == actual_witness_map_sha:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "historical association reconciliation is inapplicable when the archived "
            "paper_statement_map_sha256 already matches the witness map"
        )

    payload: dict[str, Any] = {
        "schema": SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_SCHEMA,
        "artifact_kind": SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_ARTIFACT_KIND,
        "policy_version": SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_POLICY_VERSION,
        "paper": paper,
        # This is a record of an exception, not a replacement provenance
        # field.  The original raw receipt is preserved verbatim below.
        "does_not_repair_archived_raw_aggregate_receipt": True,
        "archived_raw_audit": {
            "path": _relative_paper_path(raw_audit_path, paper_dir),
            "bytes_sha256": raw_bytes_sha,
            "source_record_audit_sha256": _sha256(
                raw_audit.get("source_record_audit_sha256")
            ),
            "source_record_audit_integrity_sha256": _sha256(
                raw_audit.get("source_record_audit_integrity_sha256")
            ),
            "reported_paper_statement_map_sha256": reported_map_sha,
        },
        "immutable_witness_statement_map": {
            "path": _relative_paper_path(witness_map_path, paper_dir),
            "bytes_sha256": witness_bytes_sha,
            "actual_paper_statement_map_sha256": actual_witness_map_sha,
        },
        "reported_map_mismatch": {
            "archived_reported_paper_statement_map_sha256": reported_map_sha,
            "actual_witness_paper_statement_map_sha256": actual_witness_map_sha,
        },
        "association_identity_ledger": _reconciliation_ledger(raw_audit, witness_map),
        "loader_replay_required": True,
    }
    payload[
        SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_INTEGRITY_FIELD
    ] = _canonical_digest(payload)
    return payload


def create_historical_association_snapshot_reconciliation(
    *,
    paper_dir: Path,
    paper: str,
    raw_audit_path: Path,
    witness_map_path: Path,
) -> dict[str, Any]:
    """Create one replayable reconciliation payload without writing it."""

    paper_dir = paper_dir.resolve()
    raw_audit_path = raw_audit_path.resolve()
    witness_map_path = witness_map_path.resolve()
    # Inputs must stay inside the paper so an eventual loader can replay them
    # from the repository rather than trusting an arbitrary host path.
    _relative_paper_path(raw_audit_path, paper_dir)
    _relative_paper_path(witness_map_path, paper_dir)
    raw_audit, raw_audit_bytes = _read_json_object(raw_audit_path, label="archived raw audit")
    witness_map, witness_map_bytes = _read_json_object(
        witness_map_path, label="immutable witness statement map"
    )
    return _reconciliation_payload(
        paper_dir=paper_dir,
        paper=paper,
        raw_audit_path=raw_audit_path,
        raw_audit=raw_audit,
        raw_audit_bytes=raw_audit_bytes,
        witness_map_path=witness_map_path,
        witness_map=witness_map,
        witness_map_bytes=witness_map_bytes,
    )


def write_historical_association_snapshot_reconciliation(
    *,
    paper_dir: Path,
    paper: str,
    raw_audit_path: Path,
    witness_map_path: Path,
    output_path: Path,
) -> dict[str, Any]:
    """Create an artifact once; existing evidence is never overwritten."""

    paper_dir = paper_dir.resolve()
    output_path = output_path.resolve()
    _relative_paper_path(output_path, paper_dir)
    if error := _reserved_output_error(output_path, paper_dir):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(error)
    if output_path.exists():
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"refusing to overwrite existing reconciliation artifact at {output_path}"
        )
    payload = create_historical_association_snapshot_reconciliation(
        paper_dir=paper_dir,
        paper=paper,
        raw_audit_path=raw_audit_path,
        witness_map_path=witness_map_path,
    )
    _atomic_write(
        output_path,
        (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8"),
    )
    return payload


def _artifact_integrity_error(payload: object) -> str:
    if not isinstance(payload, Mapping):
        return "reconciliation artifact is not an object"
    if _payload_is_non_evidence(payload):
        return "reconciliation artifact is explicitly marked non-evidence"
    if payload.get("schema") != (
        SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_SCHEMA
    ):
        return "reconciliation artifact has an unsupported schema"
    if payload.get("artifact_kind") != (
        SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_ARTIFACT_KIND
    ):
        return "reconciliation artifact has an unexpected kind"
    if payload.get("policy_version") != (
        SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_POLICY_VERSION
    ):
        return "reconciliation artifact has an unexpected policy version"
    if payload.get("does_not_repair_archived_raw_aggregate_receipt") is not True:
        return "reconciliation artifact does not preserve the raw-receipt boundary"
    if payload.get("loader_replay_required") is not True:
        return "reconciliation artifact does not require loader replay"
    supplied = _sha256(
        payload.get(
            SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_INTEGRITY_FIELD
        )
    )
    if not supplied:
        return "reconciliation artifact lacks its integrity receipt"
    unsigned = {
        str(key): value
        for key, value in payload.items()
        if str(key)
        != SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_INTEGRITY_FIELD
    }
    if supplied != _canonical_digest(unsigned):
        return "reconciliation artifact integrity receipt is stale"
    return ""


def load_historical_association_snapshot_reconciliation(
    *,
    paper_dir: Path,
    paper: str,
    artifact_path: Path | None = None,
) -> Mapping[str, Any]:
    """Replay a reconciliation and return the private loaded evidence token.

    The serialized ledger is compared with a fresh reconstruction from the raw
    bytes and witness bytes.  It is therefore safe for a future consumer to
    inspect this object only after this loader has returned it.
    """

    paper_dir = paper_dir.resolve()
    if artifact_path is None:
        artifact_path = (
            paper_dir
            / "audit"
            / SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_FILENAME
        )
    artifact_path = artifact_path.resolve()
    _relative_paper_path(artifact_path, paper_dir)
    artifact, _artifact_bytes = _read_json_object(
        artifact_path, label="historical association reconciliation artifact"
    )
    if error := _artifact_integrity_error(artifact):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(error)
    if artifact.get("paper") != paper:
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "reconciliation artifact records a different paper"
        )
    raw_meta = artifact.get("archived_raw_audit")
    witness_meta = artifact.get("immutable_witness_statement_map")
    if not isinstance(raw_meta, Mapping) or not isinstance(witness_meta, Mapping):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "reconciliation artifact has malformed immutable input provenance"
        )
    raw_path = _resolve_paper_path(
        raw_meta.get("path"), paper_dir, label="archived raw-audit path"
    )
    witness_path = _resolve_paper_path(
        witness_meta.get("path"), paper_dir, label="witness statement-map path"
    )
    # Check byte pins before parsing or reconstructing any semantic surface.
    if _file_sha256(raw_path) != _sha256(raw_meta.get("bytes_sha256")):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "archived raw-audit bytes differ from reconciliation provenance"
        )
    if _file_sha256(witness_path) != _sha256(witness_meta.get("bytes_sha256")):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "witness statement-map bytes differ from reconciliation provenance"
        )
    replayed = create_historical_association_snapshot_reconciliation(
        paper_dir=paper_dir,
        paper=paper,
        raw_audit_path=raw_path,
        witness_map_path=witness_path,
    )
    if canonical_digest_payload(replayed) != canonical_digest_payload(artifact):
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            "reconciliation artifact does not equal replayed immutable inputs"
        )
    return _LoadedHistoricalAssociationSnapshotReconciliation(replayed)


def _paper_dir_from_args(paper: str) -> Path:
    candidate = ROOT / "papers" / paper
    if not candidate.is_dir():
        raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
            f"paper directory does not exist: {candidate}"
        )
    return candidate


def _argument_paper_path(value: str, paper_dir: Path, *, label: str) -> Path:
    return _resolve_paper_path(value, paper_dir, label=label)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Create or replay a fail-closed historical source-association "
            "snapshot reconciliation."
        )
    )
    parser.add_argument("--paper", required=True)
    parser.add_argument(
        "--raw-audit",
        default="audit/source_record_audit.json",
        help="paper-relative archived raw-audit JSON path",
    )
    parser.add_argument(
        "--witness-statement-map",
        help="paper-relative immutable witness paper_statement_map JSON path",
    )
    parser.add_argument(
        "--out",
        default=(
            "audit/"
            + SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_FILENAME
        ),
        help="paper-relative reconciliation output path (must not exist)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="replay an existing --out artifact instead of creating one",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        paper_dir = _paper_dir_from_args(args.paper)
        output_path = _argument_paper_path(args.out, paper_dir, label="output path")
        if args.check:
            loaded = load_historical_association_snapshot_reconciliation(
                paper_dir=paper_dir,
                paper=args.paper,
                artifact_path=output_path,
            )
            if not is_loaded_historical_association_snapshot_reconciliation(loaded):
                raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
                    "reconciliation loader did not issue its private replay token"
                )
            print(json.dumps(loaded, indent=2, sort_keys=True))
            return 0
        if not str(args.witness_statement_map or "").strip():
            raise SourceRecordHistoricalAssociationSnapshotReconciliationError(
                "--witness-statement-map is required when creating a reconciliation"
            )
        raw_audit_path = _argument_paper_path(
            args.raw_audit, paper_dir, label="archived raw-audit path"
        )
        witness_map_path = _argument_paper_path(
            args.witness_statement_map,
            paper_dir,
            label="witness statement-map path",
        )
        payload = write_historical_association_snapshot_reconciliation(
            paper_dir=paper_dir,
            paper=args.paper,
            raw_audit_path=raw_audit_path,
            witness_map_path=witness_map_path,
            output_path=output_path,
        )
        print(json.dumps(payload, indent=2, sort_keys=True))
        return 0
    except SourceRecordHistoricalAssociationSnapshotReconciliationError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":  # pragma: no cover - CLI entry point.
    raise SystemExit(main())
