#!/usr/bin/env python3
"""Authenticate an archived schema-4 source-semantic projection transition.

This is intentionally narrower than ordinary differential reuse.  It proves
that a prior schema-2 source association and a current schema-2 association
differ only through the audited schema-4-to-schema-5 source projection.  The
admissible transitions are either removal of exactly one top-level source-map
``source_status`` field, or a schema-only change where no such field exists.
The bridge binds exact archived and current raw audits, sidecar, statement
maps, and source-proof-fidelity ledgers.  It does not pair judgments by
declaration, source-map key, or sidecar key.

The consumer must still compare a complete normalized generated descriptor and
require a unique pair.  This module only provides the authenticated association
normalization that makes that comparison meaningful.
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
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports package imports and direct execution.
    from scripts.formalization_protocol import CURRENT_SOURCE_RECORD_PROMPT_VERSION
    from scripts.source_coverage_scope import (
        legacy_source_item_coverage_sha256_before_direct_source_status_exclusion,
        legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded,
        source_item_coverage_sha256,
    )
    from scripts.source_record_integrity import (
        canonical_digest_payload,
        source_record_audit_receipt_error,
    )
    from scripts.source_record_target_disposition import (
        semantic_association_record_digest,
        source_contract_association_record_digest,
        source_map_item_record_digest,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    from formalization_protocol import CURRENT_SOURCE_RECORD_PROMPT_VERSION
    from source_coverage_scope import (
        legacy_source_item_coverage_sha256_before_direct_source_status_exclusion,
        legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded,
        source_item_coverage_sha256,
    )
    from source_record_integrity import (
        canonical_digest_payload,
        source_record_audit_receipt_error,
    )
    from source_record_target_disposition import (
        semantic_association_record_digest,
        source_contract_association_record_digest,
        source_map_item_record_digest,
    )


SOURCE_RECORD_V10_PROMPT_VERSION = CURRENT_SOURCE_RECORD_PROMPT_VERSION
ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_SCHEMA = 1
ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_POLICY_VERSION = (
    "source-record-v10-archived-schema4-direct-source-status-bridge-v1"
)
ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_ARTIFACT_KIND = (
    "source_record_v10_archived_direct_source_status_projection_bridge"
)
ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FILENAME = (
    "source_record_archived_source_status_projection_bridge.json"
)
ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_INTEGRITY_FIELD = (
    "archived_source_status_projection_bridge_sha256"
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_ASSOCIATION_FIELDS = (
    "source_contract_association",
    "semantic_contract_source_association",
    "source_statement_association",
    "semantic_contract_group",
)
_RAW_AUDIT_SECTIONS = (
    "boundary_input_items",
    "conclusion_dependency_items",
    "semantic_model_items",
)
_STATUS_INCLUDED_TO_EXCLUDED = (
    "schema4_direct_source_status_included_to_schema5_excluded"
)
_STATUS_EXCLUDED_SCHEMA_ONLY = (
    "schema4_direct_source_status_excluded_to_schema5_excluded"
)


class ArchivedSourceStatusProjectionBridgeError(ValueError):
    """Raised when a source-status archive bridge is not admissible."""


@dataclass(frozen=True)
class ValidatedArchivedSourceStatusProjectionBridge:
    """An in-memory authority produced only by exact receipt validation.

    Keys of ``prior_association_rebinds`` are complete association-record
    digests.  They are not source-map keys, Lean names, or judgment keys.  A
    consumer may normalize an exact prior association with this object but may
    not use it to find a generated judgment.
    """

    prior_association_rebinds: Mapping[str, Mapping[str, object]]
    association_bindings: Mapping[str, Mapping[str, object]]
    receipt_sha256: str


def _sha256(value: object) -> str:
    candidate = str(value or "").strip().lower()
    return candidate if _SHA256_RE.fullmatch(candidate) else ""


def _bytes_sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _json_object_from_bytes(value: bytes, *, label: str) -> dict[str, Any]:
    try:
        result = json.loads(value)
    except json.JSONDecodeError as exc:
        raise ArchivedSourceStatusProjectionBridgeError(
            f"{label} is not valid JSON: {exc}"
        ) from exc
    if not isinstance(result, dict):
        raise ArchivedSourceStatusProjectionBridgeError(f"{label} is not a JSON object")
    return result


def _relative_paper_path(path: Path, paper_dir: Path, *, label: str) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise ArchivedSourceStatusProjectionBridgeError(
            f"{label} must remain inside the paper directory"
        ) from exc


def _paper_path(paper_dir: Path, raw_path: object, *, label: str) -> Path:
    text = str(raw_path or "").strip()
    if not text:
        raise ArchivedSourceStatusProjectionBridgeError(f"{label} has no path")
    candidate = Path(text)
    if candidate.is_absolute() or any(part == ".." for part in candidate.parts):
        raise ArchivedSourceStatusProjectionBridgeError(
            f"{label} path must be paper-relative"
        )
    try:
        resolved = (paper_dir / candidate).resolve()
        resolved.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise ArchivedSourceStatusProjectionBridgeError(
            f"{label} path escapes the paper directory"
        ) from exc
    return resolved


def _read_json_object(path: Path, *, label: str) -> tuple[dict[str, Any], bytes]:
    try:
        contents = path.read_bytes()
    except OSError as exc:
        raise ArchivedSourceStatusProjectionBridgeError(
            f"could not read {label}: {exc}"
        ) from exc
    return _json_object_from_bytes(contents, label=label), contents


def _record(
    *,
    path: Path,
    contents: bytes,
    paper_dir: Path,
    raw_audit: Mapping[str, object] | None = None,
) -> dict[str, str]:
    result = {
        "path": _relative_paper_path(path, paper_dir, label="bridge artifact"),
        "bytes_sha256": _bytes_sha256(contents),
    }
    if raw_audit is not None:
        audit = _sha256(raw_audit.get("source_record_audit_sha256"))
        integrity = _sha256(raw_audit.get("source_record_audit_integrity_sha256"))
        if not audit or not integrity:
            raise ArchivedSourceStatusProjectionBridgeError(
                "raw audit record has no valid receipt identities"
            )
        result["source_record_audit_sha256"] = audit
        result["source_record_audit_integrity_sha256"] = integrity
    return result


def _record_error(
    recorded: object,
    *,
    path: Path,
    contents: bytes,
    paper_dir: Path,
    label: str,
    raw_audit: Mapping[str, object] | None = None,
) -> str:
    if not isinstance(recorded, Mapping):
        return f"{label} provenance is not an object"
    try:
        expected = _record(
            path=path,
            contents=contents,
            paper_dir=paper_dir,
            raw_audit=raw_audit,
        )
    except ArchivedSourceStatusProjectionBridgeError as exc:
        return str(exc)
    if dict(recorded) != expected:
        return f"{label} bytes, path, or receipt provenance differs"
    return ""


def _raw_audit_error(raw: Mapping[str, object], *, paper: str, label: str) -> str:
    if str(raw.get("paper") or "").strip() != paper:
        return f"{label} raw audit belongs to a different paper"
    if str(raw.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        return f"{label} raw audit does not use the v10 prompt"
    if error := source_record_audit_receipt_error(dict(raw)):
        return f"{label} raw audit receipt is invalid: {error}"
    return ""


def _sidecar_error(sidecar: Mapping[str, object], *, paper: str) -> str:
    if sidecar.get("schema") != 1 or str(sidecar.get("paper") or "").strip() != paper:
        return "archived sidecar does not belong to this paper"
    if str(sidecar.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        return "archived sidecar does not use the v10 prompt"
    if not isinstance(sidecar.get("items") or sidecar.get("field_judgments"), Mapping):
        return "archived sidecar has no response ledger"
    return ""


def _raw_fidelity_projection(value: Mapping[str, object]) -> dict[str, object]:
    """Mirror the one explicit raw-generator optional-field normalization.

    The raw audit emits ``checked_proof_steps: null`` when the source-fidelity
    file omits that optional ledger.  It is a generated shape normalization,
    not source-proof content.  No other missing/null or unknown field is
    normalized here.
    """

    projected = copy.deepcopy(dict(value))
    projected.setdefault("checked_proof_steps", None)
    return projected


def _source_fidelity_error(
    raw: Mapping[str, object], fidelity: Mapping[str, object], *, label: str
) -> str:
    embedded = raw.get("source_proof_fidelity")
    if not isinstance(embedded, Mapping):
        return f"{label} raw audit has no embedded source-proof-fidelity ledger"
    if canonical_digest_payload(_raw_fidelity_projection(embedded)) != canonical_digest_payload(
        _raw_fidelity_projection(fidelity)
    ):
        return f"{label} source-proof-fidelity ledger differs from its raw audit"
    return ""


def _map_error(statement_map: Mapping[str, object], *, label: str) -> str:
    """Validate one exact map without making unrelated items globally stale."""

    raw_items = statement_map.get("items")
    if not isinstance(raw_items, Mapping):
        return f"{label} statement map has no object-valued items ledger"
    if any(
        not str(key).strip() or not isinstance(value, Mapping)
        for key, value in raw_items.items()
    ):
        return f"{label} statement map has an invalid source item"
    return ""


def _raw_statement_map_receipt_error(
    raw: Mapping[str, object], statement_map_bytes: bytes, *, label: str
) -> str:
    """Require the supplied map bytes to be the map named by the raw audit.

    Per-item map pins are necessary for a narrow association transition, but
    they do not authenticate the aggregate source-map snapshot.  In
    particular, an unrelated map edit can preserve every associated item.
    The archived bridge must not turn an arbitrary current map with matching
    items into the historical map that generated a raw audit.
    """

    expected = _sha256(raw.get("paper_statement_map_sha256"))
    if not expected:
        return f"{label} raw audit has no paper-statement-map byte receipt"
    actual = hashlib.sha256(statement_map_bytes).hexdigest()
    if actual != expected:
        return (
            f"{label} raw audit statement-map receipt differs from supplied "
            "statement-map bytes"
        )
    return ""


def _source_map_items(statement_map: Mapping[str, object]) -> dict[str, Mapping[str, object]]:
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, Mapping):  # checked by _map_error.
        return {}
    return {
        str(key).strip(): value
        for key, value in raw_items.items()
        if str(key).strip() and isinstance(value, Mapping)
    }


def _direct_source_status_fields(source_item: Mapping[str, object]) -> list[str]:
    return [
        key
        for key in source_item
        if key == "source_status"
    ]


def _source_status_like_fields(source_item: Mapping[str, object]) -> list[str]:
    """Return canonical and noncanonical top-level status spellings.

    The schema-only route is safe only when the item has no status-looking
    field at all.  A whitespace/case lookalike is new source metadata, not an
    administrative field that this narrow bridge may normalize away.
    """

    return [
        str(key)
        for key in source_item
        if str(key).strip().lower() == "source_status"
    ]


def _schema_two_associations(
    raw_audit: Mapping[str, object], *, label: str
) -> tuple[dict[str, Mapping[str, object]], str]:
    """Collect complete generated schema-2 association records by content digest.

    The field selection is based on generated association schema containers,
    not names of the paper result, source item, or sidecar response.  Repeated
    byte-identical associations are one association identity; distinct records
    with a digest collision fail closed through the canonical equality check.
    """

    found: dict[str, Mapping[str, object]] = {}
    for section in _RAW_AUDIT_SECTIONS:
        raw_items = raw_audit.get(section)
        if not isinstance(raw_items, list):
            return {}, f"{label} raw audit section `{section}` is not a list"
        for item in raw_items:
            if not isinstance(item, Mapping):
                return {}, f"{label} raw audit contains a non-object generated item"
            for field in _ASSOCIATION_FIELDS:
                association = item.get(field)
                if not isinstance(association, Mapping) or association.get("schema") != 2:
                    continue
                digest = source_map_item_record_digest(association)
                prior = found.get(digest)
                if prior is not None and canonical_digest_payload(prior) != canonical_digest_payload(
                    association
                ):
                    return {}, f"{label} raw audit has an ambiguous association record digest"
                found[digest] = association
    return found, ""


def _association_transition(
    association: Mapping[str, object],
    *,
    prior_statement_map_items: Mapping[str, Mapping[str, object]],
    current_statement_map_items: Mapping[str, Mapping[str, object]],
) -> tuple[dict[str, object] | None, dict[str, object] | None, str]:
    """Reconstruct a current association from exactly one permitted change."""

    if association.get("schema") != 2:
        return None, None, "association is not schema 2"
    raw_identities = association.get("source_item_identities")
    signature = association.get("reviewed_elaborated_signature_identity")
    if not isinstance(raw_identities, list) or not raw_identities or not isinstance(signature, Mapping):
        return None, None, "association lacks source identities or an elaborated signature"
    prior_semantics: list[str] = []
    current_semantics: list[str] = []
    rebound_identities: list[dict[str, object]] = []
    identity_rebinds: list[dict[str, str]] = []
    seen_source_keys: set[str] = set()
    changed = False
    for index, raw_identity in enumerate(raw_identities):
        if not isinstance(raw_identity, Mapping):
            return None, None, f"source_item_identities[{index}] is not an object"
        source_key = str(raw_identity.get("source_key") or "").strip()
        source_location = str(raw_identity.get("source_location") or "").strip()
        raw_map_digest = _sha256(raw_identity.get("source_map_item_sha256"))
        prior_semantic = _sha256(raw_identity.get("source_semantic_sha256"))
        if not source_key or source_key in seen_source_keys or not source_location or not raw_map_digest or not prior_semantic:
            return None, None, "association identity lacks a unique key, location, raw map digest, or semantic digest"
        seen_source_keys.add(source_key)
        prior_source_item = prior_statement_map_items.get(source_key)
        current_source_item = current_statement_map_items.get(source_key)
        if prior_source_item is None or current_source_item is None:
            return None, None, "association source identity is absent from an exact statement map"
        if (
            str(prior_source_item.get("source_location") or "").strip()
            != source_location
            or str(current_source_item.get("source_location") or "").strip()
            != source_location
        ):
            return None, None, "association source location differs from an exact statement map"
        if (
            source_map_item_record_digest(prior_source_item) != raw_map_digest
            or source_map_item_record_digest(current_source_item) != raw_map_digest
        ):
            return None, None, "association source-map item digest differs from an exact statement map"
        if canonical_digest_payload(prior_source_item) != canonical_digest_payload(
            current_source_item
        ):
            return None, None, "affected source-map item changed outside direct source_status projection"
        current_semantic = source_item_coverage_sha256(dict(current_source_item), "")
        legacy_included = (
            legacy_source_item_coverage_sha256_before_direct_source_status_exclusion(
                dict(current_source_item), ""
            )
        )
        legacy_excluded = (
            legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
                dict(current_source_item), ""
            )
        )
        if not current_semantic or not legacy_included or not legacy_excluded:
            return None, None, "association source-map semantic projection is malformed"
        transition_kind = "already_schema5_current"
        rebound_identity = copy.deepcopy(dict(raw_identity))
        if prior_semantic != current_semantic:
            direct_status_fields = _direct_source_status_fields(current_source_item)
            status_like_fields = _source_status_like_fields(current_source_item)
            # Without a direct field the two schema-4 projections intentionally
            # coincide.  Prefer the schema-only interpretation in that case;
            # it is narrower than inventing a removed administrative field.
            if prior_semantic == legacy_excluded and not status_like_fields:
                transition_kind = _STATUS_EXCLUDED_SCHEMA_ONLY
            elif prior_semantic == legacy_included:
                if len(direct_status_fields) != 1 or len(status_like_fields) != 1:
                    return None, None, "association does not differ through exactly one top-level source_status field"
                transition_kind = _STATUS_INCLUDED_TO_EXCLUDED
            elif prior_semantic == legacy_excluded:
                # Schema 4 could already exclude the direct administrative
                # field.  With no such field in the exact map item, the only
                # remaining difference is the audited digest-schema version.
                # Retain a strict no-field condition here: a live status field
                # may affect current route/quarantine policy and must not be
                # transported through the schema-only lane.
                if status_like_fields:
                    return None, None, "association does not differ through exactly one top-level source_status field"
                transition_kind = _STATUS_EXCLUDED_SCHEMA_ONLY
            else:
                return None, None, "association source semantic identity is not an exact schema-4 direct-source-status projection"
            if current_semantic in {legacy_included, legacy_excluded}:
                return None, None, "association has no distinct current schema-5 source semantic identity"
            rebound_identity["source_semantic_sha256"] = current_semantic
            changed = True
        prior_semantics.append(prior_semantic)
        current_semantics.append(current_semantic)
        # This binding carries only cryptographic source identities.  The
        # source key above was used to authenticate the map lookup, never to
        # pair an archived judgment to a current judgment.
        identity_rebinds.append(
            {
                "source_map_item_sha256": raw_map_digest,
                "prior_source_semantic_sha256": prior_semantic,
                "current_source_semantic_sha256": current_semantic,
                "transition_kind": transition_kind,
            }
        )
        rebound_identities.append(rebound_identity)
    if not changed:
        return None, None, "association has no schema-4 direct-source-status transition"
    expected_prior_pin = semantic_association_record_digest(prior_semantics, signature)
    if not expected_prior_pin or _sha256(association.get("semantic_association_sha256")) != expected_prior_pin:
        return None, None, "association has a stale prior semantic association pin"
    if "association_sha256" in association and _sha256(association.get("association_sha256")) != source_contract_association_record_digest(association):
        return None, None, "association has a stale prior association record pin"
    rebound = copy.deepcopy(dict(association))
    rebound["source_item_identities"] = rebound_identities
    current_pin = semantic_association_record_digest(current_semantics, signature)
    if not current_pin:
        return None, None, "association has an invalid rebounded semantic association pin"
    rebound["semantic_association_sha256"] = current_pin
    if "association_sha256" in rebound:
        rebound["association_sha256"] = source_contract_association_record_digest(rebound)
    binding = {
        "prior_association_sha256": source_map_item_record_digest(association),
        "current_association_sha256": source_map_item_record_digest(rebound),
        "prior_semantic_association_sha256": expected_prior_pin,
        "current_semantic_association_sha256": current_pin,
        "source_identity_rebinds": sorted(
            identity_rebinds,
            key=lambda entry: (
                entry["source_map_item_sha256"],
                entry["prior_source_semantic_sha256"],
            ),
        ),
    }
    return binding, rebound, ""


def archived_source_status_projection_bridge_digest(payload: Mapping[str, object]) -> str:
    value = copy.deepcopy(dict(payload))
    value.pop(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_INTEGRITY_FIELD, None)
    return source_map_item_record_digest(value)


def build_archived_source_status_projection_bridge(
    *,
    paper: str,
    paper_dir: Path,
    prior_raw_audit: Mapping[str, object],
    prior_raw_audit_bytes: bytes,
    prior_raw_audit_path: Path,
    prior_judgments: Mapping[str, object],
    prior_judgments_bytes: bytes,
    prior_judgments_path: Path,
    prior_statement_map: Mapping[str, object],
    prior_statement_map_bytes: bytes,
    prior_statement_map_path: Path,
    prior_source_proof_fidelity: Mapping[str, object],
    prior_source_proof_fidelity_bytes: bytes,
    prior_source_proof_fidelity_path: Path,
    current_raw_audit: Mapping[str, object],
    current_raw_audit_bytes: bytes,
    current_raw_audit_path: Path,
    current_statement_map: Mapping[str, object],
    current_statement_map_bytes: bytes,
    current_statement_map_path: Path,
    current_source_proof_fidelity: Mapping[str, object],
    current_source_proof_fidelity_bytes: bytes,
    current_source_proof_fidelity_path: Path,
) -> tuple[dict[str, object] | None, str]:
    """Construct the deterministic archived-pair bridge or a refusal reason."""

    for label, supplied, contents in (
        ("prior raw audit", prior_raw_audit, prior_raw_audit_bytes),
        ("prior judgment sidecar", prior_judgments, prior_judgments_bytes),
        ("prior statement map", prior_statement_map, prior_statement_map_bytes),
        ("prior source-proof-fidelity", prior_source_proof_fidelity, prior_source_proof_fidelity_bytes),
        ("current raw audit", current_raw_audit, current_raw_audit_bytes),
        ("current statement map", current_statement_map, current_statement_map_bytes),
        ("current source-proof-fidelity", current_source_proof_fidelity, current_source_proof_fidelity_bytes),
    ):
        try:
            from_bytes = _json_object_from_bytes(contents, label=label)
        except ArchivedSourceStatusProjectionBridgeError as exc:
            return None, str(exc)
        if from_bytes != dict(supplied):
            return None, f"{label} object differs from its exact supplied bytes"
    for label, raw in (("prior", prior_raw_audit), ("current", current_raw_audit)):
        if error := _raw_audit_error(raw, paper=paper, label=label):
            return None, error
    for label, raw, statement_map_bytes in (
        ("prior", prior_raw_audit, prior_statement_map_bytes),
        ("current", current_raw_audit, current_statement_map_bytes),
    ):
        if error := _raw_statement_map_receipt_error(
            raw, statement_map_bytes, label=label
        ):
            return None, error
    if error := _sidecar_error(prior_judgments, paper=paper):
        return None, error
    if error := _map_error(prior_statement_map, label="prior"):
        return None, error
    if error := _map_error(current_statement_map, label="current"):
        return None, error
    if error := _source_fidelity_error(
        prior_raw_audit, prior_source_proof_fidelity, label="prior"
    ):
        return None, error
    if error := _source_fidelity_error(
        current_raw_audit, current_source_proof_fidelity, label="current"
    ):
        return None, error
    # The map snapshots are exact-byte pinned to their respective raw audits.
    # Source-fidelity ledgers are separately compared with each raw's embedded
    # ledger; they need not be globally identical because a later audit may add
    # a narrow direct-parent route for another field. Such a change remains
    # visible in every generated item's fidelity digest, so descriptor pairing
    # below cannot reuse it; requiring ledger equality here would needlessly
    # discard independent unchanged item evidence.
    prior_associations, prior_error = _schema_two_associations(
        prior_raw_audit, label="prior"
    )
    current_associations, current_error = _schema_two_associations(
        current_raw_audit, label="current"
    )
    if prior_error or current_error:
        return None, prior_error or current_error
    prior_source_items = _source_map_items(prior_statement_map)
    current_source_items = _source_map_items(current_statement_map)
    bindings: list[dict[str, object]] = []
    prior_to_rebound: dict[str, Mapping[str, object]] = {}
    seen_current: set[str] = set()
    for prior_digest, association in sorted(prior_associations.items()):
        binding, rebound, transition_error = _association_transition(
            association,
            prior_statement_map_items=prior_source_items,
            current_statement_map_items=current_source_items,
        )
        if transition_error == "association has no schema-4 direct-source-status transition":
            continue
        if transition_error or binding is None or rebound is None:
            return None, "prior association cannot be bridged: " + transition_error
        current_digest = str(binding["current_association_sha256"])
        current_association = current_associations.get(current_digest)
        if current_association is None or canonical_digest_payload(current_association) != canonical_digest_payload(rebound):
            return None, "rebuilt current association is absent or differs in the current raw audit"
        if current_digest in seen_current:
            return None, "two distinct archived association records map to one current association"
        seen_current.add(current_digest)
        if prior_digest in prior_to_rebound:
            return None, "archived association transition is ambiguous"
        prior_to_rebound[prior_digest] = rebound
        bindings.append(binding)
    if not bindings:
        return None, "archive pair has no eligible schema-4 direct-source-status association transition"
    try:
        receipt: dict[str, object] = {
            "schema": ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_SCHEMA,
            "artifact_kind": ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_ARTIFACT_KIND,
            "policy_version": ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_POLICY_VERSION,
            "paper": paper,
            "prior_raw_audit": _record(
                path=prior_raw_audit_path,
                contents=prior_raw_audit_bytes,
                paper_dir=paper_dir,
                raw_audit=prior_raw_audit,
            ),
            "prior_judgments": _record(
                path=prior_judgments_path,
                contents=prior_judgments_bytes,
                paper_dir=paper_dir,
            ),
            "prior_statement_map": _record(
                path=prior_statement_map_path,
                contents=prior_statement_map_bytes,
                paper_dir=paper_dir,
            ),
            "prior_source_proof_fidelity": _record(
                path=prior_source_proof_fidelity_path,
                contents=prior_source_proof_fidelity_bytes,
                paper_dir=paper_dir,
            ),
            "current_raw_audit": _record(
                path=current_raw_audit_path,
                contents=current_raw_audit_bytes,
                paper_dir=paper_dir,
                raw_audit=current_raw_audit,
            ),
            "current_statement_map": _record(
                path=current_statement_map_path,
                contents=current_statement_map_bytes,
                paper_dir=paper_dir,
            ),
            "current_source_proof_fidelity": _record(
                path=current_source_proof_fidelity_path,
                contents=current_source_proof_fidelity_bytes,
                paper_dir=paper_dir,
            ),
            "projection_transition": {
                "legacy_digest_schema": 4,
                "current_digest_schema": 5,
                "permitted_direct_field": "source_status",
                "normalization": (
                    "only exact schema-2 association identities reconstructed from "
                    "the unchanged source-map item projection"
                ),
            },
            "association_rebinds": sorted(
                bindings, key=lambda entry: str(entry["prior_association_sha256"])
            ),
        }
    except ArchivedSourceStatusProjectionBridgeError as exc:
        return None, str(exc)
    receipt[ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_INTEGRITY_FIELD] = (
        archived_source_status_projection_bridge_digest(receipt)
    )
    return receipt, ""


def validate_archived_source_status_projection_bridge(
    receipt: object,
    *,
    paper: str,
    paper_dir: Path,
    prior_raw_audit: Mapping[str, object],
    prior_raw_audit_bytes: bytes,
    prior_raw_audit_path: Path,
    prior_judgments: Mapping[str, object],
    prior_judgments_bytes: bytes,
    prior_judgments_path: Path,
    prior_statement_map: Mapping[str, object],
    prior_statement_map_bytes: bytes,
    prior_statement_map_path: Path,
    prior_source_proof_fidelity: Mapping[str, object],
    prior_source_proof_fidelity_bytes: bytes,
    prior_source_proof_fidelity_path: Path,
    current_raw_audit: Mapping[str, object],
    current_raw_audit_bytes: bytes,
    current_raw_audit_path: Path,
    current_statement_map: Mapping[str, object],
    current_statement_map_bytes: bytes,
    current_statement_map_path: Path,
    current_source_proof_fidelity: Mapping[str, object],
    current_source_proof_fidelity_bytes: bytes,
    current_source_proof_fidelity_path: Path,
) -> tuple[ValidatedArchivedSourceStatusProjectionBridge | None, str]:
    """Rebuild and compare a complete bridge receipt from exact artifact bytes."""

    if not isinstance(receipt, Mapping):
        return None, "archived source-status bridge is not a JSON object"
    if receipt.get("schema") != ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_SCHEMA:
        return None, "archived source-status bridge has an unsupported schema"
    if str(receipt.get("artifact_kind") or "").strip() != ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_ARTIFACT_KIND:
        return None, "archived source-status bridge has the wrong artifact kind"
    if str(receipt.get("policy_version") or "").strip() != ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_POLICY_VERSION:
        return None, "archived source-status bridge has the wrong policy version"
    supplied_digest = _sha256(receipt.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_INTEGRITY_FIELD))
    if not supplied_digest or supplied_digest != archived_source_status_projection_bridge_digest(receipt):
        return None, "archived source-status bridge has a stale integrity digest"
    expected, error = build_archived_source_status_projection_bridge(
        paper=paper,
        paper_dir=paper_dir,
        prior_raw_audit=prior_raw_audit,
        prior_raw_audit_bytes=prior_raw_audit_bytes,
        prior_raw_audit_path=prior_raw_audit_path,
        prior_judgments=prior_judgments,
        prior_judgments_bytes=prior_judgments_bytes,
        prior_judgments_path=prior_judgments_path,
        prior_statement_map=prior_statement_map,
        prior_statement_map_bytes=prior_statement_map_bytes,
        prior_statement_map_path=prior_statement_map_path,
        prior_source_proof_fidelity=prior_source_proof_fidelity,
        prior_source_proof_fidelity_bytes=prior_source_proof_fidelity_bytes,
        prior_source_proof_fidelity_path=prior_source_proof_fidelity_path,
        current_raw_audit=current_raw_audit,
        current_raw_audit_bytes=current_raw_audit_bytes,
        current_raw_audit_path=current_raw_audit_path,
        current_statement_map=current_statement_map,
        current_statement_map_bytes=current_statement_map_bytes,
        current_statement_map_path=current_statement_map_path,
        current_source_proof_fidelity=current_source_proof_fidelity,
        current_source_proof_fidelity_bytes=current_source_proof_fidelity_bytes,
        current_source_proof_fidelity_path=current_source_proof_fidelity_path,
    )
    if error or expected is None:
        return None, "archived source-status bridge cannot be reconstructed: " + error
    if dict(receipt) != expected:
        return None, "archived source-status bridge differs from exact archive/current artifact identities"
    bindings = receipt.get("association_rebinds")
    if not isinstance(bindings, list) or not bindings:
        return None, "archived source-status bridge has no association rebinds"
    prior_associations, prior_error = _schema_two_associations(
        prior_raw_audit, label="prior"
    )
    if prior_error:
        return None, prior_error
    prior_source_items = _source_map_items(prior_statement_map)
    current_source_items = _source_map_items(current_statement_map)
    rebinds: dict[str, Mapping[str, object]] = {}
    binding_by_prior: dict[str, Mapping[str, object]] = {}
    for binding in bindings:
        if not isinstance(binding, Mapping):
            return None, "archived source-status bridge has a non-object association rebind"
        prior_digest = _sha256(binding.get("prior_association_sha256"))
        association = prior_associations.get(prior_digest)
        rebuilt_binding, rebound, transition_error = (
            _association_transition(
                association,
                prior_statement_map_items=prior_source_items,
                current_statement_map_items=current_source_items,
            )
            if association is not None
            else (None, None, "association is absent from archived raw audit")
        )
        if transition_error or rebuilt_binding is None or rebound is None:
            return None, "archived source-status bridge association cannot be rebuilt: " + transition_error
        if canonical_digest_payload(rebuilt_binding) != canonical_digest_payload(binding):
            return None, "archived source-status bridge association binding differs from rebuilt evidence"
        if prior_digest in rebinds:
            return None, "archived source-status bridge has duplicate prior association identities"
        rebinds[prior_digest] = rebound
        binding_by_prior[prior_digest] = binding
    if len(rebinds) != len(bindings):
        return None, "archived source-status bridge association bindings are ambiguous"
    return (
        ValidatedArchivedSourceStatusProjectionBridge(
            prior_association_rebinds=rebinds,
            association_bindings=binding_by_prior,
            receipt_sha256=supplied_digest,
        ),
        "",
    )


def normalized_archived_source_status_association(
    association: Mapping[str, object],
    bridge: ValidatedArchivedSourceStatusProjectionBridge | None,
) -> Mapping[str, object]:
    """Return a rebound association only for an exact archived record match."""

    if bridge is None:
        return association
    if not isinstance(bridge, ValidatedArchivedSourceStatusProjectionBridge):
        return association
    rebound = bridge.prior_association_rebinds.get(source_map_item_record_digest(association))
    return rebound if isinstance(rebound, Mapping) else association


def archived_source_status_association_is_rebound(
    association: Mapping[str, object],
    bridge: ValidatedArchivedSourceStatusProjectionBridge | None,
) -> bool:
    """Whether this exact archived association is covered by the bridge."""

    return bool(
        isinstance(bridge, ValidatedArchivedSourceStatusProjectionBridge)
        and source_map_item_record_digest(association) in bridge.prior_association_rebinds
    )


def rebound_archived_source_status_response(
    response: Mapping[str, object],
    bridge: ValidatedArchivedSourceStatusProjectionBridge | None,
) -> dict[str, object] | None:
    """Advance only response pins proved by one exact archived association.

    A source-credit response can retain a semantic-association pin and a map
    keyed by the source semantic identity.  Both are derived from the exact
    association binding, so neither a source key nor a declaration name can
    move them.  No matching binding leaves a response unchanged; competing
    current pins reject rather than guessing which source claim was reviewed.
    """

    result = copy.deepcopy(dict(response))
    if not isinstance(bridge, ValidatedArchivedSourceStatusProjectionBridge):
        return result
    prior_pin = _sha256(result.get("semantic_association_sha256"))
    if not prior_pin:
        return result
    candidates = [
        binding
        for binding in bridge.association_bindings.values()
        if _sha256(binding.get("prior_semantic_association_sha256")) == prior_pin
    ]
    if not candidates:
        return result
    current_pins = {
        _sha256(binding.get("current_semantic_association_sha256"))
        for binding in candidates
    }
    if len(current_pins) != 1 or not next(iter(current_pins)):
        return None
    result["semantic_association_sha256"] = next(iter(current_pins))
    raw_targets = result.get("corrected_target_sha256_by_source_semantic_sha256")
    if isinstance(raw_targets, Mapping):
        targets = copy.deepcopy(dict(raw_targets))
        for binding in candidates:
            identities = binding.get("source_identity_rebinds")
            if not isinstance(identities, list):
                return None
            for identity in identities:
                if not isinstance(identity, Mapping):
                    return None
                prior = _sha256(identity.get("prior_source_semantic_sha256"))
                current = _sha256(identity.get("current_source_semantic_sha256"))
                if not prior or not current:
                    return None
                if prior != current and prior in targets and current not in targets:
                    targets[current] = targets.pop(prior)
        result["corrected_target_sha256_by_source_semantic_sha256"] = targets
    return result


def _bridge_input_paths(
    receipt: Mapping[str, object], *, paper_dir: Path
) -> tuple[dict[str, Path] | None, str]:
    paths: dict[str, Path] = {}
    for field in (
        "prior_raw_audit",
        "prior_judgments",
        "prior_statement_map",
        "prior_source_proof_fidelity",
        "current_raw_audit",
        "current_statement_map",
        "current_source_proof_fidelity",
    ):
        record = receipt.get(field)
        if not isinstance(record, Mapping):
            return None, f"archived source-status bridge lacks `{field}` provenance"
        try:
            paths[field] = _paper_path(
                paper_dir, record.get("path"), label=f"{field} provenance"
            )
        except ArchivedSourceStatusProjectionBridgeError as exc:
            return None, str(exc)
    return paths, ""


def load_archived_source_status_projection_bridge_context(
    *,
    paper: str,
    paper_dir: Path,
    receipt_path: Path,
) -> tuple[
    ValidatedArchivedSourceStatusProjectionBridge | None,
    dict[str, object] | None,
    dict[str, tuple[Path, dict[str, Any], bytes]] | None,
    str,
]:
    """Load and replay a paper-local bridge against all exact input bytes."""

    try:
        _relative_paper_path(receipt_path, paper_dir, label="bridge receipt")
        receipt, _receipt_bytes = _read_json_object(receipt_path, label="bridge receipt")
        paths, paths_error = _bridge_input_paths(receipt, paper_dir=paper_dir)
        if paths_error or paths is None:
            return None, None, None, paths_error
        inputs = {
            field: (*_read_json_object(path, label=field),)
            for field, path in paths.items()
        }
        # Give callers both path and exact parsed input; each item is produced
        # by bytes read just above, not an in-memory caller substitute.
        evidence = {
            field: (paths[field], inputs[field][0], inputs[field][1])
            for field in paths
        }
    except ArchivedSourceStatusProjectionBridgeError as exc:
        return None, None, None, str(exc)
    context, error = validate_archived_source_status_projection_bridge(
        receipt,
        paper=paper,
        paper_dir=paper_dir,
        prior_raw_audit=evidence["prior_raw_audit"][1],
        prior_raw_audit_bytes=evidence["prior_raw_audit"][2],
        prior_raw_audit_path=evidence["prior_raw_audit"][0],
        prior_judgments=evidence["prior_judgments"][1],
        prior_judgments_bytes=evidence["prior_judgments"][2],
        prior_judgments_path=evidence["prior_judgments"][0],
        prior_statement_map=evidence["prior_statement_map"][1],
        prior_statement_map_bytes=evidence["prior_statement_map"][2],
        prior_statement_map_path=evidence["prior_statement_map"][0],
        prior_source_proof_fidelity=evidence["prior_source_proof_fidelity"][1],
        prior_source_proof_fidelity_bytes=evidence["prior_source_proof_fidelity"][2],
        prior_source_proof_fidelity_path=evidence["prior_source_proof_fidelity"][0],
        current_raw_audit=evidence["current_raw_audit"][1],
        current_raw_audit_bytes=evidence["current_raw_audit"][2],
        current_raw_audit_path=evidence["current_raw_audit"][0],
        current_statement_map=evidence["current_statement_map"][1],
        current_statement_map_bytes=evidence["current_statement_map"][2],
        current_statement_map_path=evidence["current_statement_map"][0],
        current_source_proof_fidelity=evidence["current_source_proof_fidelity"][1],
        current_source_proof_fidelity_bytes=evidence["current_source_proof_fidelity"][2],
        current_source_proof_fidelity_path=evidence["current_source_proof_fidelity"][0],
    )
    return context, receipt, evidence, error


def archived_source_status_projection_bridge_path(paper_dir: Path) -> Path:
    return paper_dir / "audit" / ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FILENAME


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


def _paper_local_path(value: Path | None, paper_dir: Path, *, default: str, label: str) -> Path:
    return _paper_path(paper_dir, value or Path(default), label=label)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--prior-raw-audit", type=Path, required=True)
    parser.add_argument("--prior-judgments", type=Path, required=True)
    parser.add_argument("--prior-statement-map", type=Path)
    parser.add_argument("--prior-source-proof-fidelity", type=Path)
    parser.add_argument("--current-raw-audit", type=Path)
    parser.add_argument("--current-statement-map", type=Path)
    parser.add_argument("--current-source-proof-fidelity", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    paper_dir = args.root.resolve() / "papers" / args.paper
    try:
        if not paper_dir.is_dir():
            raise ArchivedSourceStatusProjectionBridgeError(
                f"paper directory does not exist: {paper_dir}"
            )
        prior_raw_path = _paper_local_path(
            args.prior_raw_audit, paper_dir, default="audit/source_record_audit.json", label="--prior-raw-audit"
        )
        prior_judgments_path = _paper_local_path(
            args.prior_judgments, paper_dir, default="audit/source_record_match_llm.json", label="--prior-judgments"
        )
        prior_map_path = _paper_local_path(
            args.prior_statement_map, paper_dir, default="audit/paper_statement_map.json", label="--prior-statement-map"
        )
        prior_fidelity_path = _paper_local_path(
            args.prior_source_proof_fidelity, paper_dir, default="audit/source_proof_fidelity.json", label="--prior-source-proof-fidelity"
        )
        current_raw_path = _paper_local_path(
            args.current_raw_audit, paper_dir, default="audit/source_record_audit.json", label="--current-raw-audit"
        )
        current_map_path = _paper_local_path(
            args.current_statement_map, paper_dir, default="audit/paper_statement_map.json", label="--current-statement-map"
        )
        current_fidelity_path = _paper_local_path(
            args.current_source_proof_fidelity, paper_dir, default="audit/source_proof_fidelity.json", label="--current-source-proof-fidelity"
        )
        out_path = _paper_local_path(
            args.out, paper_dir, default=f"audit/{ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FILENAME}", label="--out"
        )
        prior_raw, prior_raw_bytes = _read_json_object(prior_raw_path, label="prior raw audit")
        prior_judgments, prior_judgments_bytes = _read_json_object(prior_judgments_path, label="prior judgments")
        prior_map, prior_map_bytes = _read_json_object(prior_map_path, label="prior statement map")
        prior_fidelity, prior_fidelity_bytes = _read_json_object(prior_fidelity_path, label="prior source-proof-fidelity")
        current_raw, current_raw_bytes = _read_json_object(current_raw_path, label="current raw audit")
        current_map, current_map_bytes = _read_json_object(current_map_path, label="current statement map")
        current_fidelity, current_fidelity_bytes = _read_json_object(current_fidelity_path, label="current source-proof-fidelity")
        receipt, error = build_archived_source_status_projection_bridge(
            paper=args.paper,
            paper_dir=paper_dir,
            prior_raw_audit=prior_raw,
            prior_raw_audit_bytes=prior_raw_bytes,
            prior_raw_audit_path=prior_raw_path,
            prior_judgments=prior_judgments,
            prior_judgments_bytes=prior_judgments_bytes,
            prior_judgments_path=prior_judgments_path,
            prior_statement_map=prior_map,
            prior_statement_map_bytes=prior_map_bytes,
            prior_statement_map_path=prior_map_path,
            prior_source_proof_fidelity=prior_fidelity,
            prior_source_proof_fidelity_bytes=prior_fidelity_bytes,
            prior_source_proof_fidelity_path=prior_fidelity_path,
            current_raw_audit=current_raw,
            current_raw_audit_bytes=current_raw_bytes,
            current_raw_audit_path=current_raw_path,
            current_statement_map=current_map,
            current_statement_map_bytes=current_map_bytes,
            current_statement_map_path=current_map_path,
            current_source_proof_fidelity=current_fidelity,
            current_source_proof_fidelity_bytes=current_fidelity_bytes,
            current_source_proof_fidelity_path=current_fidelity_path,
        )
        if error or receipt is None:
            raise ArchivedSourceStatusProjectionBridgeError(error)
        context, error = validate_archived_source_status_projection_bridge(
            receipt,
            paper=args.paper,
            paper_dir=paper_dir,
            prior_raw_audit=prior_raw,
            prior_raw_audit_bytes=prior_raw_bytes,
            prior_raw_audit_path=prior_raw_path,
            prior_judgments=prior_judgments,
            prior_judgments_bytes=prior_judgments_bytes,
            prior_judgments_path=prior_judgments_path,
            prior_statement_map=prior_map,
            prior_statement_map_bytes=prior_map_bytes,
            prior_statement_map_path=prior_map_path,
            prior_source_proof_fidelity=prior_fidelity,
            prior_source_proof_fidelity_bytes=prior_fidelity_bytes,
            prior_source_proof_fidelity_path=prior_fidelity_path,
            current_raw_audit=current_raw,
            current_raw_audit_bytes=current_raw_bytes,
            current_raw_audit_path=current_raw_path,
            current_statement_map=current_map,
            current_statement_map_bytes=current_map_bytes,
            current_statement_map_path=current_map_path,
            current_source_proof_fidelity=current_fidelity,
            current_source_proof_fidelity_bytes=current_fidelity_bytes,
            current_source_proof_fidelity_path=current_fidelity_path,
        )
        if error or context is None:
            raise ArchivedSourceStatusProjectionBridgeError(error)
    except ArchivedSourceStatusProjectionBridgeError as exc:
        print(f"{args.paper}: archived source-status bridge refused: {exc}", file=sys.stderr)
        return 1
    contents = json.dumps(receipt, indent=2, sort_keys=True).encode("utf-8") + b"\n"
    if args.write:
        _atomic_write(out_path, contents)
        print(f"{args.paper}: wrote archived source-status bridge ({len(receipt['association_rebinds'])} associations)")
    else:
        print(f"{args.paper}: archived source-status bridge validates ({len(receipt['association_rebinds'])} associations); rerun with --write")
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI entry point.
    raise SystemExit(main())
