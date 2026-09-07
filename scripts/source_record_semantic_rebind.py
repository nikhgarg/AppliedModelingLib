#!/usr/bin/env python3
"""Authenticated semantic transport for an archived source-record sidecar.

This overlay is deliberately narrower than raw-audit reuse.  A raw audit must
remain current for the live paper folder.  The only thing transported here is a
previous human response, and only after an archived/current generated group has
one exact, name-independent semantic descriptor.

The design has two important consequences.

* Source-map keys and judgment keys are storage addresses, never matching
  evidence.  A match is found through a complete group descriptor containing
  source-content identities, source-contract structure, and expanded Lean
  obligation content.
* A presentation/admin map edit is not assumed harmless.  It is accepted only
  when the archived map bytes are available and every referenced archived map
  record validates against them.  The sole no-snapshot exception is stricter:
  every referenced archived record must have the exact current full map-item
  digest, which can only cover an aggregate/top-level map change.

Serialized overlay entries have no authority on their own.  The loader rereads
the immutable archived raw/map/sidecar inputs, checks the live raw with the
folder-aware source-record identity gate, recomputes the unique descriptor
match, and projects response association pins from the current raw members.

This module is a historical reader only. New closeouts reuse graph-native
judgment leaves and cannot issue another semantic-rebind artifact. The exact
retired CLI remains recoverable at
`a10ef303:scripts/source_record_semantic_rebind.py`; the private reconstruction
function below exists solely so the reader can reproduce and compare the
committed artifact byte-for-byte.
"""

from __future__ import annotations

import copy
import hashlib
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in focused tests.
    from scripts.source_coverage_scope import (
        source_item_coverage_sha256,
        source_record_human_review_semantic_sha256,
    )
    from scripts.source_record_current_revalidation import (
        AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD,
        SELECTED_CURRENT_REVALIDATION_ITEM_FIELD,
        _current_item_pins,
        generated_judgment_keys_sha256,
        generated_judgment_surface_sha256,
    )
    from scripts.source_record_obligation_groups import (
        SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        SOURCE_RECORD_V10_PROMPT_VERSION,
        _complete_proposition_alias_presentation_projection,
        raw_source_record_obligation_groups,
        source_record_obligation_descriptor,
    )
    from scripts.source_record_integrity import (
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_item_reuse_eligible,
    )
    from scripts.source_record_target_disposition import (
        project_source_record_response_association_pins,
        semantic_association_record_digest,
        source_contract_association_record_digest,
        source_map_item_record_digest,
    )
    from scripts.source_record_overlay_protocol import (
        SOURCE_RECORD_SEMANTIC_REBIND_FILENAME,
        SOURCE_RECORD_SEMANTIC_REBIND_ITEM_FIELD,
    )
except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
    from source_coverage_scope import (
        source_item_coverage_sha256,
        source_record_human_review_semantic_sha256,
    )
    from source_record_current_revalidation import (
        AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD,
        SELECTED_CURRENT_REVALIDATION_ITEM_FIELD,
        _current_item_pins,
        generated_judgment_keys_sha256,
        generated_judgment_surface_sha256,
    )
    from source_record_obligation_groups import (
        SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        SOURCE_RECORD_V10_PROMPT_VERSION,
        _complete_proposition_alias_presentation_projection,
        raw_source_record_obligation_groups,
        source_record_obligation_descriptor,
    )
    from source_record_integrity import (
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_item_reuse_eligible,
    )
    from source_record_target_disposition import (
        project_source_record_response_association_pins,
        semantic_association_record_digest,
        source_contract_association_record_digest,
        source_map_item_record_digest,
    )
    from source_record_overlay_protocol import (
        SOURCE_RECORD_SEMANTIC_REBIND_FILENAME,
        SOURCE_RECORD_SEMANTIC_REBIND_ITEM_FIELD,
    )


SOURCE_RECORD_SEMANTIC_REBIND_SCHEMA = 2
LEGACY_SOURCE_RECORD_SEMANTIC_REBIND_POLICY_VERSION = (
    "source-record-v10-item-level-semantic-sidecar-rebind-v1"
)
SOURCE_RECORD_SEMANTIC_REBIND_POLICY_VERSION = (
    "source-record-v10-item-level-semantic-sidecar-rebind-v2"
)
SOURCE_RECORD_SEMANTIC_REBIND_ARTIFACT_KIND = (
    "source_record_v10_item_level_semantic_sidecar_rebind"
)
SOURCE_RECORD_SEMANTIC_REBIND_INTEGRITY_FIELD = "source_record_semantic_rebind_sha256"
GENERATED_TAXONOMY_CORE_ADAPTER_FIELD = "generated_taxonomy_core_adapter"
GENERATED_TAXONOMY_CORE_ADAPTER_SCHEMA = 1
GENERATED_TAXONOMY_CORE_ADAPTER_POLICY_VERSION = (
    "source-record-generated-taxonomy-core-adapter-v1"
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.I)

# This is a deliberately small compatibility boundary for a documented raw
# audit evolution.  These generated classification facts may be absent from a
# historical row.  They are not the source-to-Lean semantic core used to find
# a rebind: that core remains the source identity/route and expanded Lean
# surface below.  Unknown fields are never stripped.
_GENERATED_TAXONOMY_CORE_FIELDS = (
    "proposition_sort",
    "proposition_sort_evidence",
    "theorem_facing_semantic_role",
    "semantic_restriction_role",
    "semantic_restriction_candidates",
    "structural_type_sha256",
)
_GENERATED_TAXONOMY_NESTED_INPUT_FIELDS = ("input_origin",)
_GENERATED_TAXONOMY_PROPOSITION_SORTS = frozenset({"true", "false", "unknown"})
_GENERATED_TAXONOMY_ROLES = frozenset(
    {"proof_bearing", "data", "data_or_container", "unclassified_theorem_input"}
)
_GENERATED_TAXONOMY_RESTRICTION_ROLES = frozenset(
    {
        "requires_source_or_lean_closure",
        "requires_semantic_route",
        "carrier_coherence_only",
        "unclassified",
    }
)


def _semantic_rebind_policy_configuration(policy_version: object) -> dict[str, object]:
    """Return the immutable compatibility policy for a serialized overlay."""

    if policy_version == LEGACY_SOURCE_RECORD_SEMANTIC_REBIND_POLICY_VERSION:
        return {
            "generated_taxonomy_core_adapter": False,
            "policy_version": LEGACY_SOURCE_RECORD_SEMANTIC_REBIND_POLICY_VERSION,
        }
    if policy_version == SOURCE_RECORD_SEMANTIC_REBIND_POLICY_VERSION:
        return {
            "generated_taxonomy_core_adapter": True,
            "policy_version": SOURCE_RECORD_SEMANTIC_REBIND_POLICY_VERSION,
        }
    raise SourceRecordSemanticRebindError(
        "semantic rebind overlay has an unsupported policy version"
    )


def _generated_taxonomy_core_adapter_receipt() -> dict[str, object]:
    """Describe the only generated taxonomy projection admitted by v2."""

    return {
        "schema": GENERATED_TAXONOMY_CORE_ADAPTER_SCHEMA,
        "policy_version": GENERATED_TAXONOMY_CORE_ADAPTER_POLICY_VERSION,
        "omitted_generated_fields": list(_GENERATED_TAXONOMY_CORE_FIELDS),
        "omitted_generated_input_fields": list(
            _GENERATED_TAXONOMY_NESTED_INPUT_FIELDS
        ),
        "legacy_absence_allowed": True,
        "requires_complete_known_field_set": True,
    }

# These are generated credentials, not human review content.  They are the
# only response fields the materializer replaces.  Unknown fields deliberately
# remain in the archived response hash and hence fail closed.
_REBOUND_RESPONSE_FIELDS = frozenset(
    {
        "source_record_audit_sha256",
        "source_record_item_digest_schema",
        "source_record_item_sha256",
        "source_record_item_sha256s",
        "semantic_association_sha256",
        "source_contract_association_sha256",
        "source_map_item_keys",
        "source_map_item_keys_sha256",
        "source_map_item_sha256_by_key",
        "source_item_semantic_sha256",
        "source_item_semantic_sha256_by_key",
        "corrected_target_sha256_by_source_item",
        "corrected_target_sha256_by_source_semantic_sha256",
        SOURCE_RECORD_SEMANTIC_REBIND_ITEM_FIELD,
    }
)
_PRIOR_TRANSPORT_FIELDS = frozenset(
    {
        "source_record_schema4_to5_migration",
        "source_record_differential_revalidation",
        "source_record_attested_selected_semantic_reuse",
        "source_record_historical_descriptor_migration",
        SOURCE_RECORD_SEMANTIC_REBIND_ITEM_FIELD,
    }
)
# A composed selected-plus-overlay sidecar has these two active response
# markers.  They are not ordinary prior evidence: the special historical
# composition validator must replay their complete provenance before this
# transport will accept them.  They are deliberately separate from the older
# generic prior-transport markers above, which remain inadmissible here.
_HISTORICAL_COMPOSITION_RESPONSE_TRANSPORT_FIELDS = frozenset(
    {
        SELECTED_CURRENT_REVALIDATION_ITEM_FIELD,
        AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD,
    }
)
_HISTORICAL_COMPOSITION_SIDECAR_TRANSPORT_FIELDS = frozenset(
    {
        "current_selected_semantic_revalidation",
        "source_record_authenticated_evidence_composition",
    }
)
HISTORICAL_COMPOSITION_PARENT_FIELD = "historical_composition_parent"
_ASSOCIATION_FIELDS = (
    "source_contract_association",
    "semantic_contract_source_association",
    "source_statement_association",
    "semantic_contract_group",
)
_CURRENT_RECEIPT_FIELDS = frozenset(
    {
        "effective_lean_source_declaration",
        "effective_qualified_declaration",
        "reviewed_elaborated_signature_identities",
        "source_record_item_reuse_eligibility",
        "source_record_item_digest_schema",
        "source_record_item_semantic_id",
        "source_record_item_context_sha256",
        "source_record_item_sha256",
    }
)
_LEGACY_RECEIPT_FIELDS = frozenset(
    {
        "paper_statement_map_sha256",
        "semantic_context_requirements_sha256",
    }
)
_EXPANDED_LEAN_SURFACE_FIELDS = (
    "expanded_input_type",
    "result_relation",
    "proposition_alias_expansion",
    "subtype_predicate_proposition_alias_expansion",
)

_LOADED_OVERLAY_ITEM_SENTINEL = object()
_CURRENT_IDENTITY_CONTEXT_SENTINEL = object()
_IDENTITY_REVALIDATION_DEFERRED_PREFIX = (
    "source-record identity revalidation deferred:"
)


class SourceRecordSemanticRebindError(ValueError):
    """Raised when an item-level semantic sidecar transport is inadmissible."""


class SourceRecordSemanticRebindIdentityDeferred(SourceRecordSemanticRebindError):
    """Raised when a live identity replay is temporarily unavailable.

    A busy source-record scan is neither proof that the optional transport is
    absent nor a stale-transport verdict.  Callers that construct a current
    manual-review worklist must stop and retry after the scan releases its
    evidence lock rather than treating the lane as an empty overlay.
    """


def _identity_revalidation_is_deferred(error: object) -> bool:
    """Recognize the evidence gate's explicit transient-identity result."""

    return str(error or "").strip().startswith(
        _IDENTITY_REVALIDATION_DEFERRED_PREFIX
    )


class _LoadedSourceRecordSemanticRebindItem(dict[str, Any]):
    __slots__ = ("_source_record_semantic_rebind_loader_token",)

    def __init__(self, value: Mapping[str, Any]) -> None:
        super().__init__(value)
        self._source_record_semantic_rebind_loader_token = _LOADED_OVERLAY_ITEM_SENTINEL


@dataclass(frozen=True)
class _CurrentSemanticRebindIdentityContext:
    """One in-memory proof that a caller has checked the live raw identity.

    This object is intentionally not serialized or included in any receipt. It
    merely lets one overlay-registry invocation share a folder-aware identity
    check across the schema-2 loader and legacy bridge without treating a
    cached result as durable evidence.
    """

    paper_dir: Path
    paper: str
    current_source_record_audit_sha256: str
    current_raw_canonical_sha256: str
    paper_statement_map_sha256: str
    _token: object = field(repr=False, compare=False)


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


def _payload_is_non_evidence(payload: Mapping[str, Any]) -> bool:
    """Match the differential transport's explicit non-evidence policy.

    Filenames are navigation only.  A payload is excluded solely by its own
    explicit scaffold/candidate markers or candidate/proposal artifact and
    validator classifications.
    """

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


def _read_json_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordSemanticRebindError(
            f"could not read {label} at {path}: {exc}"
        ) from exc
    if not isinstance(value, dict):
        raise SourceRecordSemanticRebindError(f"{label} at {path} is not a JSON object")
    return value


def _relative_paper_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordSemanticRebindError(
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
        raise SourceRecordSemanticRebindError(
            f"{label} must be a normalized paper-relative path"
        )
    path = (paper_dir / Path(*pure.parts)).resolve()
    if _relative_paper_path(path, paper_dir) != text:
        raise SourceRecordSemanticRebindError(f"{label} is not canonical")
    return path


def _same_resolved_path(left: Path, right: Path) -> bool:
    try:
        return left.resolve() == right.resolve()
    except OSError:
        return False


def _canonical_live_raw_error(
    current_raw_audit: Mapping[str, Any], *, paper_dir: Path
) -> str:
    """Require the caller's live raw object to be the canonical file bytes.

    The overlay may reuse an unchanged *item* after unrelated canonical raw
    changes, but it cannot treat an arbitrary self-consistent in-memory raw as
    the live paper.  The archived current snapshot is authenticated separately
    by the overlay replay; this check binds the receiving side to the canonical
    raw audit that the workflow will actually consume.
    """

    canonical_path = paper_dir / "audit" / "source_record_audit.json"
    try:
        canonical_raw = _read_json_object(canonical_path, label="canonical current raw audit")
    except SourceRecordSemanticRebindError as exc:
        return str(exc)
    if canonical_digest_payload(canonical_raw) != canonical_digest_payload(
        current_raw_audit
    ):
        return "live current raw audit does not equal canonical raw-audit bytes"
    if _sha256(canonical_raw.get("source_record_audit_sha256")) != _sha256(
        current_raw_audit.get("source_record_audit_sha256")
    ):
        return "live current raw audit has a different canonical aggregate receipt"
    return ""


def _file_provenance(path: Path, paper_dir: Path, *, raw: Mapping[str, Any] | None = None) -> dict[str, str]:
    value = {
        "path": _relative_paper_path(path, paper_dir),
        "file_sha256": _file_sha256(path),
    }
    if raw is not None:
        value.update(
            {
                "source_record_audit_sha256": _sha256(raw.get("source_record_audit_sha256")),
                "source_record_audit_integrity_sha256": _sha256(
                    raw.get("source_record_audit_integrity_sha256")
                ),
                "paper_statement_map_sha256": _sha256(raw.get("paper_statement_map_sha256")),
            }
        )
    return value


def _raw_basic_error(raw: object, *, paper: str, label: str) -> str:
    if not isinstance(raw, Mapping):
        return f"{label} raw audit is not an object"
    # Raw audits are evidence inputs too.  Do not allow a self-consistent
    # candidate/scaffold payload to enter either the archived or live replay
    # path merely because its receipt and Lean metadata are otherwise valid.
    if _payload_is_non_evidence(raw):
        return f"{label} raw audit is explicitly marked non-evidence"
    if raw.get("paper") != paper:
        return f"{label} raw audit records a different paper"
    if str(raw.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        return f"{label} raw audit does not use the v10 prompt"
    if str(raw.get("source_record_policy_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        return f"{label} raw audit does not use the v10 policy"
    if not _sha256(raw.get("source_record_audit_sha256")):
        return f"{label} raw audit has no aggregate receipt"
    if not _sha256(raw.get("paper_statement_map_sha256")):
        return f"{label} raw audit has no paper statement-map receipt"
    if error := source_record_audit_receipt_error(raw):
        return f"{label} raw audit receipt is invalid: {error}"
    return ""


def _reusable_raw_error(raw: object, *, paper: str, label: str) -> str:
    """Require a raw audit to be a successful, non-recursive Lean issuance."""

    if error := _raw_basic_error(raw, paper=paper, label=label):
        return error
    if not isinstance(raw, Mapping):  # protected above; narrows static typing.
        return f"{label} raw audit is not an object"
    lean_check = raw.get("lean_check")
    if not isinstance(lean_check, Mapping) or lean_check.get("returncode") != 0:
        return f"{label} raw audit lacks a successful Lean check"
    try:
        recursion_failure_count = int(raw.get("recursion_failure_count") or 0)
    except (TypeError, ValueError):
        return f"{label} raw audit has a malformed recursion failure count"
    if recursion_failure_count != 0:
        return f"{label} raw audit has recursion failures"
    return ""


def _prior_raw_error(raw: object, *, paper: str, label: str) -> str:
    """Apply the live raw-audit execution gate to archived reuse evidence."""

    return _reusable_raw_error(raw, paper=paper, label=label)


def _current_raw_error(raw: object, *, paper: str, label: str) -> str:
    return _reusable_raw_error(raw, paper=paper, label=label)


def _map_items(statement_map: Mapping[str, Any]) -> Mapping[str, Any]:
    items = statement_map.get("items")
    if not isinstance(items, Mapping):
        raise SourceRecordSemanticRebindError("paper statement map has no items object")
    return items


def _map_items_by_full_digest(
    map_items: Mapping[str, Any], *, label: str
) -> dict[str, list[Mapping[str, Any]]]:
    """Index full map records without making a storage key a match selector."""

    out: dict[str, list[Mapping[str, Any]]] = {}
    for source_item in map_items.values():
        if not isinstance(source_item, Mapping):
            raise SourceRecordSemanticRebindError(
                f"{label} has a malformed statement-map item"
            )
        digest = source_map_item_record_digest(source_item)
        if not _sha256(digest):
            raise SourceRecordSemanticRebindError(
                f"{label} has an undigestible statement-map item"
            )
        out.setdefault(digest, []).append(source_item)
    return out


def _historical_association_snapshot_module() -> Any:
    """Load the exceptional map-reconciliation lane without import cycles."""

    try:
        from scripts import (
            source_record_historical_association_snapshot_reconciliation as reconciliation,
        )
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        import source_record_historical_association_snapshot_reconciliation as reconciliation
    return reconciliation


def _reconciled_prior_map(
    *,
    reconciliation_path: Path,
    paper_dir: Path,
    paper: str,
    prior_raw_path: Path,
    prior_raw: Mapping[str, Any],
) -> tuple[Mapping[str, Any], dict[str, Any]]:
    """Load the sole exception to an exact archived map byte receipt.

    The reconciliation does not repair the archived aggregate receipt.  It
    establishes only that every full source-map item identity used by that raw
    audit resolves uniquely in one immutable witness map.  Bind the raw path
    and every retained aggregate field here before allowing the witness map to
    feed semantic descriptor construction.
    """

    reconciliation = _historical_association_snapshot_module()
    try:
        loaded = reconciliation.load_historical_association_snapshot_reconciliation(
            paper_dir=paper_dir,
            paper=paper,
            artifact_path=reconciliation_path,
        )
    except reconciliation.SourceRecordHistoricalAssociationSnapshotReconciliationError as exc:
        raise SourceRecordSemanticRebindError(
            f"historical association snapshot reconciliation is invalid: {exc}"
        ) from exc
    if not reconciliation.is_loaded_historical_association_snapshot_reconciliation(
        loaded
    ):
        raise SourceRecordSemanticRebindError(
            "historical association snapshot reconciliation has no loader authority"
        )
    raw_meta = loaded.get("archived_raw_audit")
    witness_meta = loaded.get("immutable_witness_statement_map")
    if not isinstance(raw_meta, Mapping) or not isinstance(witness_meta, Mapping):
        raise SourceRecordSemanticRebindError(
            "historical association snapshot reconciliation has malformed provenance"
        )
    try:
        recorded_raw_path = _resolve_paper_path(
            raw_meta.get("path"), paper_dir, label="reconciled archived raw-audit path"
        )
        witness_path = _resolve_paper_path(
            witness_meta.get("path"),
            paper_dir,
            label="reconciled witness statement-map path",
        )
        witness_map = _read_json_object(
            witness_path, label="reconciled witness statement map"
        )
    except SourceRecordSemanticRebindError:
        raise
    if not _same_resolved_path(recorded_raw_path, prior_raw_path):
        raise SourceRecordSemanticRebindError(
            "historical association reconciliation refers to a different archived raw audit"
        )
    if _sha256(raw_meta.get("bytes_sha256")) != _file_sha256(prior_raw_path):
        raise SourceRecordSemanticRebindError(
            "historical association reconciliation raw-audit bytes differ from prior provenance"
        )
    for field_name, artifact_field in (
        ("source_record_audit_sha256", "source_record_audit_sha256"),
        ("source_record_audit_integrity_sha256", "source_record_audit_integrity_sha256"),
        ("paper_statement_map_sha256", "reported_paper_statement_map_sha256"),
    ):
        if _sha256(raw_meta.get(artifact_field)) != _sha256(prior_raw.get(field_name)):
            raise SourceRecordSemanticRebindError(
                "historical association reconciliation does not match archived raw "
                f"`{field_name}`"
            )
    if _sha256(witness_meta.get("bytes_sha256")) != _file_sha256(witness_path):
        raise SourceRecordSemanticRebindError(
            "historical association reconciliation witness-map bytes changed"
        )
    actual_witness_sha = _file_sha256(witness_path)
    if _sha256(witness_meta.get("actual_paper_statement_map_sha256")) != actual_witness_sha:
        raise SourceRecordSemanticRebindError(
            "historical association reconciliation witness-map receipt is stale"
        )
    _map_items(witness_map)
    return witness_map, {
        "mode": "historical_association_snapshot_reconciliation",
        "reconciliation": {
            "path": _relative_paper_path(reconciliation_path, paper_dir),
            "file_sha256": _file_sha256(reconciliation_path),
            "integrity_sha256": _sha256(
                loaded.get(
                    "source_record_historical_association_snapshot_reconciliation_sha256"
                )
            ),
        },
        "witness_statement_map": {
            "path": _relative_paper_path(witness_path, paper_dir),
            "file_sha256": actual_witness_sha,
        },
        "archived_reported_paper_statement_map_sha256": _sha256(
            prior_raw.get("paper_statement_map_sha256")
        ),
    }


def _map_provenance(
    path: Path, paper_dir: Path, *, expected_raw_map_sha: str
) -> dict[str, str]:
    actual = _file_sha256(path)
    if actual != expected_raw_map_sha:
        raise SourceRecordSemanticRebindError(
            "statement-map bytes do not equal the raw audit paper_statement_map_sha256"
        )
    return {
        "path": _relative_paper_path(path, paper_dir),
        "file_sha256": actual,
        "paper_statement_map_sha256": expected_raw_map_sha,
    }


def _strict_no_alias_receipt(value: object) -> bool:
    """Allow only the known complete no-alias schema addition to disappear."""

    if not isinstance(value, Mapping):
        return False
    allowed = {
        "schema",
        "reviewed_declaration",
        "effective_declaration",
        "effective_kind",
        "alias_present",
        "complete",
        "steps",
        "blocked_routes",
    }
    return bool(
        set(value).issubset(allowed)
        and value.get("schema") == 1
        and value.get("alias_present") is False
        and value.get("complete") is True
        and value.get("steps") == []
        and value.get("blocked_routes") == []
        and str(value.get("reviewed_declaration") or "").strip()
        and str(value.get("effective_declaration") or "").strip()
        and str(value.get("effective_kind") or "").strip()
    )


def _identity_from_map(
    raw_identity: Mapping[str, Any],
    *,
    map_items: Mapping[str, Any],
    map_items_by_full_digest: Mapping[str, list[Mapping[str, Any]]] | None = None,
    current: bool,
    label: str,
) -> dict[str, Any]:
    """Validate a raw association against its own immutable source-map record.

    ``source_key`` is used only to dereference the record inside that map.  The
    returned identity deliberately omits it, so it cannot determine a match
    between the archived and current maps.
    """

    source_key = str(raw_identity.get("source_key") or "").strip()
    source_location = str(raw_identity.get("source_location") or "").strip()
    source_kind = str(raw_identity.get("source_kind") or "").strip()
    supplied_map_digest = _sha256(raw_identity.get("source_map_item_sha256"))
    if map_items_by_full_digest is None:
        source_item = map_items.get(source_key)
    else:
        candidates = map_items_by_full_digest.get(supplied_map_digest, [])
        source_item = candidates[0] if len(candidates) == 1 else None
    if (
        not source_key
        or not source_location
        or not source_kind
        or not supplied_map_digest
        or not isinstance(source_item, Mapping)
    ):
        raise SourceRecordSemanticRebindError(
            f"{label} has no complete source-map identity"
        )
    if str(source_item.get("source_location") or "").strip() != source_location:
        raise SourceRecordSemanticRebindError(f"{label} source location differs from its map record")
    if str(source_item.get("source_kind") or "").strip() != source_kind:
        raise SourceRecordSemanticRebindError(f"{label} source kind differs from its map record")
    if source_map_item_record_digest(source_item) != supplied_map_digest:
        raise SourceRecordSemanticRebindError(f"{label} source-map item digest is stale")
    # The source-map direct-route convention intentionally omits
    # ``semantic_contract``.  The generator represents that same empty
    # direct-route contract with all four canonical contract fields present
    # and empty, so normalize only this documented representation before
    # comparing content.  A nonmapping map value remains invalid rather than
    # being silently projected away.
    contract = raw_identity.get("semantic_contract")
    map_contract = source_item.get("semantic_contract")
    if map_contract is None:
        map_contract = {
            field: ""
            for field in (
                "evidence_declaration",
                "spec_declaration",
                "evidence_mode",
                "semantic_shape",
            )
        }
    if not isinstance(contract, Mapping) or not isinstance(map_contract, Mapping) or (
        canonical_digest_payload(contract) != canonical_digest_payload(map_contract)
    ):
        raise SourceRecordSemanticRebindError(f"{label} source-contract route differs from its map record")
    receipt_semantic = source_item_coverage_sha256(dict(source_item), "")
    if not receipt_semantic:
        raise SourceRecordSemanticRebindError(f"{label} has no source-content identity")
    supplied_semantic = _sha256(raw_identity.get("source_semantic_sha256"))
    if current and supplied_semantic != receipt_semantic:
        raise SourceRecordSemanticRebindError(f"{label} source semantic identity is stale")
    if not current and supplied_semantic and supplied_semantic != receipt_semantic:
        raise SourceRecordSemanticRebindError(
            f"{label} archived source semantic identity disagrees with its archived map"
        )
    review_semantic = source_record_human_review_semantic_sha256(source_item, "")
    if not review_semantic:
        raise SourceRecordSemanticRebindError(
            f"{label} has no source human-review identity"
        )
    return {
        "source_item_semantic_sha256": review_semantic,
        "_source_item_receipt_semantic_sha256": receipt_semantic,
        # The full semantic contract is checked against this map record above,
        # but its declaration strings are navigation coordinates.  Cross-map
        # matching instead uses the source-content identity, route role/mode,
        # expanded Lean obligation, and (for current rows) the independently
        # validated name-independent semantic-association pin.  A theorem or
        # helper FQN rename must not manufacture or invalidate reuse.
        "source_kind": source_kind,
    }


def _association_structure_projection(value: Mapping[str, Any]) -> dict[str, object]:
    """Retain unknown structural fields while removing generated coordinates."""

    omitted = {
        "schema",
        "association_sha256",
        "semantic_association_sha256",
        "source_item_identities",
        "source_map_item_keys",
        "source_map_item_keys_sha256",
        "source_map_item_sha256_by_key",
        "reviewed_declaration_identity",
        "reviewed_elaborated_signature_identity",
        "semantic_model_judgment_key",
        "paired_qualified_declaration",
    }
    return {
        str(key): copy.deepcopy(raw_value)
        for key, raw_value in value.items()
        if str(key) not in omitted
    }


def _current_signature_receipt(item: Mapping[str, Any], *, label: str) -> dict[str, Any]:
    identity = item.get("reviewed_declaration_identity")
    if not isinstance(identity, Mapping):
        raise SourceRecordSemanticRebindError(f"{label} lacks a reviewed declaration identity")
    qualified = str(identity.get("qualified_declaration") or "").strip()
    declaration_sha = _sha256(identity.get("declaration_sha256"))
    if not qualified or not declaration_sha:
        raise SourceRecordSemanticRebindError(f"{label} has a malformed reviewed declaration identity")
    signatures = item.get("reviewed_elaborated_signature_identities")
    if not isinstance(signatures, list) or not signatures:
        raise SourceRecordSemanticRebindError(f"{label} lacks elaborated-signature identities")
    seen: set[str] = set()
    signature_digests: list[str] = []
    by_qualified: dict[str, str] = {}
    for raw_signature in signatures:
        if not isinstance(raw_signature, Mapping):
            raise SourceRecordSemanticRebindError(f"{label} has a malformed elaborated signature")
        signature_qualified = str(raw_signature.get("qualified_declaration") or "").strip()
        digest = _sha256(raw_signature.get("elaborated_signature_sha256"))
        if not signature_qualified or not digest or signature_qualified in seen:
            raise SourceRecordSemanticRebindError(f"{label} has an ambiguous elaborated signature ledger")
        seen.add(signature_qualified)
        by_qualified[signature_qualified] = digest
        signature_digests.append(digest)
    if qualified not in by_qualified:
        raise SourceRecordSemanticRebindError(
            f"{label} signature ledger omits the reviewed declaration"
        )
    effective = item.get("effective_lean_source_declaration")
    if effective is not None and (
        not isinstance(effective, str)
        or effective != item.get("lean_source_declaration")
    ):
        raise SourceRecordSemanticRebindError(
            f"{label} effective Lean declaration is not byte-identical to its reviewed declaration"
        )
    effective_qualified = item.get("effective_qualified_declaration")
    if effective_qualified is not None and str(effective_qualified).strip() != qualified:
        raise SourceRecordSemanticRebindError(
            f"{label} effective declaration coordinate does not match the reviewed declaration"
        )
    if not source_record_item_reuse_eligible(
        item, expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    ):
        raise SourceRecordSemanticRebindError(
            f"{label} is not independently item-reuse eligible"
        )
    return {
        "reviewed_elaborated_signature_sha256": sorted(signature_digests),
        "reviewed_declaration_sha256": declaration_sha,
        "_signature_by_qualified": by_qualified,
        "_qualified": qualified,
    }


def _association_descriptor(
    item: Mapping[str, Any],
    *,
    map_items: Mapping[str, Any],
    map_items_by_full_digest: Mapping[str, list[Mapping[str, Any]]] | None,
    current: bool,
    current_signature: Mapping[str, Any] | None,
    label: str,
) -> list[dict[str, Any]]:
    """Validate source routes and return a key/FQN-independent match surface."""

    result: list[dict[str, Any]] = []
    for field_name in _ASSOCIATION_FIELDS:
        association = item.get(field_name)
        if association is None:
            continue
        if not isinstance(association, Mapping):
            raise SourceRecordSemanticRebindError(
                f"{label} {field_name} is malformed"
            )
        # A historical source record can already carry the schema-2
        # association receipt.  Treat it as an authenticated historical
        # witness, not as a schema downgrade.  Schema 1 remains supported for
        # genuine pre-schema-2 archives; a live row must always be schema 2.
        schema = association.get("schema")
        admissible_schemas = {2} if current else {1, 2}
        if schema not in admissible_schemas:
            raise SourceRecordSemanticRebindError(
                f"{label} {field_name} has unsupported association schema"
            )
        if _sha256(association.get("association_sha256")) != source_contract_association_record_digest(
            association
        ):
            raise SourceRecordSemanticRebindError(
                f"{label} {field_name} has a stale association digest"
            )
        raw_identities = association.get("source_item_identities")
        if not isinstance(raw_identities, list) or not raw_identities:
            raise SourceRecordSemanticRebindError(
                f"{label} {field_name} has no source identities"
            )
        identities = [
            _identity_from_map(
                raw_identity,
                map_items=map_items,
                map_items_by_full_digest=map_items_by_full_digest,
                current=current,
                label=f"{label} {field_name} source identity {index}",
            )
            for index, raw_identity in enumerate(raw_identities)
            if isinstance(raw_identity, Mapping)
        ]
        if len(identities) != len(raw_identities):
            raise SourceRecordSemanticRebindError(
                f"{label} {field_name} has a malformed source identity"
            )
        semantic_ids = [identity["source_item_semantic_sha256"] for identity in identities]
        receipt_semantic_ids = [
            identity["_source_item_receipt_semantic_sha256"]
            for identity in identities
        ]
        if len(set(semantic_ids)) != len(semantic_ids):
            raise SourceRecordSemanticRebindError(
                f"{label} {field_name} duplicates a source identity"
            )
        role = str(
            association.get("semantic_contract_member_role") or association.get("role") or ""
        ).strip()
        mode = str(association.get("association_mode") or "").strip()
        if not role or not mode:
            raise SourceRecordSemanticRebindError(
                f"{label} {field_name} lacks route role or mode"
            )
        if current or schema == 2:
            # Schema-2 historical rows also have an elaborated route receipt.
            # Validate it against the row's own receipt ledger before using
            # its old human response; only the live row supplies the current
            # route receipt that is persisted into the rebind artifact.
            route_receipt = current_signature or _current_signature_receipt(
                item, label=label
            )
            if route_receipt is None:  # defensive; helper never returns None.
                raise SourceRecordSemanticRebindError(f"{label} lacks a route receipt")
            signature = association.get("reviewed_elaborated_signature_identity")
            if not isinstance(signature, Mapping):
                raise SourceRecordSemanticRebindError(
                    f"{label} {field_name} lacks an elaborated association signature"
                )
            signature_qualified = str(signature.get("qualified_declaration") or "").strip()
            signature_digest = _sha256(signature.get("elaborated_signature_sha256"))
            signatures_by_qualified = route_receipt.get("_signature_by_qualified")
            if (
                not isinstance(signatures_by_qualified, Mapping)
                or signatures_by_qualified.get(signature_qualified) != signature_digest
            ):
                raise SourceRecordSemanticRebindError(
                    f"{label} {field_name} association signature is absent from the current route ledger"
                )
            expected = semantic_association_record_digest(
                receipt_semantic_ids, signature
            )
            if not expected or _sha256(association.get("semantic_association_sha256")) != expected:
                raise SourceRecordSemanticRebindError(
                    f"{label} {field_name} has a stale semantic association digest"
                )
        result.append(
            {
                "association_field": field_name,
                "association_mode": mode,
                "semantic_contract_member_role": role,
                "source_identities": sorted(
                    [
                        {
                            "source_item_semantic_sha256": identity[
                                "source_item_semantic_sha256"
                            ],
                            "source_kind": identity["source_kind"],
                        }
                        for identity in identities
                    ],
                    key=lambda identity: str(identity["source_item_semantic_sha256"]),
                ),
                "association_structure": _association_structure_projection(association),
            }
        )
    return sorted(result, key=lambda value: _canonical_digest(value))


def _expanded_lean_surface(item: Mapping[str, Any]) -> dict[str, object]:
    """Preserve the expanded local proposition, never a declaration spelling."""

    out: dict[str, object] = {}
    for field_name in _EXPANDED_LEAN_SURFACE_FIELDS:
        if field_name in item:
            value = item.get(field_name)
            if (
                field_name
                in {
                    "proposition_alias_expansion",
                    "subtype_predicate_proposition_alias_expansion",
                }
                and isinstance(value, Mapping)
            ):
                # A complete transparent alias trace has an independently
                # expanded proposition.  Reuse the differential transport's
                # structural projection so declaration FQNs and source lines
                # never decide equality, while incomplete/unfamiliar traces
                # retain their raw surface and fail closed.
                out[field_name] = _complete_proposition_alias_presentation_projection(
                    value,
                    full_result_surface=False,
                    omit_recursive_structural_coordinates=False,
                )
            else:
                out[field_name] = copy.deepcopy(value)
    if not isinstance(item.get("lean_source_declaration"), str) or not str(
        item.get("lean_source_declaration") or ""
    ).strip():
        raise SourceRecordSemanticRebindError("generated row has no Lean source declaration")
    if "expanded_input_type" in item and not isinstance(item.get("expanded_input_type"), str):
        raise SourceRecordSemanticRebindError("generated row has malformed expanded input type")
    return out


def _generated_taxonomy_core_fields_error(
    item: Mapping[str, Any], *, label: str
) -> str:
    """Validate the closed v1 generated-taxonomy schema before omitting it.

    This validation intentionally does not infer a classification from a Lean
    declaration or a row name.  It only recognizes the complete documented
    generated field set.  A partial set, an unfamiliar value shape, or any
    future field remains part of the ordinary descriptor and therefore fails
    closed across the historical/current comparison.
    """

    present = [field for field in _GENERATED_TAXONOMY_CORE_FIELDS if field in item]
    if not present:
        return ""
    if len(present) != len(_GENERATED_TAXONOMY_CORE_FIELDS):
        return f"{label} has a partial generated-taxonomy field set"
    if item.get("proposition_sort") not in _GENERATED_TAXONOMY_PROPOSITION_SORTS:
        return f"{label} has an invalid generated proposition sort"
    evidence = item.get("proposition_sort_evidence")
    if not isinstance(evidence, str) or not evidence.strip():
        return f"{label} has an invalid generated proposition-sort receipt"
    if item.get("theorem_facing_semantic_role") not in _GENERATED_TAXONOMY_ROLES:
        return f"{label} has an invalid generated theorem-facing role"
    if (
        item.get("semantic_restriction_role")
        not in _GENERATED_TAXONOMY_RESTRICTION_ROLES
    ):
        return f"{label} has an invalid generated semantic-restriction role"
    candidates = item.get("semantic_restriction_candidates")
    if (
        not isinstance(candidates, list)
        or any(not isinstance(value, str) or not value.strip() for value in candidates)
        or candidates != sorted(set(candidates))
    ):
        return f"{label} has an invalid generated semantic-restriction candidate set"
    if not _sha256(item.get("structural_type_sha256")):
        return f"{label} has an invalid generated structural type digest"
    return ""


def _strip_generated_taxonomy_core_fields(
    item: dict[str, Any], *, enabled: bool, label: str
) -> None:
    """Project the closed v1 taxonomy only under the v2 compatibility policy."""

    if not enabled:
        return
    if error := _generated_taxonomy_core_fields_error(item, label=label):
        raise SourceRecordSemanticRebindError(error)
    if any(field in item for field in _GENERATED_TAXONOMY_CORE_FIELDS):
        for field in _GENERATED_TAXONOMY_CORE_FIELDS:
            item.pop(field, None)
        input_value = item.get("input")
        if isinstance(input_value, dict):
            for field in _GENERATED_TAXONOMY_NESTED_INPUT_FIELDS:
                value = input_value.get(field)
                if value is not None and (
                    not isinstance(value, str) or not value.strip()
                ):
                    raise SourceRecordSemanticRebindError(
                        f"{label} has an invalid generated input taxonomy field"
                    )
                input_value.pop(field, None)


def _normalized_generated_item(
    item: Mapping[str, Any],
    *,
    section: str,
    map_items: Mapping[str, Any],
    current: bool,
    generated_taxonomy_core_adapter: bool = True,
    map_items_by_full_digest: Mapping[str, list[Mapping[str, Any]]] | None = None,
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    """Return a finite two-sided item descriptor and current receipt if any."""

    if section == "semantic_model_items":
        # Schema-1 raw audits did not store complete elaborated signature
        # receipts.  Do not manufacture an equivalence for a paper-facing
        # result-level judgment; it remains ordinary current manual work.
        raise SourceRecordSemanticRebindError("semantic-model rows require current review")
    if section == "recursive_field_items":
        # Recursive source-parent receipts have a separate structural policy.
        # This overlay is for legacy input/conclusion sidecars only.
        raise SourceRecordSemanticRebindError("recursive-field rows require current review")
    if section not in {"boundary_input_items", "conclusion_dependency_items"}:
        raise SourceRecordSemanticRebindError(f"unsupported generated section `{section}`")

    current_route = _current_signature_receipt(item, label=section) if current else None
    associations = _association_descriptor(
        item,
        map_items=map_items,
        map_items_by_full_digest=map_items_by_full_digest,
        current=current,
        current_signature=current_route,
        label=section,
    )
    # Let the established differential descriptor normalize presentation
    # routes/binder names.  Associations are handled above because schema 1
    # lacks the schema-2 semantic pin and must not be equated by omission.
    ordinary = copy.deepcopy(dict(item))
    _strip_generated_taxonomy_core_fields(
        ordinary,
        enabled=generated_taxonomy_core_adapter,
        label=section,
    )
    for field_name in _ASSOCIATION_FIELDS:
        ordinary.pop(field_name, None)
    for field_name in _CURRENT_RECEIPT_FIELDS | _LEGACY_RECEIPT_FIELDS:
        ordinary.pop(field_name, None)
    # An absent historical alias receipt can only equal this exact complete
    # no-alias record.  Any alias path or unfamiliar field stays in the
    # differential descriptor, where the existing presentation normalizer
    # retains its route shape and unknown fields.  Do not strip it as a current
    # receipt: an alias can alter the reviewed endpoint despite an unchanged
    # source declaration string.
    alias = item.get("review_alias_expansion")
    if _strict_no_alias_receipt(alias):
        ordinary.pop("review_alias_expansion", None)
    elif not current and alias is None:
        ordinary.pop("review_alias_expansion", None)
    # The shared differential projection knows how to normalize a complete
    # alias route only after it sees a source-content identity.  Schema-1
    # associations predate that identity field, so supply the already
    # authenticated map-derived identities solely for that projection.  The
    # association is then overwritten below with the independently checked
    # role/mode structure; it is never used to select a match by name.
    synthetic_identities = sorted(
        {
            identity["source_item_semantic_sha256"]
            for association in associations
            for identity in association["source_identities"]
        }
    )
    ordinary["source_contract_association"] = {
        "source_item_identities": [
            {"source_semantic_sha256": identity}
            for identity in synthetic_identities
        ]
    }
    differential = source_record_obligation_descriptor(ordinary, section=section)
    # The association-free differential descriptor correctly retains every
    # unknown generated field.  Add the independently validated source route
    # and exact expanded Lean source surface.
    differential["source_item_semantic_identities"] = sorted(
        {
            identity["source_item_semantic_sha256"]
            for association in associations
            for identity in association["source_identities"]
        }
    )
    differential["source_association_roles"] = associations
    differential.pop("source_association_semantic_sha256", None)
    differential.pop("reviewed_elaborated_signature_sha256", None)
    return (
        {
            "section": section,
            "expanded_lean_surface": _expanded_lean_surface(item),
            "semantic_descriptor": differential,
        },
        current_route,
    )


def _group_semantic_descriptor(
    group: Mapping[str, Any],
    *,
    map_items: Mapping[str, Any],
    current: bool,
    generated_taxonomy_core_adapter: bool = True,
    map_items_by_full_digest: Mapping[str, list[Mapping[str, Any]]] | None = None,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    members = group.get("raw_members")
    if not isinstance(members, list) or not members:
        raise SourceRecordSemanticRebindError("generated judgment group has no raw members")
    descriptors: list[dict[str, Any]] = []
    current_receipts: list[dict[str, Any]] = []
    for member in members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            raise SourceRecordSemanticRebindError("generated judgment group has malformed raw members")
        descriptor, receipt = _normalized_generated_item(
            member[1],
            section=member[0],
            map_items=map_items,
            map_items_by_full_digest=map_items_by_full_digest,
            current=current,
            generated_taxonomy_core_adapter=generated_taxonomy_core_adapter,
        )
        descriptors.append(descriptor)
        if receipt is not None:
            current_receipts.append(
                {
                    "member_descriptor_sha256": _canonical_digest(descriptor),
                    "route_receipt": {
                        key: value
                        for key, value in receipt.items()
                        if not key.startswith("_")
                    },
                }
            )
    descriptors.sort(key=_canonical_digest)
    current_receipts.sort(key=_canonical_digest)
    scope = group.get("raw_formalization_scope")
    return (
        {
            "schema": SOURCE_RECORD_SEMANTIC_REBIND_SCHEMA,
            "raw_formalization_scope": copy.deepcopy(scope),
            "members": descriptors,
        },
        current_receipts,
    )


def _groups_by_descriptor(
    raw: Mapping[str, Any],
    *,
    map_items: Mapping[str, Any],
    current: bool,
    generated_taxonomy_core_adapter: bool = True,
    map_items_by_full_digest: Mapping[str, list[Mapping[str, Any]]] | None = None,
) -> tuple[dict[str, dict[str, Any]], dict[str, list[str]], dict[str, str]]:
    groups, group_errors = raw_source_record_obligation_groups(raw)
    if group_errors:
        raise SourceRecordSemanticRebindError(
            "raw audit has malformed generated groups: " + ", ".join(sorted(group_errors)[:5])
        )
    descriptors: dict[str, dict[str, Any]] = {}
    by_digest: dict[str, list[str]] = {}
    excluded: dict[str, str] = {}
    for key, group in groups.items():
        try:
            descriptor, receipts = _group_semantic_descriptor(
                group,
                map_items=map_items,
                map_items_by_full_digest=map_items_by_full_digest,
                current=current,
                generated_taxonomy_core_adapter=generated_taxonomy_core_adapter,
            )
            pins = _current_group_pins(group) if current else []
        except SourceRecordSemanticRebindError as exc:
            excluded[key] = str(exc)
            continue
        digest = _canonical_digest(descriptor)
        descriptors[key] = {
            "descriptor": descriptor,
            "descriptor_sha256": digest,
            "current_route_receipts": receipts,
            "current_item_pins": pins,
            "raw_members": group.get("raw_members"),
        }
        by_digest.setdefault(digest, []).append(key)
    for values in by_digest.values():
        values.sort()
    return descriptors, by_digest, excluded


def _current_group_pins(group: Mapping[str, Any]) -> list[dict[str, Any]]:
    members = group.get("raw_members")
    if not isinstance(members, list):
        raise SourceRecordSemanticRebindError("current group has no raw members for item pins")
    try:
        pins = _current_item_pins(members)
    except Exception as exc:  # noqa: BLE001 - shared helper fails closed.
        raise SourceRecordSemanticRebindError(
            f"current group has malformed reusable-item pins: {exc}"
        ) from exc
    if not pins:
        raise SourceRecordSemanticRebindError("current group has no reusable item pins")
    return pins


def _prior_sidecar_error(
    sidecar: Mapping[str, Any],
    *,
    paper: str,
    prior_raw: Mapping[str, Any],
    prior_groups: Mapping[str, Any],
    validated_historical_composition: bool = False,
) -> str:
    if _payload_is_non_evidence(sidecar):
        return "prior sidecar is explicitly marked non-evidence"
    if sidecar.get("schema") != 1 or sidecar.get("paper") != paper:
        return "prior sidecar has an invalid paper/schema identity"
    if _sha256(sidecar.get("source_record_audit_sha256")) != _sha256(
        prior_raw.get("source_record_audit_sha256")
    ):
        return "prior sidecar is not bound to the archived raw audit"
    composition_transport = {
        field
        for field in _HISTORICAL_COMPOSITION_SIDECAR_TRANSPORT_FIELDS
        if field in sidecar
    }
    if composition_transport and not validated_historical_composition:
        return (
            "prior sidecar carries historical selected-overlay transport without "
            "a validated composition parent"
        )
    items = sidecar.get("items")
    if not isinstance(items, Mapping):
        return "prior sidecar has no items object"
    if set(str(key) for key in items) != set(prior_groups):
        return "prior sidecar does not cover exactly the archived generated ledger"
    prompt = str(sidecar.get("prompt_version") or "").strip()
    for key, response in items.items():
        if not isinstance(response, Mapping):
            return f"prior sidecar response `{key}` is not an object"
        if _payload_is_non_evidence(response):
            return f"prior sidecar response `{key}` is explicitly marked non-evidence"
        prior_transport = {
            field for field in _PRIOR_TRANSPORT_FIELDS if field in response
        }
        composition_response_transport = {
            field
            for field in _HISTORICAL_COMPOSITION_RESPONSE_TRANSPORT_FIELDS
            if field in response
        }
        if prior_transport or (
            composition_response_transport and not validated_historical_composition
        ):
            return f"prior sidecar response `{key}` already carries an overlay transport"
        if str(response.get("prompt_version") or prompt).strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
            return f"prior sidecar response `{key}` does not use v10"
        if _sha256(response.get("source_record_audit_sha256") or sidecar.get("source_record_audit_sha256")) != _sha256(
            prior_raw.get("source_record_audit_sha256")
        ):
            return f"prior sidecar response `{key}` is not bound to the archived raw audit"
        classification = str(
            response.get("classification")
            or response.get("judgment")
            or response.get("verdict")
            or response.get("status")
            or ""
        ).strip()
        validator = response.get("validator") or response.get("model") or sidecar.get("validator") or sidecar.get("model")
        timestamp = response.get("validated_at") or response.get("timestamp") or sidecar.get("validated_at") or sidecar.get("timestamp")
        if not classification or not str(validator or "").strip() or not str(timestamp or "").strip():
            return f"prior sidecar response `{key}` lacks judgment/validator/timestamp"
    return ""


def _prior_attestation_error(
    attestation: Mapping[str, Any],
    *,
    paper: str,
    prior_raw: Mapping[str, Any],
) -> str:
    """Require a whole-ledger historical semantic-review attestation.

    This is intentionally structural.  It does not select a result by an
    attestation name, but prevents an incomplete archived sidecar from being
    transported as though its semantic-model review had been completed.
    """

    if _payload_is_non_evidence(attestation):
        return "prior semantic attestation is explicitly marked non-evidence"
    if (
        attestation.get("schema") != 1
        or attestation.get("artifact_kind")
        != "source_record_current_semantic_revalidation_attestation"
        or attestation.get("paper") != paper
        or str(attestation.get("review_scope") or "").strip()
        != "all_current_generated_judgment_keys"
        or str(attestation.get("scope") or "").strip()
        != "all_current_semantic_model_judgment_groups"
    ):
        return "prior semantic attestation has an invalid paper/schema identity"
    if attestation.get("reviewed_current_semantics") is not True:
        return "prior semantic attestation does not affirm current semantics"
    if _sha256(attestation.get("current_source_record_audit_sha256")) != _sha256(
        prior_raw.get("source_record_audit_sha256")
    ):
        return "prior semantic attestation is not bound to the archived raw audit"
    if _sha256(attestation.get("generated_judgment_keys_sha256")) != generated_judgment_keys_sha256(
        prior_raw
    ) or _sha256(attestation.get("generated_judgment_surface_sha256")) != generated_judgment_surface_sha256(
        prior_raw
    ):
        return "prior semantic attestation does not cover the archived generated ledger"
    if not str(attestation.get("reviewer") or "").strip() or not str(
        attestation.get("validated_at") or ""
    ).strip():
        return "prior semantic attestation lacks reviewer/timestamp"
    return ""


def _effective_prior_attestation(
    *,
    paper: str,
    paper_dir: Path,
    prior_raw_audit: Mapping[str, Any],
    prior_raw_audit_path: Path,
    prior_judgments: Mapping[str, Any],
    prior_judgments_path: Path,
    prior_attestation: Mapping[str, Any] | None,
    prior_attestation_path: Path | None,
    historical_composition_parent: Mapping[str, Any] | None,
    historical_composition_parent_path: Path | None,
) -> tuple[Mapping[str, Any], bool]:
    """Return one accepted full-attestation lane for the archived sidecar.

    The normal lane retains its existing immutable ordinary-attestation input.
    The historical-composition lane is intentionally opt-in and has no
    serialized normal-form surrogate: it first validates the complete parent
    against the archived raw and composed sidecar, then returns only the
    validator's in-memory normal-form projection for the ordinary structural
    attestation check below.
    """

    ordinary_present = prior_attestation is not None or prior_attestation_path is not None
    historical_present = (
        historical_composition_parent is not None
        or historical_composition_parent_path is not None
    )
    if (prior_attestation is None) != (prior_attestation_path is None):
        raise SourceRecordSemanticRebindError(
            "ordinary prior attestation and path must be supplied together"
        )
    if (historical_composition_parent is None) != (
        historical_composition_parent_path is None
    ):
        raise SourceRecordSemanticRebindError(
            "historical composition parent and path must be supplied together"
        )
    if ordinary_present == historical_present:
        raise SourceRecordSemanticRebindError(
            "supply exactly one ordinary prior attestation or historical composition parent"
        )
    if not historical_present:
        assert prior_attestation is not None
        return prior_attestation, False

    assert historical_composition_parent is not None
    assert historical_composition_parent_path is not None
    try:
        from scripts.source_record_historical_composition_attestation import (
            SourceRecordHistoricalCompositionAttestationError,
            validate_historical_composition_attestation,
        )
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        from source_record_historical_composition_attestation import (
            SourceRecordHistoricalCompositionAttestationError,
            validate_historical_composition_attestation,
        )

    try:
        validated = validate_historical_composition_attestation(
            paper=paper,
            paper_dir=paper_dir,
            archived_raw_audit=prior_raw_audit,
            archived_raw_audit_path=prior_raw_audit_path,
            composed_sidecar=prior_judgments,
            composed_sidecar_path=prior_judgments_path,
            parent_attestation=historical_composition_parent,
            parent_attestation_path=historical_composition_parent_path,
        )
    except SourceRecordHistoricalCompositionAttestationError as exc:
        raise SourceRecordSemanticRebindError(
            "historical composition parent validation failed: " + str(exc)
        ) from exc
    return validated.normalized_full_attestation, True


def _artifact_without_integrity(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        str(key): value
        for key, value in payload.items()
        if str(key) != SOURCE_RECORD_SEMANTIC_REBIND_INTEGRITY_FIELD
    }


def source_record_semantic_rebind_sha256(payload: Mapping[str, Any]) -> str:
    return _canonical_digest(_artifact_without_integrity(payload))


def stamp_source_record_semantic_rebind(payload: dict[str, Any]) -> None:
    payload[SOURCE_RECORD_SEMANTIC_REBIND_INTEGRITY_FIELD] = source_record_semantic_rebind_sha256(payload)


def _maps_for_prior(
    *,
    paper: str,
    prior_raw: Mapping[str, Any],
    prior_raw_path: Path,
    current_map: Mapping[str, Any],
    current_map_path: Path,
    paper_dir: Path,
    prior_statement_map: Mapping[str, Any] | None,
    prior_statement_map_path: Path | None,
    prior_association_snapshot_reconciliation_path: Path | None,
) -> tuple[Mapping[str, Any], dict[str, Any]]:
    """Return a validated archived map or the exact-item-only fallback map."""

    prior_map_sha = _sha256(prior_raw.get("paper_statement_map_sha256"))
    if prior_association_snapshot_reconciliation_path is not None:
        if prior_statement_map is not None or prior_statement_map_path is not None:
            raise SourceRecordSemanticRebindError(
                "an archived statement map and association reconciliation are mutually exclusive"
            )
        return _reconciled_prior_map(
            reconciliation_path=prior_association_snapshot_reconciliation_path,
            paper_dir=paper_dir,
            paper=paper,
            prior_raw_path=prior_raw_path,
            prior_raw=prior_raw,
        )
    if prior_statement_map is not None or prior_statement_map_path is not None:
        if not isinstance(prior_statement_map, Mapping) or prior_statement_map_path is None:
            raise SourceRecordSemanticRebindError(
                "prior statement map and its path must be supplied together"
            )
        provenance = _map_provenance(
            prior_statement_map_path,
            paper_dir,
            expected_raw_map_sha=prior_map_sha,
        )
        _map_items(prior_statement_map)
        return prior_statement_map, {"mode": "archived_exact_map", **provenance}

    # The only mapless historical lane is exact per-associated-item equality.
    # `_identity_from_map` enforces that full digest during prior descriptor
    # construction.  A changed individual map record cannot enter this lane.
    _map_items(current_map)
    return current_map, {
        "mode": "all_referenced_map_items_exact_in_current_snapshot",
        "current_statement_map": {
            "path": _relative_paper_path(current_map_path, paper_dir),
            "file_sha256": _file_sha256(current_map_path),
        },
        "archived_raw_paper_statement_map_sha256": prior_map_sha,
    }


def _reconstruct_source_record_semantic_rebind(
    *,
    paper: str,
    paper_dir: Path,
    prior_raw_audit: Mapping[str, Any],
    current_raw_audit: Mapping[str, Any],
    prior_judgments: Mapping[str, Any],
    prior_attestation: Mapping[str, Any] | None = None,
    prior_raw_audit_path: Path,
    current_raw_audit_path: Path,
    prior_judgments_path: Path,
    prior_attestation_path: Path | None = None,
    current_statement_map: Mapping[str, Any],
    current_statement_map_path: Path,
    prior_statement_map: Mapping[str, Any] | None = None,
    prior_statement_map_path: Path | None = None,
    prior_association_snapshot_reconciliation_path: Path | None = None,
    historical_composition_parent: Mapping[str, Any] | None = None,
    historical_composition_parent_path: Path | None = None,
    policy_version: str = SOURCE_RECORD_SEMANTIC_REBIND_POLICY_VERSION,
) -> dict[str, Any]:
    """Reconstruct the retired artifact exactly for reader validation."""

    policy = _semantic_rebind_policy_configuration(policy_version)
    generated_taxonomy_core_adapter = bool(
        policy["generated_taxonomy_core_adapter"]
    )
    if error := _prior_raw_error(prior_raw_audit, paper=paper, label="prior"):
        raise SourceRecordSemanticRebindError(error)
    if error := _current_raw_error(current_raw_audit, paper=paper, label="current"):
        raise SourceRecordSemanticRebindError(error)
    effective_prior_attestation, validated_historical_composition = (
        _effective_prior_attestation(
            paper=paper,
            paper_dir=paper_dir,
            prior_raw_audit=prior_raw_audit,
            prior_raw_audit_path=prior_raw_audit_path,
            prior_judgments=prior_judgments,
            prior_judgments_path=prior_judgments_path,
            prior_attestation=prior_attestation,
            prior_attestation_path=prior_attestation_path,
            historical_composition_parent=historical_composition_parent,
            historical_composition_parent_path=historical_composition_parent_path,
        )
    )
    current_map_sha = _sha256(current_raw_audit.get("paper_statement_map_sha256"))
    current_map_provenance = _map_provenance(
        current_statement_map_path,
        paper_dir,
        expected_raw_map_sha=current_map_sha,
    )
    current_map_items = _map_items(current_statement_map)
    prior_map, prior_map_validation = _maps_for_prior(
        paper=paper,
        prior_raw=prior_raw_audit,
        prior_raw_path=prior_raw_audit_path,
        current_map=current_statement_map,
        current_map_path=current_statement_map_path,
        paper_dir=paper_dir,
        prior_statement_map=prior_statement_map,
        prior_statement_map_path=prior_statement_map_path,
        prior_association_snapshot_reconciliation_path=(
            prior_association_snapshot_reconciliation_path
        ),
    )
    prior_map_items = _map_items(prior_map)
    prior_map_items_by_full_digest = (
        _map_items_by_full_digest(
            prior_map_items,
            label="reconciled archived statement map",
        )
        if prior_map_validation.get("mode")
        == "historical_association_snapshot_reconciliation"
        else None
    )

    prior_descriptors, prior_index, prior_excluded = _groups_by_descriptor(
        prior_raw_audit,
        map_items=prior_map_items,
        map_items_by_full_digest=prior_map_items_by_full_digest,
        current=False,
        generated_taxonomy_core_adapter=generated_taxonomy_core_adapter,
    )
    current_descriptors, current_index, current_excluded = _groups_by_descriptor(
        current_raw_audit,
        map_items=current_map_items,
        current=True,
        generated_taxonomy_core_adapter=generated_taxonomy_core_adapter,
    )
    if error := _prior_sidecar_error(
        prior_judgments,
        paper=paper,
        prior_raw=prior_raw_audit,
        prior_groups={key: value for key, value in raw_source_record_obligation_groups(prior_raw_audit)[0].items()},
        validated_historical_composition=validated_historical_composition,
    ):
        raise SourceRecordSemanticRebindError(error)
    if error := _prior_attestation_error(
        effective_prior_attestation, paper=paper, prior_raw=prior_raw_audit
    ):
        raise SourceRecordSemanticRebindError(error)

    raw_responses = prior_judgments.get("items")
    assert isinstance(raw_responses, Mapping)  # checked above
    items: dict[str, dict[str, Any]] = {}
    decisions: list[dict[str, str]] = []
    all_prior_groups, _ = raw_source_record_obligation_groups(prior_raw_audit)
    all_current_groups, _ = raw_source_record_obligation_groups(current_raw_audit)
    for prior_key in sorted(all_prior_groups):
        prior_entry = prior_descriptors.get(prior_key)
        if prior_entry is None:
            decisions.append(
                {
                    "prior_judgment_key": prior_key,
                    "status": "manual_current_review_required",
                    "reason": prior_excluded.get(prior_key, "archived group has no admissible semantic descriptor"),
                }
            )
            continue
        digest = str(prior_entry["descriptor_sha256"])
        prior_candidates = prior_index.get(digest, [])
        current_candidates = current_index.get(digest, [])
        if len(prior_candidates) != 1 or len(current_candidates) != 1:
            decisions.append(
                {
                    "prior_judgment_key": prior_key,
                    "status": "manual_current_review_required",
                    "reason": "semantic descriptor is not one-to-one across archived and current generated ledgers",
                }
            )
            continue
        current_key = current_candidates[0]
        current_entry = current_descriptors[current_key]
        response = raw_responses.get(prior_key)
        if not isinstance(response, Mapping):
            decisions.append(
                {
                    "prior_judgment_key": prior_key,
                    "status": "not_rebound",
                    "reason": "archived sidecar response is missing",
                }
            )
            continue
        items[current_key] = {
            "schema": SOURCE_RECORD_SEMANTIC_REBIND_SCHEMA,
            "policy_version": policy_version,
            "prior_judgment_key": prior_key,
            "current_judgment_key": current_key,
            "prior_group_descriptor": copy.deepcopy(prior_entry["descriptor"]),
            "prior_group_descriptor_sha256": digest,
            "current_group_descriptor": copy.deepcopy(current_entry["descriptor"]),
            "current_group_descriptor_sha256": str(current_entry["descriptor_sha256"]),
            "current_route_receipts": copy.deepcopy(current_entry["current_route_receipts"]),
            "current_item_pins": copy.deepcopy(current_entry["current_item_pins"]),
            "prior_response_sha256": _canonical_digest(response),
        }
        decisions.append(
            {
                "prior_judgment_key": prior_key,
                "current_judgment_key": current_key,
                "status": "rebound",
                "reason": "one exact name-independent semantic descriptor across archived and current groups",
            }
        )
    for current_key in sorted(all_current_groups):
        if current_key in items:
            continue
        if current_key in current_excluded:
            reason = current_excluded[current_key]
        else:
            reason = "no one-to-one archived semantic descriptor"
        decisions.append(
            {
                "current_judgment_key": current_key,
                "status": "not_rebound",
                "reason": reason,
            }
        )

    payload: dict[str, Any] = {
        "schema": SOURCE_RECORD_SEMANTIC_REBIND_SCHEMA,
        "artifact_kind": SOURCE_RECORD_SEMANTIC_REBIND_ARTIFACT_KIND,
        "policy_version": policy_version,
        "paper": paper,
        "prompt_version": SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_policy_version": SOURCE_RECORD_V10_PROMPT_VERSION,
        "prior_raw_audit": _file_provenance(prior_raw_audit_path, paper_dir, raw=prior_raw_audit),
        "current_raw_audit_snapshot": _file_provenance(
            current_raw_audit_path, paper_dir, raw=current_raw_audit
        ),
        "prior_judgments": _file_provenance(prior_judgments_path, paper_dir),
        "prior_statement_map_validation": prior_map_validation,
        "current_statement_map": current_map_provenance,
        "items": items,
        "decisions": decisions,
    }
    if generated_taxonomy_core_adapter:
        payload[GENERATED_TAXONOMY_CORE_ADAPTER_FIELD] = (
            _generated_taxonomy_core_adapter_receipt()
        )
    if validated_historical_composition:
        assert historical_composition_parent_path is not None
        payload[HISTORICAL_COMPOSITION_PARENT_FIELD] = _file_provenance(
            historical_composition_parent_path, paper_dir
        )
    else:
        assert prior_attestation_path is not None
        payload["prior_semantic_attestation"] = _file_provenance(
            prior_attestation_path, paper_dir
        )
    stamp_source_record_semantic_rebind(payload)
    return payload


def source_record_semantic_rebind_overlay_path(paper_dir: Path) -> Path:
    return paper_dir / "audit" / SOURCE_RECORD_SEMANTIC_REBIND_FILENAME


_DECLARED_BYTE_PINNED_PROVENANCE_DIGEST_FIELDS = (
    "file_sha256",
    "bytes_sha256",
)
_MAX_DECLARED_BYTE_PINNED_PROVENANCE_NODES = 4096
_MAX_DECLARED_BYTE_PINNED_PROVENANCE_PATHS = 256


def source_record_semantic_rebind_declared_provenance_paths(
    payload: object,
    *,
    paper_dir: Path,
) -> tuple[Path, ...]:
    """Return only explicit, paper-local byte-pinned provenance references.

    The traversal is structural rather than name based: a reference qualifies
    only when one mapping carries both a ``path`` and one of the two closed
    byte-digest fields.  Source anchors and arbitrary human review text are
    consequently not discovered as dependencies.  The caller may apply this
    function again to a referenced JSON payload to freeze an entire declared
    provenance graph without recursively scanning the audit directory.
    """

    paths: dict[Path, None] = {}
    visited_nodes = 0

    def visit(value: object, *, label: str) -> None:
        nonlocal visited_nodes
        visited_nodes += 1
        if visited_nodes > _MAX_DECLARED_BYTE_PINNED_PROVENANCE_NODES:
            raise SourceRecordSemanticRebindError(
                "semantic rebind declared provenance graph is too large"
            )
        if isinstance(value, Mapping):
            raw_path = value.get("path")
            digest_fields = [
                field
                for field in _DECLARED_BYTE_PINNED_PROVENANCE_DIGEST_FIELDS
                if field in value
            ]
            if raw_path is not None and digest_fields:
                digests = [_sha256(value.get(field)) for field in digest_fields]
                if not all(digests) or len(set(digests)) != 1:
                    raise SourceRecordSemanticRebindError(
                        f"{label} has a malformed byte-pinned provenance record"
                    )
                path = _resolve_paper_path(
                    raw_path,
                    paper_dir,
                    label=f"{label} provenance path",
                )
                paths[path.resolve()] = None
                if len(paths) > _MAX_DECLARED_BYTE_PINNED_PROVENANCE_PATHS:
                    raise SourceRecordSemanticRebindError(
                        "semantic rebind declared provenance has too many paths"
                    )
            for key, child in value.items():
                visit(child, label=f"{label}.{key}")
            return
        if isinstance(value, list):
            for index, child in enumerate(value):
                visit(child, label=f"{label}[{index}]")

    visit(payload, label="semantic rebind")
    return tuple(sorted(paths, key=lambda path: str(path)))


def _provenance_file(
    value: object, *, paper_dir: Path, label: str, raw: bool = False
) -> tuple[Path | None, dict[str, Any] | None, str]:
    if not isinstance(value, Mapping):
        return None, None, f"{label} provenance is malformed"
    try:
        path = _resolve_paper_path(value.get("path"), paper_dir, label=f"{label} path")
        payload = _read_json_object(path, label=label)
    except SourceRecordSemanticRebindError as exc:
        return None, None, str(exc)
    if _sha256(value.get("file_sha256")) != _file_sha256(path):
        return None, None, f"{label} bytes changed from immutable provenance"
    if raw:
        for field in (
            "source_record_audit_sha256",
            "source_record_audit_integrity_sha256",
            "paper_statement_map_sha256",
        ):
            if _sha256(value.get(field)) != _sha256(payload.get(field)):
                return None, None, f"{label} has a different `{field}`"
    return path, payload, ""


def _map_from_validation(
    validation: object,
    *,
    paper_dir: Path,
    paper: str,
    prior_raw_path: Path,
    prior_raw: Mapping[str, Any],
    current_snapshot_map: Mapping[str, Any],
) -> tuple[Mapping[str, Any] | None, str]:
    if not isinstance(validation, Mapping):
        return None, "prior statement-map validation is malformed"
    mode = str(validation.get("mode") or "").strip()
    if mode == "archived_exact_map":
        try:
            path = _resolve_paper_path(
                validation.get("path"), paper_dir, label="prior statement map path"
            )
            statement_map = _read_json_object(path, label="prior statement map")
        except SourceRecordSemanticRebindError as exc:
            return None, str(exc)
        if _sha256(validation.get("file_sha256")) != _file_sha256(path):
            return None, "prior statement-map bytes changed from immutable provenance"
        if _sha256(validation.get("paper_statement_map_sha256")) != _sha256(
            prior_raw.get("paper_statement_map_sha256")
        ):
            return None, "prior statement-map provenance does not match the archived raw audit"
        return statement_map, ""
    if mode == "historical_association_snapshot_reconciliation":
        provenance = validation.get("reconciliation")
        witness_meta = validation.get("witness_statement_map")
        if not isinstance(provenance, Mapping) or not isinstance(witness_meta, Mapping):
            return None, "historical association reconciliation provenance is malformed"
        try:
            reconciliation_path = _resolve_paper_path(
                provenance.get("path"),
                paper_dir,
                label="historical association reconciliation path",
            )
        except SourceRecordSemanticRebindError as exc:
            return None, str(exc)
        if _sha256(provenance.get("file_sha256")) != _file_sha256(
            reconciliation_path
        ):
            return None, "historical association reconciliation bytes changed"
        try:
            statement_map, replayed = _reconciled_prior_map(
                reconciliation_path=reconciliation_path,
                paper_dir=paper_dir,
                paper=paper,
                prior_raw_path=prior_raw_path,
                prior_raw=prior_raw,
            )
        except SourceRecordSemanticRebindError as exc:
            return None, str(exc)
        if canonical_digest_payload(replayed) != canonical_digest_payload(
            dict(validation)
        ):
            return None, "historical association reconciliation validation does not replay"
        return statement_map, ""
    if mode == "all_referenced_map_items_exact_in_current_snapshot":
        current_meta = validation.get("current_statement_map")
        if not isinstance(current_meta, Mapping):
            return None, "exact-item fallback has no current statement-map provenance"
        try:
            path = _resolve_paper_path(
                current_meta.get("path"), paper_dir, label="fallback current statement map path"
            )
        except SourceRecordSemanticRebindError as exc:
            return None, str(exc)
        if _sha256(current_meta.get("file_sha256")) != _file_sha256(path):
            return None, "exact-item fallback current map bytes changed"
        if canonical_digest_payload(_read_json_object(path, label="fallback current statement map")) != canonical_digest_payload(
            current_snapshot_map
        ):
            return None, "exact-item fallback map does not equal the current raw snapshot map"
        return current_snapshot_map, ""
    return None, "prior statement-map validation has an unsupported mode"


def source_record_semantic_rebind_overlay_error(
    payload: object, *, paper: str, paper_dir: Path
) -> str:
    """Validate that the overlay exactly replays from immutable snapshots."""

    if not isinstance(payload, Mapping):
        return "semantic rebind overlay is not an object"
    try:
        policy = _semantic_rebind_policy_configuration(payload.get("policy_version"))
    except SourceRecordSemanticRebindError as exc:
        return str(exc)
    expected_fields = {
        "schema",
        "artifact_kind",
        "policy_version",
        "paper",
        "prompt_version",
        "source_record_policy_version",
        "prior_raw_audit",
        "current_raw_audit_snapshot",
        "prior_judgments",
        "prior_semantic_attestation",
        HISTORICAL_COMPOSITION_PARENT_FIELD,
        "prior_statement_map_validation",
        "current_statement_map",
        "items",
        "decisions",
        SOURCE_RECORD_SEMANTIC_REBIND_INTEGRITY_FIELD,
    }
    if bool(policy["generated_taxonomy_core_adapter"]):
        expected_fields.add(GENERATED_TAXONOMY_CORE_ADAPTER_FIELD)
    unknown = sorted(str(key) for key in payload if str(key) not in expected_fields)
    if unknown:
        return "semantic rebind overlay has unsupported fields: " + ", ".join(unknown[:5])
    if (
        payload.get("schema") != SOURCE_RECORD_SEMANTIC_REBIND_SCHEMA
        or payload.get("artifact_kind") != SOURCE_RECORD_SEMANTIC_REBIND_ARTIFACT_KIND
        or payload.get("paper") != paper
        or str(payload.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION
        or str(payload.get("source_record_policy_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return "semantic rebind overlay has an invalid identity or policy"
    if bool(policy["generated_taxonomy_core_adapter"]) and canonical_digest_payload(
        payload.get(GENERATED_TAXONOMY_CORE_ADAPTER_FIELD)
    ) != canonical_digest_payload(_generated_taxonomy_core_adapter_receipt()):
        return "semantic rebind overlay has an invalid generated-taxonomy core adapter"
    if _sha256(payload.get(SOURCE_RECORD_SEMANTIC_REBIND_INTEGRITY_FIELD)) != source_record_semantic_rebind_sha256(payload):
        return "semantic rebind overlay integrity digest does not match"
    prior_path, prior_raw, error = _provenance_file(
        payload.get("prior_raw_audit"), paper_dir=paper_dir, label="prior raw audit", raw=True
    )
    if error or prior_path is None or prior_raw is None:
        return error
    current_path, current_raw, error = _provenance_file(
        payload.get("current_raw_audit_snapshot"), paper_dir=paper_dir, label="current raw audit snapshot", raw=True
    )
    if error or current_path is None or current_raw is None:
        return error
    prior_judgments_path, prior_judgments, error = _provenance_file(
        payload.get("prior_judgments"), paper_dir=paper_dir, label="prior judgments"
    )
    if error or prior_judgments_path is None or prior_judgments is None:
        return error
    historical_composition_parent_path: Path | None = None
    historical_composition_parent: Mapping[str, Any] | None = None
    if HISTORICAL_COMPOSITION_PARENT_FIELD in payload:
        if "prior_semantic_attestation" in payload:
            return (
                "semantic rebind overlay supplies both ordinary and historical "
                "composition attestation lanes"
            )
        (
            historical_composition_parent_path,
            historical_composition_parent,
            error,
        ) = _provenance_file(
            payload.get(HISTORICAL_COMPOSITION_PARENT_FIELD),
            paper_dir=paper_dir,
            label="historical composition parent",
        )
        if (
            error
            or historical_composition_parent_path is None
            or historical_composition_parent is None
        ):
            return error
        attestation_path = None
        attestation = None
    else:
        attestation_path, attestation, error = _provenance_file(
            payload.get("prior_semantic_attestation"),
            paper_dir=paper_dir,
            label="prior semantic attestation",
        )
        if error or attestation_path is None or attestation is None:
            return error
    current_map_meta = payload.get("current_statement_map")
    if not isinstance(current_map_meta, Mapping):
        return "semantic rebind overlay current statement-map provenance is malformed"
    try:
        current_map_path = _resolve_paper_path(
            current_map_meta.get("path"), paper_dir, label="current statement map path"
        )
        current_map = _read_json_object(current_map_path, label="current statement map")
    except SourceRecordSemanticRebindError as exc:
        return str(exc)
    if _sha256(current_map_meta.get("file_sha256")) != _file_sha256(current_map_path):
        return "semantic rebind overlay current statement-map bytes changed"
    if _sha256(current_map_meta.get("paper_statement_map_sha256")) != _sha256(
        current_raw.get("paper_statement_map_sha256")
    ):
        return "semantic rebind overlay current statement-map provenance is stale"
    prior_map, error = _map_from_validation(
        payload.get("prior_statement_map_validation"),
        paper_dir=paper_dir,
        paper=paper,
        prior_raw_path=prior_path,
        prior_raw=prior_raw,
        current_snapshot_map=current_map,
    )
    if error or prior_map is None:
        return error
    try:
        rebuilt = _reconstruct_source_record_semantic_rebind(
            paper=paper,
            paper_dir=paper_dir,
            prior_raw_audit=prior_raw,
            current_raw_audit=current_raw,
            prior_judgments=prior_judgments,
            prior_attestation=attestation,
            prior_raw_audit_path=prior_path,
            current_raw_audit_path=current_path,
            prior_judgments_path=prior_judgments_path,
            prior_attestation_path=attestation_path,
            current_statement_map=current_map,
            current_statement_map_path=current_map_path,
            prior_statement_map=(
                prior_map
                if str(payload.get("prior_statement_map_validation", {}).get("mode") or "")
                == "archived_exact_map"
                else None
            ),
            prior_statement_map_path=(
                _resolve_paper_path(
                    payload["prior_statement_map_validation"].get("path"),
                    paper_dir,
                    label="prior statement map path",
                )
                if str(payload.get("prior_statement_map_validation", {}).get("mode") or "")
                == "archived_exact_map"
                else None
            ),
            prior_association_snapshot_reconciliation_path=(
                _resolve_paper_path(
                    payload["prior_statement_map_validation"]
                    .get("reconciliation", {})
                    .get("path"),
                    paper_dir,
                    label="historical association reconciliation path",
                )
                if str(payload.get("prior_statement_map_validation", {}).get("mode") or "")
                == "historical_association_snapshot_reconciliation"
                else None
            ),
            historical_composition_parent=historical_composition_parent,
            historical_composition_parent_path=historical_composition_parent_path,
            policy_version=str(policy["policy_version"]),
        )
    except (SourceRecordSemanticRebindError, KeyError) as exc:
        return f"semantic rebind overlay replay failed: {exc}"
    if canonical_digest_payload(rebuilt) != canonical_digest_payload(payload):
        return "semantic rebind overlay does not replay from immutable snapshots"
    return ""


def _live_raw_identity_error(
    current_raw_audit: Mapping[str, Any], *, paper_dir: Path
) -> str:
    """Call the folder-aware gate lazily to avoid the evidence-loader cycle."""

    try:
        from scripts.audit_evidence_integrity import (
            current_paper_statement_map_sha256,
            source_record_audit_identity_error,
        )
    except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
        from audit_evidence_integrity import (
            current_paper_statement_map_sha256,
            source_record_audit_identity_error,
        )
    return source_record_audit_identity_error(
        dict(current_raw_audit),
        expected_paper_statement_map_sha256=current_paper_statement_map_sha256(paper_dir),
        folder=paper_dir,
    )


def _source_record_identity_context_error(
    context: object,
    *,
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
) -> str:
    """Validate the neutral evidence-owned context without importing eagerly."""

    try:
        from scripts.audit_evidence_integrity import (
            current_source_record_identity_context_error,
        )
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        from audit_evidence_integrity import (
            current_source_record_identity_context_error,
        )
    return current_source_record_identity_context_error(
        context,
        paper_dir=paper_dir,
        paper=paper,
        current_raw_audit=current_raw_audit,
    )


def prepare_current_source_record_semantic_rebind_identity_context(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    source_record_identity_context: object | None = None,
) -> object | None:
    """Verify one live raw identity for a single in-memory overlay invocation.

    The returned private capability is deliberately process-local.  It binds
    the exact raw object content, aggregate receipt, statement-map receipt,
    paper, and folder that just passed the folder-aware evidence gate.  It is
    not a serialized authority and callers must recreate it for every
    invocation.
    """

    if _current_raw_error(current_raw_audit, paper=paper, label="live current"):
        return None
    if _canonical_live_raw_error(current_raw_audit, paper_dir=paper_dir):
        return None
    if source_record_identity_context is not None:
        if _source_record_identity_context_error(
            source_record_identity_context,
            paper_dir=paper_dir,
            paper=paper,
            current_raw_audit=current_raw_audit,
        ):
            return None
    else:
        identity_error = _live_raw_identity_error(
            current_raw_audit, paper_dir=paper_dir
        )
        if identity_error:
            if _identity_revalidation_is_deferred(identity_error):
                raise SourceRecordSemanticRebindIdentityDeferred(identity_error)
            return None
    raw_digest = _sha256(current_raw_audit.get("source_record_audit_sha256"))
    map_digest = _sha256(current_raw_audit.get("paper_statement_map_sha256"))
    if not raw_digest or not map_digest:  # Defensive: established by the raw gate.
        return None
    try:
        resolved_paper_dir = paper_dir.resolve()
    except (OSError, RuntimeError):
        return None
    return _CurrentSemanticRebindIdentityContext(
        paper_dir=resolved_paper_dir,
        paper=paper,
        current_source_record_audit_sha256=raw_digest,
        current_raw_canonical_sha256=_canonical_digest(current_raw_audit),
        paper_statement_map_sha256=map_digest,
        _token=_CURRENT_IDENTITY_CONTEXT_SENTINEL,
    )


def _current_semantic_rebind_identity_context_error(
    context: object,
    *,
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
) -> str:
    """Reject a context unless it is exactly the just-verified live identity."""

    if not isinstance(context, _CurrentSemanticRebindIdentityContext):
        return "semantic rebind loader did not receive a private identity context"
    if context._token is not _CURRENT_IDENTITY_CONTEXT_SENTINEL:
        return "semantic rebind loader identity context lacks verifier authority"
    try:
        resolved_paper_dir = paper_dir.resolve()
    except (OSError, RuntimeError):
        return "semantic rebind loader paper directory cannot be resolved"
    if context.paper_dir != resolved_paper_dir or context.paper != paper:
        return "semantic rebind loader identity context belongs to another paper"
    if (
        context.current_source_record_audit_sha256
        != _sha256(current_raw_audit.get("source_record_audit_sha256"))
        or context.paper_statement_map_sha256
        != _sha256(current_raw_audit.get("paper_statement_map_sha256"))
        or context.current_raw_canonical_sha256 != _canonical_digest(current_raw_audit)
    ):
        return "semantic rebind loader identity context is stale for the current raw audit"
    return ""


def _response_from_prior(
    response: Mapping[str, Any],
    *,
    prior_sidecar: Mapping[str, Any],
    current_raw_digest: str,
    current_pins: list[dict[str, Any]],
    item_metadata: Mapping[str, Any],
    current_members: object,
    current_key: str,
    statement_map: Mapping[str, Any],
) -> dict[str, Any] | None:
    copied = copy.deepcopy(dict(response))
    # The v10 sidecar schema permits review protocol metadata at either the
    # response or ledger level. The builder validates that effective metadata;
    # materialization must preserve the same effective values so downstream
    # consumers do not reject an authenticated response merely because its
    # reviewer/timestamp were factored out of each item.
    if not str(copied.get("prompt_version") or "").strip():
        copied["prompt_version"] = prior_sidecar.get("prompt_version")
    if not any(
        str(copied.get(field) or "").strip()
        for field in ("validator", "model", "judge", "agent", "generator")
    ):
        copied["validator"] = (
            prior_sidecar.get("validator")
            or prior_sidecar.get("model")
            or prior_sidecar.get("judge")
        )
    if not any(
        str(copied.get(field) or "").strip()
        for field in ("validated_at", "timestamp", "generated_at")
    ):
        copied["validated_at"] = (
            prior_sidecar.get("validated_at")
            or prior_sidecar.get("timestamp")
            or prior_sidecar.get("generated_at")
        )
    # The composed selected/overlay markers authenticated the archived
    # response through the special parent.  They are not current response
    # credentials; preserve their evidence in the immutable replay inputs and
    # replace them with this transport's own item marker below.
    for field_name in (
        _REBOUND_RESPONSE_FIELDS
        | _HISTORICAL_COMPOSITION_RESPONSE_TRANSPORT_FIELDS
    ):
        copied.pop(field_name, None)
    copied["source_record_audit_sha256"] = current_raw_digest
    copied["source_record_item_digest_schema"] = SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    copied["source_record_item_sha256s"] = copy.deepcopy(current_pins)
    copied["source_record_item_sha256"] = (
        str(current_pins[0].get("source_record_item_sha256") or "") if current_pins else ""
    )
    # Do not copy a prior source association or corrected-target choice.  The
    # target-disposition projection reconstructs both from exact live members.
    projected, error = project_source_record_response_association_pins(
        current_members,
        copied,
        judgment_key=current_key,
        statement_map=statement_map,
    )
    if error or projected is None:
        return None
    projected[SOURCE_RECORD_SEMANTIC_REBIND_ITEM_FIELD] = copy.deepcopy(dict(item_metadata))
    return projected


def load_current_source_record_semantic_rebind_items(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    path: Path | None = None,
    identity_context: object | None = None,
    source_record_identity_context: object | None = None,
) -> dict[str, dict[str, Any]]:
    """Return only loader-authenticated prior responses for live current groups.

    ``identity_context`` retains the schema-2-local compatibility capability.
    ``source_record_identity_context`` is the neutral evidence-owned
    capability shared across current overlay lanes.  Both are in-memory only;
    a caller may not combine them to skip either validation path.
    """

    overlay_path = path or source_record_semantic_rebind_overlay_path(paper_dir)
    try:
        payload = json.loads(overlay_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if source_record_semantic_rebind_overlay_error(payload, paper=paper, paper_dir=paper_dir):
        return {}
    try:
        policy = _semantic_rebind_policy_configuration(payload.get("policy_version"))
    except SourceRecordSemanticRebindError:
        return {}
    generated_taxonomy_core_adapter = bool(policy["generated_taxonomy_core_adapter"])
    if identity_context is not None and source_record_identity_context is not None:
        return {}
    if source_record_identity_context is not None:
        if _current_raw_error(current_raw_audit, paper=paper, label="live current"):
            return {}
        if _canonical_live_raw_error(current_raw_audit, paper_dir=paper_dir):
            return {}
        if _source_record_identity_context_error(
            source_record_identity_context,
            paper_dir=paper_dir,
            paper=paper,
            current_raw_audit=current_raw_audit,
        ):
            return {}
    elif identity_context is None:
        if _current_raw_error(current_raw_audit, paper=paper, label="live current"):
            return {}
        if _canonical_live_raw_error(current_raw_audit, paper_dir=paper_dir):
            return {}
        identity_error = _live_raw_identity_error(
            current_raw_audit, paper_dir=paper_dir
        )
        if identity_error:
            if _identity_revalidation_is_deferred(identity_error):
                raise SourceRecordSemanticRebindIdentityDeferred(identity_error)
            return {}
    elif _current_semantic_rebind_identity_context_error(
        identity_context,
        paper_dir=paper_dir,
        paper=paper,
        current_raw_audit=current_raw_audit,
    ):
        return {}
    try:
        prior_path = _resolve_paper_path(
            payload["prior_raw_audit"].get("path"), paper_dir, label="prior raw audit path"
        )
        snapshot_path = _resolve_paper_path(
            payload["current_raw_audit_snapshot"].get("path"),
            paper_dir,
            label="current raw audit snapshot path",
        )
        sidecar_path = _resolve_paper_path(
            payload["prior_judgments"].get("path"), paper_dir, label="prior judgments path"
        )
        current_map_path = paper_dir / "audit" / "paper_statement_map.json"
        prior_raw = _read_json_object(prior_path, label="prior raw audit")
        _read_json_object(snapshot_path, label="current raw audit snapshot")
        prior_judgments = _read_json_object(sidecar_path, label="prior judgments")
        live_map = _read_json_object(current_map_path, label="live current statement map")
        snapshot_map_path = _resolve_paper_path(
            payload["current_statement_map"].get("path"),
            paper_dir,
            label="current snapshot statement map path",
        )
        snapshot_map = _read_json_object(snapshot_map_path, label="current snapshot statement map")
        prior_map, error = _map_from_validation(
            payload.get("prior_statement_map_validation"),
            paper_dir=paper_dir,
            paper=paper,
            prior_raw_path=prior_path,
            prior_raw=prior_raw,
            current_snapshot_map=snapshot_map,
        )
        if error or prior_map is None:
            return {}
        if _sha256(current_raw_audit.get("paper_statement_map_sha256")) != _file_sha256(
            current_map_path
        ):
            return {}
        prior_descriptors, prior_index, _prior_excluded = _groups_by_descriptor(
            prior_raw,
            map_items=_map_items(prior_map),
            map_items_by_full_digest=(
                _map_items_by_full_digest(
                    _map_items(prior_map),
                    label="reconciled archived statement map",
                )
                if str(
                    payload.get("prior_statement_map_validation", {}).get("mode")
                    or ""
                )
                == "historical_association_snapshot_reconciliation"
                else None
            ),
            current=False,
            generated_taxonomy_core_adapter=generated_taxonomy_core_adapter,
        )
        live_descriptors, live_index, _live_excluded = _groups_by_descriptor(
            current_raw_audit,
            map_items=_map_items(live_map),
            current=True,
            generated_taxonomy_core_adapter=generated_taxonomy_core_adapter,
        )
    except (SourceRecordSemanticRebindError, KeyError):
        return {}
    raw_items = payload.get("items")
    prior_responses = prior_judgments.get("items")
    if not isinstance(raw_items, Mapping) or not isinstance(prior_responses, Mapping):
        return {}
    current_digest = _sha256(current_raw_audit.get("source_record_audit_sha256"))
    out: dict[str, dict[str, Any]] = {}
    for storage_key, raw_metadata in raw_items.items():
        if not isinstance(raw_metadata, Mapping):
            continue
        if (
            raw_metadata.get("schema") != SOURCE_RECORD_SEMANTIC_REBIND_SCHEMA
            or raw_metadata.get("policy_version") != policy["policy_version"]
        ):
            continue
        prior_key = str(raw_metadata.get("prior_judgment_key") or "").strip()
        stored_current_key = str(raw_metadata.get("current_judgment_key") or "").strip()
        prior_descriptor = raw_metadata.get("prior_group_descriptor")
        current_descriptor = raw_metadata.get("current_group_descriptor")
        digest = _sha256(raw_metadata.get("prior_group_descriptor_sha256"))
        if (
            not prior_key
            or not stored_current_key
            or not isinstance(prior_descriptor, Mapping)
            or not isinstance(current_descriptor, Mapping)
            or not digest
            or _canonical_digest(prior_descriptor) != digest
            or _sha256(raw_metadata.get("current_group_descriptor_sha256")) != digest
            or canonical_digest_payload(prior_descriptor)
            != canonical_digest_payload(current_descriptor)
        ):
            continue
        # Addresses are checked only after the semantic class is unique.  A
        # live generated key may change; it is never used to choose a match.
        if prior_index.get(digest) != [prior_key]:
            continue
        live_keys = live_index.get(digest, [])
        if len(live_keys) != 1:
            continue
        current_key = live_keys[0]
        prior_entry = prior_descriptors.get(prior_key)
        current_entry = live_descriptors.get(current_key)
        response = prior_responses.get(prior_key)
        if (
            prior_entry is None
            or current_entry is None
            or not isinstance(response, Mapping)
            or _canonical_digest(response) != _sha256(raw_metadata.get("prior_response_sha256"))
            or canonical_digest_payload(prior_entry["descriptor"])
            != canonical_digest_payload(prior_descriptor)
            or canonical_digest_payload(current_entry["descriptor"])
            != canonical_digest_payload(current_descriptor)
        ):
            continue
        members = current_entry.get("raw_members")
        pins = current_entry.get("current_item_pins")
        if not isinstance(pins, list):
            continue
        live_metadata = {
            **copy.deepcopy(dict(raw_metadata)),
            "current_judgment_key": current_key,
            "live_current_group_descriptor": copy.deepcopy(current_entry["descriptor"]),
            "live_current_group_descriptor_sha256": _canonical_digest(
                current_entry["descriptor"]
            ),
            "live_current_route_receipts": copy.deepcopy(
                current_entry["current_route_receipts"]
            ),
            "live_current_item_pins": copy.deepcopy(pins),
        }
        materialized = _response_from_prior(
            response,
            prior_sidecar=prior_judgments,
            current_raw_digest=current_digest,
            current_pins=pins,
            item_metadata=live_metadata,
            current_members=members,
            current_key=current_key,
            statement_map=live_map,
        )
        if materialized is not None:
            out[current_key] = _LoadedSourceRecordSemanticRebindItem(materialized)
    return out


def is_loaded_source_record_semantic_rebind_item(value: object) -> bool:
    return bool(
        isinstance(value, _LoadedSourceRecordSemanticRebindItem)
        and value._source_record_semantic_rebind_loader_token is _LOADED_OVERLAY_ITEM_SENTINEL
        and isinstance(value.get(SOURCE_RECORD_SEMANTIC_REBIND_ITEM_FIELD), Mapping)
    )


def source_record_semantic_rebind_item_has_provenance(value: object) -> bool:
    return bool(
        isinstance(value, Mapping)
        and isinstance(value.get(SOURCE_RECORD_SEMANTIC_REBIND_ITEM_FIELD), Mapping)
    )


def copy_loaded_source_record_semantic_rebind_item(
    value: Mapping[str, Any], updates: Mapping[str, Any] | None = None
) -> dict[str, Any]:
    copied: dict[str, Any] = dict(value)
    if updates:
        copied.update(updates)
    if is_loaded_source_record_semantic_rebind_item(value):
        return _LoadedSourceRecordSemanticRebindItem(copied)
    return copied
