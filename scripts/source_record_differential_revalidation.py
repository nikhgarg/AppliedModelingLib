#!/usr/bin/env python3
"""Authenticate historical differential source-record overlays.

An aggregate source-record receipt changes whenever any reviewed Lean/source
surface changes. Historical papers may retain a strict differential overlay
issued by the retired writer:

* a prior v10 raw receipt and its current judgment sidecar are archived;
* every prior/current generated judgment group is compared through a complete
  semantic descriptor with narrowly normalized presentation fields; and
* only unique, descriptor-identical groups are made current through the
  loader-authenticated overlay.  Everything else remains absent and therefore
  requires a fresh manual response in the ordinary sidecar.

This live module is a reader only. New graph-native closeouts reuse current
content-addressed judgment leaves and never issue this historical transport.

The matching relation deliberately does not use a source-map key, declaration
name, binder name, or sidecar storage key.  Keys are retained only to locate a
saved response and to expose the uniquely matched current generated group.
Input/field judgments use their local source antecedent and structural surface;
they do not become stale merely because an enclosing theorem result changes.
Semantic-model judgments, which audit the advertised result itself, retain the
full expanded result surface and consequently require review after that change.
"""

from __future__ import annotations

import copy
import hashlib
import json
import sys
from pathlib import Path, PurePosixPath
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in focused tests.
    from scripts import source_record_obligation_groups as OBLIGATIONS
    from scripts.source_record_integrity import (
        LEGACY_SOURCE_RECORD_AUDIT_SURFACE_SCHEMA,
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        SOURCE_RECORD_AUDIT_SURFACE_GENERATOR_SHA256_FIELD,
        SOURCE_RECORD_AUDIT_SURFACE_RAW_SHA256_FIELD,
        SOURCE_RECORD_AUDIT_SURFACE_SCHEMA,
        SOURCE_RECORD_AUDIT_SURFACE_SCHEMA_FIELD,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_audit_surface_view,
        source_record_item_is_nonreusable_theorem_facing_mirror,
        source_record_raw_reusable_item_metadata_error,
        source_record_target_route_error,
    )
    from scripts.source_record_archived_source_status_projection_bridge import (
        ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_INTEGRITY_FIELD,
        ValidatedArchivedSourceStatusProjectionBridge,
        archived_source_status_association_is_rebound,
        load_archived_source_status_projection_bridge_context,
        normalized_archived_source_status_association,
        rebound_archived_source_status_response,
    )
    from scripts.source_record_target_disposition import (
        INPUT_SOURCE_CREDIT_CLASSIFICATIONS,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE,
        SOURCE_TARGET_DISPOSITIONS,
        SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
        SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD,
        SOURCE_CLAIM_ATOM_ROUTE_ORIGIN,
        SOURCE_CLAIM_ATOM_ROUTE_ROLE,
        ValidatedAdministrativeProjectionRebind,
        administrative_projection_rebound_association,
        administrative_projection_rebound_response,
        load_administrative_projection_rebind_context,
        recursive_field_parent_route_record_digest,
        semantic_association_record_digest,
        statement_source_component_effective_semantic_pin,
        statement_source_review_effective_semantic_pin,
    )
    from scripts.source_record_overlay_protocol import (
        SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_FILENAME,
        SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD,
    )
    from scripts.source_record_obligation_groups import (
        SOURCE_RECORD_V10_PROMPT_VERSION,
        SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        PRESENTATION_NORMALIZER_SCHEMA,
        _NAVIGATION_FIELDS,
        _RECEIPT_ONLY_FIELDS,
        _ASSOCIATION_FIELDS,
        _ASSOCIATION_NAME_FIELDS,
        _DIRECT_SOURCE_DOMAIN_PARENT_CONTRACT_SCHEMA,
        _DIRECT_SOURCE_DOMAIN_PARENT_CONTRACTS_FIELD,
        _SHA256_RE,
        _canonical_digest,
        _sha256,
        _raw_audit_error,
        _canonical_projection_sort_key,
        _complete_review_alias_presentation_projection,
        _complete_proposition_alias_presentation_projection,
        _complete_terminal_dependency_presentation_projection,
        _semantic_projection,
        _association_mappings,
        _source_semantic_identities,
        _association_semantic_digests,
        _association_role_projection,
        _association_roles,
        _signature_digests,
        _recursive_field_parent_route_semantic_scope,
        _optional_source_domain_fingerprint,
        _direct_source_domain_record_input_projection,
        _recursive_field_direct_source_domain_parent_contract,
        _recursive_field_direct_source_domain_parent_contracts,
        _raw_formalization_scope_descriptor,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    import source_record_obligation_groups as OBLIGATIONS
    from source_record_integrity import (
        LEGACY_SOURCE_RECORD_AUDIT_SURFACE_SCHEMA,
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        SOURCE_RECORD_AUDIT_SURFACE_GENERATOR_SHA256_FIELD,
        SOURCE_RECORD_AUDIT_SURFACE_RAW_SHA256_FIELD,
        SOURCE_RECORD_AUDIT_SURFACE_SCHEMA,
        SOURCE_RECORD_AUDIT_SURFACE_SCHEMA_FIELD,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_audit_surface_view,
        source_record_item_is_nonreusable_theorem_facing_mirror,
        source_record_raw_reusable_item_metadata_error,
        source_record_target_route_error,
    )
    from source_record_archived_source_status_projection_bridge import (
        ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_INTEGRITY_FIELD,
        ValidatedArchivedSourceStatusProjectionBridge,
        archived_source_status_association_is_rebound,
        load_archived_source_status_projection_bridge_context,
        normalized_archived_source_status_association,
        rebound_archived_source_status_response,
    )
    from source_record_target_disposition import (
        INPUT_SOURCE_CREDIT_CLASSIFICATIONS,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE,
        SOURCE_TARGET_DISPOSITIONS,
        SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
        SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD,
        SOURCE_CLAIM_ATOM_ROUTE_ORIGIN,
        SOURCE_CLAIM_ATOM_ROUTE_ROLE,
        ValidatedAdministrativeProjectionRebind,
        administrative_projection_rebound_association,
        administrative_projection_rebound_response,
        load_administrative_projection_rebind_context,
        recursive_field_parent_route_record_digest,
        semantic_association_record_digest,
        statement_source_component_effective_semantic_pin,
        statement_source_review_effective_semantic_pin,
    )
    from source_record_overlay_protocol import (
        SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_FILENAME,
        SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD,
    )
    from source_record_obligation_groups import (
        SOURCE_RECORD_V10_PROMPT_VERSION,
        SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        PRESENTATION_NORMALIZER_SCHEMA,
        _NAVIGATION_FIELDS,
        _RECEIPT_ONLY_FIELDS,
        _ASSOCIATION_FIELDS,
        _ASSOCIATION_NAME_FIELDS,
        _DIRECT_SOURCE_DOMAIN_PARENT_CONTRACT_SCHEMA,
        _DIRECT_SOURCE_DOMAIN_PARENT_CONTRACTS_FIELD,
        _SHA256_RE,
        _canonical_digest,
        _sha256,
        _raw_audit_error,
        _canonical_projection_sort_key,
        _complete_review_alias_presentation_projection,
        _complete_proposition_alias_presentation_projection,
        _complete_terminal_dependency_presentation_projection,
        _semantic_projection,
        _association_mappings,
        _source_semantic_identities,
        _association_semantic_digests,
        _association_role_projection,
        _association_roles,
        _signature_digests,
        _recursive_field_parent_route_semantic_scope,
        _optional_source_domain_fingerprint,
        _direct_source_domain_record_input_projection,
        _recursive_field_direct_source_domain_parent_contract,
        _recursive_field_direct_source_domain_parent_contracts,
        _raw_formalization_scope_descriptor,
    )




SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_SCHEMA = 1


def _current_revalidation_module() -> Any:
    """Load the optional current-revalidation validator only when needed.

    Evidence integrity loads the differential overlay during module import,
    while the current-revalidation tool imports that evidence gate to validate
    its source anchors.  Importing both eagerly makes correctness depend on
    Python's module import order.  The complete-reissue path is the only
    consumer of the current-revalidation validator, so defer that dependency
    until a caller actually requests a complete reissue.
    """

    try:
        from scripts import source_record_current_revalidation as current
    except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
        import source_record_current_revalidation as current
    return current


SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_POLICY_VERSION = (
    "source-record-v10-differential-semantic-overlay-v2"
)
SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ARTIFACT_KIND = (
    "source_record_v10_differential_revalidation"
)
SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_INTEGRITY_FIELD = (
    "source_record_differential_revalidation_sha256"
)
SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_HISTORY_FIELD = (
    "prior_source_record_differential_revalidations"
)
SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD = (
    "complete_reusable_section_identity"
)
SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_SCHEMA = 1
SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_MODE = (
    "all_reusable_sections_and_semantic_descriptors_exact"
)
SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_FIELD = (
    "complete_reissue_raw_group_identity"
)
SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_SCHEMA = 1
SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_FIELD = (
    "prior_attested_current_revalidation"
)
SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_SCHEMA = 1
SOURCE_RECORD_COMPLETE_REISSUE_AGGREGATE_DELTA_SCHEMA = 1
SOURCE_RECORD_COMPLETE_REISSUE_AGGREGATE_DELTA_POLICY = (
    "only-generated-receipt-fields-and-replicated-selected-semantic-projection-v1"
)
# A receipt reissue may regenerate its own aggregate receipts.  The only
# non-generated field allowed to differ is the selected semantic-projection
# receipt emitted by the aggregate-only receipt reprojector.  It occurs once
# in the raw payload and twice in independently checked projections.  Keep the
# paths explicit: an unknown aggregate/provenance delta must force a review.
_COMPLETE_REISSUE_GENERATED_RECEIPT_PATHS = (
    ("source_record_audit_sha256",),
    ("source_record_audit_integrity_sha256",),
)
_COMPLETE_REISSUE_COMPACT_GENERATED_RECEIPT_PATHS = (
    (
        "source_record_audit_surface",
        SOURCE_RECORD_AUDIT_SURFACE_GENERATOR_SHA256_FIELD,
    ),
    (
        "source_record_audit_surface",
        SOURCE_RECORD_AUDIT_SURFACE_RAW_SHA256_FIELD,
    ),
)
_COMPLETE_REISSUE_SELECTED_PROJECTION_TAIL = (
    "source_record_receipt_reprojection",
    "paper_statement_map_exact_default_mode_delta",
    "selected_semantic_projection_sha256",
)
_COMPLETE_REISSUE_SELECTED_PROJECTION_PATHS = (
    _COMPLETE_REISSUE_SELECTED_PROJECTION_TAIL,
    (
        "source_record_audit_surface",
        *_COMPLETE_REISSUE_SELECTED_PROJECTION_TAIL,
    ),
    (
        "source_record_audit_surface",
        "raw_evidence_projection",
        *_COMPLETE_REISSUE_SELECTED_PROJECTION_TAIL,
    ),
)
SEMANTIC_ASSOCIATION_REBIND_FIELD = "semantic_association_rebind"
SEMANTIC_ASSOCIATION_REBIND_SCHEMA = 1
ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD = (
    "archived_source_status_projection_bridge"
)
ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_FIELD = (
    "archived_source_status_projection_normalized_prior_group_semantic_descriptor"
)
ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_SHA256_FIELD = (
    "archived_source_status_projection_normalized_prior_group_semantic_descriptor_sha256"
)
SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD = (
    "source_free_recursive_structural_identity"
)
SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_SCHEMA = 1
SOURCE_FREE_RECURSIVE_CONTENT_IDENTITY_SCHEMA = 1
SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_SCHEMA = 1
SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_POLICY_VERSION = (
    "source-record-v10-differential-semantic-descriptor-reuse-exclusions-v1"
)
SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_ARTIFACT_KIND = (
    "source_record_v10_differential_semantic_descriptor_reuse_exclusions"
)
SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_FIELD = (
    "semantic_descriptor_reuse_exclusions"
)
SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD = (
    "excluded_current_group_semantic_descriptor_reasons"
)

_LOADED_OVERLAY_ITEM_SENTINEL = object()

# Recursive raw fields can be exact semantic matches even when they are only
# data, a derived component, or an unresolved boundary.  Those responses do
# not assert source credit and so do not need a separate source-parent route
# merely to retain their exact reviewed disposition.  This is deliberately an
# allowlist: a new response classification is source-credit-sensitive until
# the audit policy explicitly says otherwise.
_NON_SOURCE_CREDIT_RECURSIVE_CLASSIFICATIONS = frozenset(
    {
        "approved_external_boundary",
        "container_recursively_audited",
        "derived_consequence_record",
        "derived_from_visible_boundary",
        "nonpropositional_witness_data",
        "proved_from_primitives",
        "unresolved_assumed_math",
        "visible_boundary_component",
    }
)
# A classification is not the only way a response can claim source credit.
# Keep the content-bearing response fields explicit; arbitrary new fields
# remain fail-closed through the classification allowlist above rather than
# being inferred from a source-looking spelling or a function name.
_RECURSIVE_SOURCE_CREDIT_RESPONSE_FIELDS = frozenset(
    {
        "corrected_target_sha256_by_source_item",
        "corrected_target_sha256_by_source_semantic_sha256",
        "governing_source_defect_ids",
        "model_convention_ids",
        "model_convention_sha256_by_id",
        "source_target_disposition",
        "source_target_disposition_sha256",
        "source_target_match_verdict",
    }
)
# These are the generated response credentials that can bind a human response
# to a source association even when its classification spelling has not yet
# been added to the source-credit classification set.  A bare ``source_location``
# on a non-source-credit recursive response is deliberately *not* listed: it is
# a human-facing audit annotation and cannot discharge a theorem premise (the
# shared target-disposition validator only treats it as source credit together
# with a source-credit classification/association).  The fields below instead
# carry a machine-checkable source/map/convention/corrected-target claim.
_RECURSIVE_SOURCE_CREDIT_PIN_FIELDS = frozenset(
    {
        "semantic_association_sha256",
        "source_contract_association_sha256",
        "source_map_item_sha256_by_key",
        "source_map_item_keys_sha256",
        "source_target_disposition",
        "source_target_disposition_sha256",
        "source_target_match_verdict",
        "model_convention_ids",
        "model_convention_sha256_by_id",
        "governing_defect_ids",
        "governing_source_defect_ids",
        "corrected_target_sha256_by_source_item",
        "corrected_target_sha256_by_source_semantic_sha256",
        "source_item_semantic_sha256",
        "source_item_semantic_sha256_by_key",
        "source_key",
        "paper_statement_key",
    }
)


class SourceRecordDifferentialRevalidationError(ValueError):
    """Raised when a proposed v10 differential overlay is inadmissible."""


class _LoadedSourceRecordDifferentialRevalidationItem(dict[str, Any]):
    """A JSON-invisible token proving that this item passed the loader."""

    __slots__ = ("_source_record_differential_revalidation_loader_token",)

    def __init__(self, value: Mapping[str, Any]) -> None:
        super().__init__(value)
        self._source_record_differential_revalidation_loader_token = (
            _LOADED_OVERLAY_ITEM_SENTINEL
        )


# Navigation strings may help a person find the generated item, but must never
# make two obligations appear equal.  Keep unknown future fields by default so
# an audit-engine extension causes re-review until it is consciously classified.
# A source-free recursive fallback may pair only the complete non-presentation
# content of a generated group. The sidecar key, record/field spelling, source
# file location, and receipt bookkeeping are navigation rather than a semantic
# matching relation. A separate full raw-group witness is still retained below
# and must remain exact once this content identity finds a unique candidate.
_SOURCE_FREE_RECURSIVE_CONTENT_OMITTED_FIELDS = (
    _NAVIGATION_FIELDS
    | _RECEIPT_ONLY_FIELDS
    | frozenset({"risk_terms"})
)




def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _stable_provenance_path(path: Path) -> str:
    """Return the unique checkout-stable locator for repository evidence."""

    resolved = path.resolve()
    try:
        return resolved.relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        raise SourceRecordDifferentialRevalidationError(
            f"source-record differential evidence must be inside the repository: {path}"
        )


def _repository_provenance_path(value: object) -> Path:
    """Resolve one serialized provenance locator without accepting aliases."""

    text = str(value or "").strip()
    if not text or text == ".":
        raise SourceRecordDifferentialRevalidationError(
            "source-record differential provenance has no path"
        )
    pure = PurePosixPath(text)
    if pure.is_absolute() or any(part in {"", ".", ".."} for part in pure.parts):
        raise SourceRecordDifferentialRevalidationError(
            "source-record differential provenance path is not normalized relative to the repository"
        )
    path = (ROOT / Path(*pure.parts)).resolve()
    try:
        normalized = path.relative_to(ROOT.resolve()).as_posix()
    except ValueError as exc:
        raise SourceRecordDifferentialRevalidationError(
            "source-record differential provenance escapes the repository"
        ) from exc
    if normalized != text:
        raise SourceRecordDifferentialRevalidationError(
            "source-record differential provenance path is not canonical"
        )
    return path




def _reuse_exclusion_reason_ledger(
    value: object, *, label: str
) -> dict[str, str]:
    """Validate a descriptor-only reviewer exclusion ledger.

    This deliberately accepts neither generated judgment keys nor any Lean
    naming surface.  A digest identifies a complete current semantic group;
    its reason only explains why that otherwise reusable group must receive a
    fresh current review.
    """

    if not isinstance(value, Mapping):
        raise SourceRecordDifferentialRevalidationError(
            f"{label} must map semantic descriptor SHA-256 values to reasons"
        )
    reasons: dict[str, str] = {}
    for raw_digest, raw_reason in value.items():
        digest = _sha256(raw_digest)
        reason = raw_reason.strip() if isinstance(raw_reason, str) else ""
        if not digest or not reason or digest in reasons:
            raise SourceRecordDifferentialRevalidationError(
                f"{label} has an invalid, duplicate, or undocumented descriptor exclusion"
            )
        reasons[digest] = reason
    if not reasons:
        raise SourceRecordDifferentialRevalidationError(
            f"{label} has no descriptor exclusions"
        )
    return reasons


def _reuse_exclusions_artifact_error(
    payload: object,
    *,
    paper: str,
    current_raw_audit: Mapping[str, Any] | None = None,
) -> str:
    """Return whether a reviewer exclusion artifact is admissible.

    The artifact is intentionally small and fail-closed.  It has exactly one
    selector surface: a current semantic-descriptor SHA-256.  Binding it to
    the current raw receipts prevents an old exclusion decision from silently
    narrowing a later differential overlay.
    """

    if not isinstance(payload, Mapping):
        return "reuse-exclusions artifact is not an object"
    expected_fields = {
        "schema",
        "artifact_kind",
        "policy_version",
        "paper",
        "current_source_record_audit_sha256",
        "current_source_record_audit_integrity_sha256",
        SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD,
    }
    unexpected = sorted(str(key) for key in payload if str(key) not in expected_fields)
    if unexpected:
        return "reuse-exclusions artifact has unsupported fields: " + ", ".join(
            unexpected[:5]
        )
    if payload.get("schema") != SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_SCHEMA:
        return "reuse-exclusions artifact has an unsupported schema"
    if (
        str(payload.get("artifact_kind") or "").strip()
        != SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_ARTIFACT_KIND
    ):
        return "reuse-exclusions artifact has the wrong artifact kind"
    if (
        str(payload.get("policy_version") or "").strip()
        != SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_POLICY_VERSION
    ):
        return "reuse-exclusions artifact has an unsupported policy"
    if payload.get("paper") != paper:
        return "reuse-exclusions artifact belongs to another paper"
    if not _sha256(payload.get("current_source_record_audit_sha256")):
        return "reuse-exclusions artifact lacks a current raw aggregate receipt"
    if not _sha256(payload.get("current_source_record_audit_integrity_sha256")):
        return "reuse-exclusions artifact lacks a current raw integrity receipt"
    try:
        _reuse_exclusion_reason_ledger(
            payload.get(SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD),
            label="reuse-exclusions artifact",
        )
    except SourceRecordDifferentialRevalidationError as exc:
        return str(exc)
    if current_raw_audit is not None:
        if _sha256(payload.get("current_source_record_audit_sha256")) != _sha256(
            current_raw_audit.get("source_record_audit_sha256")
        ):
            return "reuse-exclusions artifact is not bound to the current raw aggregate receipt"
        if _sha256(payload.get("current_source_record_audit_integrity_sha256")) != _sha256(
            current_raw_audit.get("source_record_audit_integrity_sha256")
        ):
            return "reuse-exclusions artifact is not bound to the current raw integrity receipt"
    return ""


def _reuse_exclusions_record(
    payload: Mapping[str, Any], path: Path
) -> dict[str, Any]:
    """Serialize exact artifact provenance into the overlay receipt."""

    reasons = _reuse_exclusion_reason_ledger(
        payload.get(SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD),
        label="reuse-exclusions artifact",
    )
    return {
        "path": _stable_provenance_path(path),
        "file_sha256": _file_sha256(path),
        "schema": SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_SCHEMA,
        "artifact_kind": SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_ARTIFACT_KIND,
        "policy_version": SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_POLICY_VERSION,
        "paper": str(payload.get("paper") or ""),
        "current_source_record_audit_sha256": _sha256(
            payload.get("current_source_record_audit_sha256")
        ),
        "current_source_record_audit_integrity_sha256": _sha256(
            payload.get("current_source_record_audit_integrity_sha256")
        ),
        SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD: {
            digest: reasons[digest] for digest in sorted(reasons)
        },
    }


def _reuse_exclusions_record_error(
    value: object,
    *,
    paper: str,
    current_raw_audit: Mapping[str, Any] | None = None,
) -> str:
    """Reauthenticate a serialized descriptor-only exclusion record."""

    if not isinstance(value, Mapping):
        return "overlay reuse-exclusions provenance is not an object"
    expected_fields = {
        "path",
        "file_sha256",
        "schema",
        "artifact_kind",
        "policy_version",
        "paper",
        "current_source_record_audit_sha256",
        "current_source_record_audit_integrity_sha256",
        SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD,
    }
    if set(value) != expected_fields:
        return "overlay reuse-exclusions provenance has an unsupported shape"
    try:
        artifact_path = _repository_provenance_path(value.get("path"))
        artifact = _read_json_object(artifact_path)
    except (OSError, SourceRecordDifferentialRevalidationError) as exc:
        return "could not read reuse-exclusions artifact: " + str(exc)
    if _file_sha256(artifact_path) != str(value.get("file_sha256") or ""):
        return "reuse-exclusions artifact bytes differ from the overlay receipt"
    if error := _reuse_exclusions_artifact_error(
        artifact, paper=paper, current_raw_audit=current_raw_audit
    ):
        return error
    expected = _reuse_exclusions_record(artifact, artifact_path)
    if canonical_digest_payload(value) != canonical_digest_payload(expected):
        return "reuse-exclusions artifact content differs from the overlay receipt"
    return ""


def _reuse_exclusions_current_group_error(
    reasons: Mapping[str, str],
    descriptor_index: Mapping[str, list[tuple[str, Mapping[str, object]]]],
) -> str:
    """Ensure each descriptor-only exclusion resolves to one current group."""

    for digest in reasons:
        if len(descriptor_index.get(digest, [])) != 1:
            return (
                "reuse-exclusions descriptor does not identify exactly one "
                "current semantic group"
            )
    return ""


def _read_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordDifferentialRevalidationError(
            f"could not read JSON object at {path}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceRecordDifferentialRevalidationError(f"{path} is not a JSON object")
    return payload
















def _payload_is_non_evidence(payload: Mapping[str, Any]) -> bool:
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


def _effective(value: Mapping[str, Any], payload: Mapping[str, Any], field: str) -> Any:
    return value.get(field) or payload.get(field)














































def _archived_source_status_projection_normalized_group(
    group: Mapping[str, object],
    bridge: ValidatedArchivedSourceStatusProjectionBridge,
) -> tuple[dict[str, object] | None, bool, str]:
    """Normalize only receipt-bound archived associations in one raw group.

    This is a descriptor preparation step, not a group matcher.  Each source
    association is selected by its complete raw association-record digest by
    the validated bridge; judgment keys, declaration names, and source-map
    keys never choose a candidate here.  The caller must still require a
    unique complete normalized descriptor class.
    """

    if not isinstance(bridge, ValidatedArchivedSourceStatusProjectionBridge):
        return None, False, "source-status bridge did not yield a validated context"
    raw_descriptor = group.get("descriptor")
    raw_members = group.get("raw_members")
    if not isinstance(raw_descriptor, Mapping) or not isinstance(raw_members, list):
        return None, False, "generated group has no complete raw descriptor/members"
    raw_scope = raw_descriptor.get("raw_formalization_scope")
    if not isinstance(raw_scope, Mapping):
        return None, False, "generated group has no raw formalization-scope descriptor"
    normalized_members: list[tuple[str, Mapping[str, Any]]] = []
    member_descriptors: list[dict[str, object]] = []
    changed = False
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return None, False, "generated group has malformed complete raw members"
        section, raw_item = member
        item = copy.deepcopy(dict(raw_item))
        for field, association in _association_mappings(raw_item):
            if not archived_source_status_association_is_rebound(association, bridge):
                continue
            rebound = normalized_archived_source_status_association(association, bridge)
            if not isinstance(rebound, Mapping):  # defensive against future bridge APIs.
                return None, False, "source-status bridge returned a malformed association"
            item[field] = copy.deepcopy(dict(rebound))
            changed = True
        normalized_members.append((section, item))
        member_descriptors.append(
            {
                "section": section,
                "descriptor": OBLIGATIONS.source_record_obligation_descriptor(
                    item, section=section
                ),
            }
        )
    member_descriptors.sort(
        key=lambda entry: json.dumps(entry, sort_keys=True, separators=(",", ":"))
    )
    descriptor: dict[str, object] = {
        "schema": SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_SCHEMA,
        "raw_formalization_scope": copy.deepcopy(dict(raw_scope)),
        "members": member_descriptors,
    }
    normalized_group = {
        "descriptor": descriptor,
        "descriptor_sha256": _canonical_digest(descriptor),
        "raw_members": normalized_members,
        "semantic_model_items": [
            dict(item)
            for section, item in normalized_members
            if section == "semantic_model_items"
        ],
    }
    return normalized_group, changed, ""




def _complete_reissue_raw_group_identity(
    group: Mapping[str, object],
) -> tuple[dict[str, object] | None, str]:
    """Bind one strict-reissue response to its complete generated raw group.

    The group key is only a sidecar locator.  Its identity is the canonical
    multiset of every full raw member (section plus complete raw item), so a
    duplicate semantic descriptor can never be used as an interchangeable
    response target in the strict receipt-reissue path.
    """

    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list) or not raw_members:
        return None, "generated group has no complete raw members"
    members: list[dict[str, object]] = []
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return None, "generated group has malformed complete raw members"
        members.append({"section": member[0], "raw_item": dict(member[1])})
    return {
        "schema": SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_SCHEMA,
        "member_count": len(members),
        "canonical_sha256": _canonical_digest(members),
    }, ""


def _source_free_recursive_content_projection(value: object) -> object:
    """Project a source-free raw member without navigation or receipt noise.

    This is deliberately stricter than the semantic descriptor: it retains
    every non-presentation generated field, including recursive containment
    and expanded obligation content. It only removes names/locations used for
    navigation plus machine-generated receipt bookkeeping. It never sees a
    source association because the caller first proves the mapless lane.
    """

    if isinstance(value, Mapping):
        return {
            str(key): _source_free_recursive_content_projection(child)
            for key, child in value.items()
            if str(key) not in _SOURCE_FREE_RECURSIVE_CONTENT_OMITTED_FIELDS
        }
    if isinstance(value, list):
        return [_source_free_recursive_content_projection(child) for child in value]
    if isinstance(value, tuple):
        return [_source_free_recursive_content_projection(child) for child in value]
    return value


def _source_free_recursive_content_identity(
    group: Mapping[str, object],
) -> tuple[dict[str, object] | None, str]:
    """Return the complete name-free raw-content identity for one group."""

    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list) or not raw_members:
        return None, "generated group has no complete raw members"
    members: list[dict[str, object]] = []
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return None, "generated group has malformed complete raw members"
        members.append(
            {
                "section": member[0],
                "raw_item": _source_free_recursive_content_projection(member[1]),
            }
        )
    return {
        "schema": SOURCE_FREE_RECURSIVE_CONTENT_IDENTITY_SCHEMA,
        "member_count": len(members),
        "canonical_sha256": _canonical_digest(members),
    }, ""


def _source_free_recursive_content_identity_matches(
    candidates: list[tuple[str, Mapping[str, object]]],
    *,
    target: Mapping[str, object],
) -> list[tuple[str, Mapping[str, object]]]:
    """Find the unique current group with one name-free content identity.

    This is intentionally only a candidate selector for a mapless recursive
    group whose descriptor class is otherwise ambiguous.  It does not make a
    response reusable by itself: the caller still proves that the selected
    group is mapless/non-semantic and that its complete raw group is exactly
    identical to the archived one.  Count *every* current group with the
    content identity before making that decision, including one that would
    later fail the mapless lane, so source credit cannot be hidden by the
    fallback projection.
    """

    target_digest = canonical_digest_payload(target)
    matches: list[tuple[str, Mapping[str, object]]] = []
    for key, group in candidates:
        identity, error = _source_free_recursive_content_identity(group)
        if error or identity is None:
            continue
        if canonical_digest_payload(identity) == target_digest:
            matches.append((key, group))
    return matches


def _complete_reissue_raw_group_identity_error(
    recorded: object,
    *,
    prior_group: Mapping[str, object] | None = None,
    current_group: Mapping[str, object] | None = None,
) -> str:
    """Recompute one strict transport's prior/current raw-group identities."""

    if not isinstance(recorded, Mapping):
        return "complete receipt reissue item has no raw-group identity"
    if recorded.get("schema") != SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_SCHEMA:
        return "complete receipt reissue item has an unsupported raw-group identity schema"
    identities: dict[str, dict[str, object]] = {}
    for field, group in (("prior", prior_group), ("current", current_group)):
        saved = recorded.get(field)
        if not isinstance(saved, Mapping):
            return f"complete receipt reissue item lacks `{field}` raw-group identity"
        if (
            saved.get("schema") != SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_SCHEMA
            or not isinstance(saved.get("member_count"), int)
            or saved.get("member_count") < 1
            or not _sha256(saved.get("canonical_sha256"))
        ):
            return f"complete receipt reissue item has malformed `{field}` raw-group identity"
        if group is None:
            continue
        actual, actual_error = _complete_reissue_raw_group_identity(group)
        if actual_error or actual is None:
            return f"complete receipt reissue {field} raw group is invalid: {actual_error}"
        if canonical_digest_payload(saved) != canonical_digest_payload(actual):
            return f"complete receipt reissue {field} raw-group identity differs from raw audit"
        identities[field] = actual
    if len(identities) == 2 and (
        canonical_digest_payload(identities["prior"])
        != canonical_digest_payload(identities["current"])
    ):
        return "complete receipt reissue prior/current raw groups differ"
    return ""


def _complete_reissue_response_semantic_association_error(
    response: Mapping[str, Any], group: Mapping[str, object]
) -> str:
    """Verify a preserved response pin directly against an exact raw group."""

    if "semantic_association_sha256" not in response:
        return ""
    pin = _sha256(response.get("semantic_association_sha256"))
    if not pin:
        return "complete receipt reissue response semantic association pin is malformed"
    records = _group_semantic_association_rebind_records(group)
    if not any(record.get("semantic_association_sha256") == pin for record in records):
        return (
            "complete receipt reissue response semantic association pin is absent "
            "from its exact generated raw group"
        )
    return ""


def _complete_reusable_section_identity(
    payload: Mapping[str, Any],
    groups: Mapping[str, Mapping[str, object]],
) -> tuple[dict[str, object] | None, str]:
    """Bind an all-group receipt reissue to every raw reusable section.

    Ordinary differential reuse intentionally works one semantic group at a
    time.  A complete receipt reissue is stricter: it is available only when
    the complete raw reusable-item sections are unchanged as canonical JSON
    and every generated group descriptor is unchanged as a multiset.  This is
    a transport identity, not a declaration-name matching relation.
    """

    sections: dict[str, dict[str, object]] = {}
    for section in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        present = section in payload
        values = payload.get(section)
        if values is None:
            values = []
        if not isinstance(values, list):
            return None, f"raw audit `{section}` is not a list"
        if not all(isinstance(item, Mapping) for item in values):
            return None, f"raw audit `{section}` has a non-object item"
        sections[section] = {
            "present": present,
            "item_count": len(values),
            "canonical_sha256": _canonical_digest(values),
        }
    descriptors = []
    for group in groups.values():
        descriptor = group.get("descriptor")
        digest = _sha256(group.get("descriptor_sha256"))
        if not isinstance(descriptor, Mapping) or not digest:
            return None, "raw audit has a malformed generated semantic descriptor"
        if digest != _canonical_digest(descriptor):
            return None, "raw audit has a malformed generated semantic descriptor digest"
        descriptors.append({"sha256": digest, "descriptor": descriptor})
    descriptors.sort(
        key=lambda value: json.dumps(value, sort_keys=True, separators=(",", ":"))
    )
    return {
        "schema": SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_SCHEMA,
        "reusable_sections": sections,
        "generated_group_count": len(groups),
        "generated_descriptor_multiset_sha256": _canonical_digest(descriptors),
    }, ""


def _complete_reissue_path_label(path: tuple[str, ...]) -> str:
    return ".".join(path)


def _complete_reissue_path_value(
    payload: Mapping[str, Any], path: tuple[str, ...]
) -> tuple[bool, object]:
    current: object = payload
    for field in path:
        if not isinstance(current, Mapping) or field not in current:
            return False, None
        current = current[field]
    return True, current


def _complete_reissue_replace_path(
    payload: dict[str, Any], path: tuple[str, ...], value: object
) -> None:
    current: dict[str, Any] = payload
    for field in path[:-1]:
        next_value = current.get(field)
        if not isinstance(next_value, dict):  # Prechecked by the caller.
            raise SourceRecordDifferentialRevalidationError(
                "complete receipt reissue attempted to normalize a missing aggregate path"
            )
        current = next_value
    current[path[-1]] = value


def _complete_reissue_aggregate_metadata_identity(
    payload: Mapping[str, Any],
) -> tuple[dict[str, object] | None, str]:
    """Return a fail-closed normalized identity for receipt-only deltas.

    Full reusable-section equality cannot, by itself, prove that unrelated
    aggregate provenance remained stable.  This identity accepts only the two
    self-generated raw receipts and, when present in all three replicated
    projections, the receipt-reprojector's selected semantic-projection SHA.
    Every other serialized raw field remains in the canonical digest.
    """

    normalized = copy.deepcopy(dict(payload))
    surface_schema = payload.get(SOURCE_RECORD_AUDIT_SURFACE_SCHEMA_FIELD)
    if surface_schema not in {
        LEGACY_SOURCE_RECORD_AUDIT_SURFACE_SCHEMA,
        SOURCE_RECORD_AUDIT_SURFACE_SCHEMA,
    }:
        return None, "raw audit has an unsupported aggregate-surface schema"
    generated_receipt_paths = list(_COMPLETE_REISSUE_GENERATED_RECEIPT_PATHS)
    if surface_schema == SOURCE_RECORD_AUDIT_SURFACE_SCHEMA:
        generated_receipt_paths.extend(
            _COMPLETE_REISSUE_COMPACT_GENERATED_RECEIPT_PATHS
        )
    for path in generated_receipt_paths:
        present, value = _complete_reissue_path_value(payload, path)
        if not present or not _sha256(value):
            return (
                None,
                "raw audit lacks a valid generated receipt at `"
                + _complete_reissue_path_label(path)
                + "`",
            )
        _complete_reissue_replace_path(
            normalized, path, "<complete-reissue-generated-receipt>"
        )

    logical_surface = source_record_audit_surface_view(payload)
    if not isinstance(logical_surface, Mapping):
        return None, "raw audit has no authenticated logical aggregate surface"
    raw_projection = logical_surface.get("raw_evidence_projection")
    logical_selected_locations = (
        (payload, _COMPLETE_REISSUE_SELECTED_PROJECTION_TAIL),
        (logical_surface, _COMPLETE_REISSUE_SELECTED_PROJECTION_TAIL),
        (raw_projection, _COMPLETE_REISSUE_SELECTED_PROJECTION_TAIL),
    )
    selected_values: list[str] = []
    selected_presence: list[bool] = []
    for container, path in logical_selected_locations:
        present, value = (
            _complete_reissue_path_value(container, path)
            if isinstance(container, Mapping)
            else (False, None)
        )
        selected_presence.append(present)
        if present:
            digest = _sha256(value)
            if not digest:
                return (
                    None,
                    "raw audit has an invalid selected semantic-projection receipt at `"
                    + _complete_reissue_path_label(path)
                    + "`",
                )
            selected_values.append(digest)
    if any(selected_presence) and not all(selected_presence):
        return (
            None,
            "raw audit has only a partial replicated selected semantic-projection receipt",
        )
    if selected_values and len(set(selected_values)) != 1:
        return (
            None,
            "raw audit's replicated selected semantic-projection receipts disagree",
        )
    if selected_values:
        # Schema 1 serialized all three logical copies. Schema 2 serializes
        # only the canonical top-level value; its two surface digests above
        # authenticate the reconstructed logical copies.
        serialized_selected_paths = [
            path
            for path in _COMPLETE_REISSUE_SELECTED_PROJECTION_PATHS
            if _complete_reissue_path_value(payload, path)[0]
        ]
        for path in serialized_selected_paths:
            _complete_reissue_replace_path(
                normalized, path, "<complete-reissue-selected-semantic-projection>"
            )

    identity: dict[str, object] = {
        "schema": SOURCE_RECORD_COMPLETE_REISSUE_AGGREGATE_DELTA_SCHEMA,
        "policy": SOURCE_RECORD_COMPLETE_REISSUE_AGGREGATE_DELTA_POLICY,
        "generated_receipt_paths": [
            _complete_reissue_path_label(path)
            for path in generated_receipt_paths
        ],
        "selected_semantic_projection_path_state": (
            "replicated" if selected_values else "absent"
        ),
        "selected_semantic_projection_paths": (
            [
                _complete_reissue_path_label(path)
                for path in _COMPLETE_REISSUE_SELECTED_PROJECTION_PATHS
            ]
            if selected_values
            else []
        ),
        "normalized_payload_sha256": _canonical_digest(normalized),
    }
    if selected_values:
        identity["selected_semantic_projection_sha256"] = selected_values[0]
    return identity, ""


def _complete_reissue_aggregate_metadata_identity_error(
    value: object,
    *,
    prior_raw_audit: Mapping[str, Any],
    current_raw_audit: Mapping[str, Any],
) -> str:
    """Recompute the narrow aggregate-delta receipt for both raw audits."""

    if not isinstance(value, Mapping):
        return "complete receipt reissue has no aggregate metadata identity"
    prior_identity, prior_error = _complete_reissue_aggregate_metadata_identity(
        prior_raw_audit
    )
    current_identity, current_error = _complete_reissue_aggregate_metadata_identity(
        current_raw_audit
    )
    if prior_error or prior_identity is None:
        return "complete receipt reissue prior aggregate metadata is invalid: " + prior_error
    if current_error or current_identity is None:
        return "complete receipt reissue current aggregate metadata is invalid: " + current_error
    recorded_prior = value.get("prior")
    recorded_current = value.get("current")
    if canonical_digest_payload(recorded_prior) != canonical_digest_payload(prior_identity):
        return "complete receipt reissue prior aggregate metadata differs from archived raw"
    if canonical_digest_payload(recorded_current) != canonical_digest_payload(current_identity):
        return "complete receipt reissue current aggregate metadata differs from current raw"
    if canonical_digest_payload(prior_identity.get("normalized_payload_sha256")) != canonical_digest_payload(
        current_identity.get("normalized_payload_sha256")
    ):
        return "complete receipt reissue changed aggregate metadata outside allowed receipt paths"
    return ""


def _complete_reissue_attested_current_revalidation_record(
    *,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    candidate_sidecar: Mapping[str, Any],
    candidate_sidecar_path: Path,
    attestation_path: Path,
    replay_only: bool = False,
) -> tuple[dict[str, object] | None, str]:
    """Authenticate a candidate full-current revalidation before transport.

    Strict raw equality can carry a complete previously attested ledger, but
    cannot convert an unverified candidate sidecar into evidence.  At issuance
    this runs the current-revalidation validator's full source-target checks.
    Later loader replay rechecks exact immutable evidence and its attested
    ledger without rerunning the expensive identity-only source audit.
    """

    current_revalidation = _current_revalidation_module()
    metadata = candidate_sidecar.get(
        getattr(current_revalidation, "CURRENT_REVALIDATION_FIELD", "")
    )
    if not isinstance(metadata, Mapping):
        return None, "candidate sidecar lacks current semantic revalidation metadata"
    try:
        relative_attestation = str(metadata.get("attestation_path") or "").strip()
        relative_sidecar = str(
            metadata.get("current_judgment_sidecar_path") or ""
        ).strip()
        if not relative_attestation or not relative_sidecar:
            return None, "candidate current revalidation metadata lacks attestation or sidecar path"
        metadata_attestation = (paper_dir / relative_attestation).resolve()
        metadata_sidecar = (paper_dir / relative_sidecar).resolve()
        paper_root = paper_dir.resolve()
        metadata_attestation.relative_to(paper_root)
        metadata_sidecar.relative_to(paper_root)
        if metadata_attestation != attestation_path.resolve():
            return None, "candidate current revalidation metadata names a different attestation path"
        if metadata_sidecar != candidate_sidecar_path.resolve():
            return None, "candidate current revalidation metadata names a different sidecar path"
        if not metadata_attestation.is_file() or not metadata_sidecar.is_file():
            return None, "candidate current revalidation attestation or sidecar file is missing"
        attestation_sha256 = _file_sha256(metadata_attestation)
        if _sha256(metadata.get("attestation_sha256")) != attestation_sha256:
            return None, "candidate current revalidation attestation bytes differ from its metadata"
        errors = current_revalidation.validate_rebound_sidecar(
            raw_audit,
            candidate_sidecar,
            paper=paper,
            paper_dir=paper_dir,
            output_sidecar_path=candidate_sidecar_path,
            include_runtime_semantic_checks=not replay_only,
        )
    except (OSError, RuntimeError, ValueError) as exc:
        return None, "could not resolve candidate current revalidation evidence: " + str(exc)
    except current_revalidation.SourceRecordCurrentRevalidationError as exc:
        return None, "candidate current revalidation is invalid: " + str(exc)
    if errors:
        return None, "candidate current revalidation is invalid: " + "; ".join(errors[:3])
    return {
        "schema": SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_SCHEMA,
        "candidate_sidecar": {
            "path": _stable_provenance_path(candidate_sidecar_path),
            "file_sha256": _file_sha256(candidate_sidecar_path),
        },
        "attestation": {
            "path": _stable_provenance_path(metadata_attestation),
            "file_sha256": attestation_sha256,
        },
        "archived_raw_source_record_audit_sha256": _sha256(
            raw_audit.get("source_record_audit_sha256")
        ),
    }, ""


def _complete_reissue_attested_current_revalidation_error(
    value: object,
    *,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    candidate_sidecar: Mapping[str, Any],
    candidate_sidecar_path: Path,
) -> str:
    """Recheck the exact candidate attestation binding at overlay load time."""

    if not isinstance(value, Mapping):
        return "complete receipt reissue lacks attested current-revalidation provenance"
    if value.get("schema") != SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_SCHEMA:
        return "complete receipt reissue has an unsupported current-revalidation provenance schema"
    candidate_record = value.get("candidate_sidecar")
    attestation_record = value.get("attestation")
    if not isinstance(candidate_record, Mapping) or not isinstance(attestation_record, Mapping):
        return "complete receipt reissue has malformed candidate current-revalidation provenance"
    try:
        recorded_sidecar = _repository_provenance_path(candidate_record.get("path"))
        recorded_attestation = _repository_provenance_path(attestation_record.get("path"))
    except SourceRecordDifferentialRevalidationError as exc:
        return "complete receipt reissue has invalid candidate current-revalidation path: " + str(exc)
    if recorded_sidecar != candidate_sidecar_path.resolve():
        return "complete receipt reissue candidate sidecar path differs from archived sidecar"
    if not _sha256(candidate_record.get("file_sha256")) or not _sha256(
        attestation_record.get("file_sha256")
    ):
        return "complete receipt reissue has malformed candidate current-revalidation file hashes"
    try:
        if _file_sha256(recorded_sidecar) != candidate_record.get("file_sha256"):
            return "complete receipt reissue candidate sidecar bytes differ from provenance"
        if _file_sha256(recorded_attestation) != attestation_record.get("file_sha256"):
            return "complete receipt reissue candidate attestation bytes differ from provenance"
    except OSError as exc:
        return "complete receipt reissue candidate current-revalidation file is unreadable: " + str(exc)
    actual, actual_error = _complete_reissue_attested_current_revalidation_record(
        paper=paper,
        paper_dir=paper_dir,
        raw_audit=raw_audit,
        candidate_sidecar=candidate_sidecar,
        candidate_sidecar_path=candidate_sidecar_path,
        attestation_path=recorded_attestation,
        replay_only=True,
    )
    if actual_error or actual is None:
        return actual_error
    if canonical_digest_payload(value) != canonical_digest_payload(actual):
        return "complete receipt reissue candidate current-revalidation provenance differs from evidence"
    return ""


def _complete_reusable_section_identity_error(
    identity: object,
    *,
    prior_raw_audit: Mapping[str, Any],
    prior_groups: Mapping[str, Mapping[str, object]],
    current_raw_audit: Mapping[str, Any],
    current_groups: Mapping[str, Mapping[str, object]],
) -> str:
    """Verify a strict reissue receipt against both exact raw surfaces."""

    if not isinstance(identity, Mapping):
        return "complete receipt reissue has no reusable-section identity"
    if identity.get("schema") != SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_SCHEMA:
        return "complete receipt reissue has an unsupported reusable-section identity schema"
    if (
        str(identity.get("mode") or "").strip()
        != SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_MODE
    ):
        return "complete receipt reissue has the wrong reusable-section identity mode"
    prior_identity, prior_error = _complete_reusable_section_identity(
        prior_raw_audit, prior_groups
    )
    current_identity, current_error = _complete_reusable_section_identity(
        current_raw_audit, current_groups
    )
    if prior_error or prior_identity is None:
        return "complete receipt reissue prior raw identity is invalid: " + prior_error
    if current_error or current_identity is None:
        return "complete receipt reissue current raw identity is invalid: " + current_error
    recorded_prior = identity.get("prior")
    recorded_current = identity.get("current")
    if canonical_digest_payload(recorded_prior) != canonical_digest_payload(prior_identity):
        return "complete receipt reissue prior reusable-section identity differs from archived raw"
    if canonical_digest_payload(recorded_current) != canonical_digest_payload(current_identity):
        return "complete receipt reissue current reusable-section identity differs from current raw"
    if canonical_digest_payload(prior_identity) != canonical_digest_payload(current_identity):
        return "complete receipt reissue raw reusable sections or descriptor multiset changed"
    aggregate_error = _complete_reissue_aggregate_metadata_identity_error(
        identity.get("allowed_aggregate_metadata_delta"),
        prior_raw_audit=prior_raw_audit,
        current_raw_audit=current_raw_audit,
    )
    if aggregate_error:
        return aggregate_error
    return ""


def _response_classification(value: Mapping[str, object]) -> str:
    """Return the stored disposition category without interpreting its name.

    Historical sidecars have used a few equivalent ledger fields.  They are
    response metadata, not semantic matching inputs: callers have already
    established descriptor equality before this function is consulted.
    """

    return str(
        value.get("classification")
        or value.get("judgment")
        or value.get("verdict")
        or value.get("status")
        or ""
    ).strip()


def _response_field_has_value(value: Mapping[str, object], field: str) -> bool:
    """Whether one source-credit response field carries a substantive claim."""

    raw = value.get(field)
    if raw is None or raw is False:
        return False
    if isinstance(raw, str):
        return bool(raw.strip())
    if isinstance(raw, Mapping) or isinstance(raw, (list, tuple, set)):
        return bool(raw)
    return True


def _recursive_response_requires_direct_parent_route(
    response: Mapping[str, object] | None,
) -> bool:
    """Return whether exact reuse still needs a direct source-parent route.

    A direct route is mandatory for every source-credit disposition, including
    an approved source convention.  Exact descriptor reuse is safe without
    that route only for an explicit non-source-credit recursive disposition.
    An absent, malformed, or future classification therefore fails closed.
    """

    if response is None:
        # The manual-review summary does not have a current response to
        # classify.  Do not pretend a missing route is a raw-only failure;
        # the builder/loader pass the actual archived response when reuse is
        # being considered.
        return False
    classification = _response_classification(response)
    if classification in INPUT_SOURCE_CREDIT_CLASSIFICATIONS:
        return True
    disposition = str(response.get("source_target_disposition") or "").strip()
    if disposition in SOURCE_TARGET_DISPOSITIONS:
        return True
    if any(
        _response_field_has_value(response, field)
        for field in _RECURSIVE_SOURCE_CREDIT_RESPONSE_FIELDS
    ):
        return True
    return classification not in _NON_SOURCE_CREDIT_RECURSIVE_CLASSIFICATIONS


def _has_substantive_response_field(value: Mapping[str, object], field: str) -> bool:
    """Return whether one structured response credential is actually present."""

    raw = value.get(field)
    if raw is None or raw is False:
        return False
    if isinstance(raw, str):
        return bool(raw.strip())
    if isinstance(raw, Mapping) or isinstance(raw, (list, tuple, set)):
        return bool(raw)
    return True


def _source_free_recursive_member_error(item: Mapping[str, object]) -> str:
    """Reject an unrouted recursive item that carries source-credit structure.

    This is a deliberately narrow *mapless* lane.  It does not infer a source
    relation from a name or an enclosing record.  It only accepts a recursive
    item when the signed raw item itself has no association, explicit parent
    route, source semantic identity, or source-fidelity receipt.  An exact
    full raw-member identity is checked separately after the unique semantic
    descriptor pair is known.
    """

    if _association_mappings(item):
        return "unrouted non-source-credit recursive field carries a source association"
    if item.get("recursive_field_explicit_parent_route") is not None:
        return "unrouted non-source-credit recursive field carries a source parent route"
    if _source_semantic_identities(item):
        return "unrouted non-source-credit recursive field carries source semantic identities"
    if _sha256(item.get("source_record_item_source_proof_fidelity_records_sha256")):
        return "unrouted non-source-credit recursive field carries a source-proof fidelity receipt"
    return ""


def _source_free_recursive_response_error(response: Mapping[str, object]) -> str:
    """Reject machine-readable source credit on a purportedly source-free row."""

    classification = _response_classification(response)
    if classification not in _NON_SOURCE_CREDIT_RECURSIVE_CLASSIFICATIONS:
        return "recursive response is not an explicit non-source-credit disposition"
    if classification in INPUT_SOURCE_CREDIT_CLASSIFICATIONS:
        return "recursive response carries a source-credit classification"
    for field in _RECURSIVE_SOURCE_CREDIT_PIN_FIELDS:
        if _has_substantive_response_field(response, field):
            return "recursive response carries source-credit field `" + field + "`"
    return ""


def _group_has_semantic_model_obligation(group: Mapping[str, object]) -> bool:
    """Whether one response group includes an advertised model/result review."""

    raw_members = group.get("raw_members")
    return bool(
        isinstance(raw_members, list)
        and any(
            isinstance(member, tuple)
            and len(member) == 2
            and member[0] == "semantic_model_items"
            for member in raw_members
        )
    )


def _source_free_recursive_structural_identity(
    group: Mapping[str, object],
    *,
    response: Mapping[str, object] | None,
) -> tuple[dict[str, object] | None, str]:
    """Return an exact raw-member witness for the narrow mapless lane.

    ``None, ""`` means the group does not use this lane.  A response can use
    it only when it has an explicit non-source-credit classification and the
    group contains at least one recursive member with no direct parent route.
    The full raw member multiset is intentionally retained as an equality
    witness after semantic matching; it is never a selector for a current
    group.  That makes a changed recursive containment/field closure manual
    work even if its presentation-normalized descriptor is unchanged.
    """

    if response is None:
        return None, ""
    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list):
        return None, "generated group has no raw members"
    uses_lane = False
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return None, "generated group has malformed raw members"
        section, item = member
        if section != "recursive_field_items":
            continue
        if _recursive_field_parent_route_semantic_scope(item) is not None:
            continue
        # A malformed/partial route is still source structure and must not
        # become a mapless non-credit row merely because its semantic scope
        # could not be parsed.
        if item.get("recursive_field_explicit_parent_route") is not None:
            return None, "unrouted non-source-credit recursive field carries a malformed source parent route"
        uses_lane = True
        if error := _source_free_recursive_member_error(item):
            return None, error
    if not uses_lane:
        return None, ""
    if error := _source_free_recursive_response_error(response):
        return None, error
    identity, identity_error = _complete_reissue_raw_group_identity(group)
    if identity_error or identity is None:
        return None, "source-free recursive raw-member identity is invalid: " + identity_error
    content_identity, content_identity_error = _source_free_recursive_content_identity(
        group
    )
    if content_identity_error or content_identity is None:
        return (
            None,
            "source-free recursive content identity is invalid: "
            + content_identity_error,
        )
    return {
        "schema": SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_SCHEMA,
        "raw_group_identity": identity,
        "semantic_content_identity": content_identity,
    }, ""


def _source_free_recursive_structural_identity_error(
    recorded: object,
    *,
    group: Mapping[str, object],
    response: Mapping[str, object] | None,
) -> str:
    """Recompute one mapless recursive witness from authenticated raw data."""

    if not isinstance(recorded, Mapping):
        return "source-free recursive structural identity is not an object"
    if recorded.get("schema") != SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_SCHEMA:
        return "source-free recursive structural identity has an unsupported schema"
    if set(recorded) not in (
        {"schema", "raw_group_identity"},
        {"schema", "raw_group_identity", "semantic_content_identity"},
    ):
        return "source-free recursive structural identity has unsupported fields"
    actual, error = _source_free_recursive_structural_identity(
        group, response=response
    )
    if error:
        return error
    if actual is None:
        return "source-free recursive structural identity is attached to a non-mapless group"
    # Schema-v1 receipts issued before name-free content selection retained
    # only the strict raw witness.  They remain valid for the old unique
    # descriptor path, but cannot resolve a future descriptor collision.
    expected = (
        actual
        if "semantic_content_identity" in recorded
        else {
            "schema": actual["schema"],
            "raw_group_identity": actual["raw_group_identity"],
        }
    )
    if canonical_digest_payload(recorded) != canonical_digest_payload(expected):
        return "source-free recursive structural identity differs from authenticated raw group"
    return ""


def _group_differential_reuse_error(
    group: Mapping[str, object],
    *,
    response: Mapping[str, object] | None = None,
) -> str:
    """Return why this generated group cannot receive automatic reuse.

    Most groups are evaluated through their complete semantic descriptor. A
    recursive field claiming source credit has an additional source-fidelity
    requirement: it must carry a locally checked direct semantic parent route.
    A recursive response that explicitly makes no source-credit claim instead
    retains an exact descriptor match without inventing a route.  We never
    compose routes through another field or recover a parent by name.
    """

    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list):
        return "generated group has no raw members"
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return "generated group has malformed raw members"
        section, item = member
        if (
            section == "recursive_field_items"
            and _recursive_field_parent_route_semantic_scope(item) is None
            and _recursive_response_requires_direct_parent_route(response)
        ):
            return (
                "recursive field lacks a locally authenticated direct semantic "
                "parent route"
            )
    _identity, source_free_error = _source_free_recursive_structural_identity(
        group, response=response
    )
    if source_free_error:
        return source_free_error
    return ""


def _raw_audit_provenance(payload: Mapping[str, Any], path: Path) -> dict[str, str]:
    return {
        "path": _stable_provenance_path(path),
        "file_sha256": _file_sha256(path),
        "source_record_audit_sha256": _sha256(payload.get("source_record_audit_sha256")),
        "source_record_audit_integrity_sha256": _sha256(
            payload.get("source_record_audit_integrity_sha256")
        ),
    }


def _same_resolved_path(left: Path, right: Path) -> bool:
    try:
        return left.resolve() == right.resolve()
    except OSError:
        return False


def _archived_source_status_projection_bridge_context(
    *,
    bridge_path: Path,
    paper: str,
    paper_dir: Path,
    prior_raw_audit: Mapping[str, Any],
    prior_raw_audit_path: Path,
    prior_judgments: Mapping[str, Any],
    prior_judgments_path: Path,
    current_raw_audit: Mapping[str, Any],
    current_raw_audit_path: Path,
    recorded: Mapping[str, object] | None = None,
) -> tuple[ValidatedArchivedSourceStatusProjectionBridge | None, dict[str, str] | None, str]:
    """Load a bridge only when it replays the exact differential evidence.

    The bridge module authenticates its old/current source maps and fidelity
    ledgers as well as both raw receipts.  This wrapper additionally proves
    that those archived/current raw and sidecar files are the same evidence
    selected by this differential overlay.  A bridge cannot be used as a
    nearby-file waiver for another receipt.
    """

    context, receipt, evidence, error = (
        load_archived_source_status_projection_bridge_context(
            paper=paper,
            paper_dir=paper_dir,
            receipt_path=bridge_path,
        )
    )
    if error or context is None or receipt is None or evidence is None:
        return None, None, error or "could not load archived source-status bridge"
    if not isinstance(context, ValidatedArchivedSourceStatusProjectionBridge):
        return None, None, "archived source-status bridge did not yield a validated context"
    expected_evidence = {
        "prior_raw_audit": (prior_raw_audit_path, prior_raw_audit),
        "prior_judgments": (prior_judgments_path, prior_judgments),
        "current_raw_audit": (current_raw_audit_path, current_raw_audit),
    }
    for field, (expected_path, expected_payload) in expected_evidence.items():
        loaded = evidence.get(field)
        if (
            not isinstance(loaded, tuple)
            or len(loaded) != 3
            or not isinstance(loaded[0], Path)
            or not isinstance(loaded[1], Mapping)
            or not isinstance(loaded[2], bytes)
        ):
            return None, None, f"archived source-status bridge has malformed `{field}` evidence"
        actual_path, actual_payload, _actual_bytes = loaded
        if not _same_resolved_path(actual_path, expected_path):
            return None, None, f"archived source-status bridge `{field}` path differs from differential evidence"
        if canonical_digest_payload(actual_payload) != canonical_digest_payload(
            expected_payload
        ):
            return None, None, f"archived source-status bridge `{field}` content differs from differential evidence"
    try:
        bridge_record = {
            "path": _stable_provenance_path(bridge_path),
            "file_sha256": _file_sha256(bridge_path),
            "receipt_sha256": context.receipt_sha256,
        }
    except (OSError, SourceRecordDifferentialRevalidationError) as exc:
        return None, None, "could not authenticate archived source-status bridge file: " + str(exc)
    if recorded is not None and dict(recorded) != bridge_record:
        return None, None, "archived source-status bridge provenance differs from overlay"
    if _sha256(receipt.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_INTEGRITY_FIELD)) != context.receipt_sha256:
        return None, None, "archived source-status bridge receipt integrity differs from its validated context"
    return context, bridge_record, ""


def _current_raw_provenance_error(
    recorded: object, expected: Mapping[str, str]
) -> str:
    """Compare the stable identity of the receiving raw audit.

    A differential overlay archives its *prior* raw audit by exact file bytes.
    The current raw audit is different: ``--refresh-judgment-summary`` is
    explicitly allowed to rewrite only derived summary fields, which changes
    the JSON file hash while leaving both independently verified raw receipts
    unchanged.  The loader has already authenticated the current file through
    ``_raw_audit_error``; this comparison therefore binds its canonical path
    and the two stable receipts, deliberately not its serialization hash.
    """

    if not isinstance(recorded, Mapping):
        return "is missing"
    for field in (
        "path",
        "source_record_audit_sha256",
        "source_record_audit_integrity_sha256",
    ):
        if str(recorded.get(field) or "") != str(expected.get(field) or ""):
            return f"has a different `{field}`"
    # The issuance file hash remains required in the serialized overlay for a
    # human audit trail, but it cannot make a permitted summary refresh stale.
    if not _sha256(recorded.get("file_sha256")):
        return "has no valid issuance `file_sha256`"
    return ""


def _semantic_association_rebind_record(
    *, section: str, field: str, association: Mapping[str, Any]
) -> dict[str, object] | None:
    """Return one source-content-validated semantic association receipt.

    The public association pin also contains the reviewed elaborated signature,
    so it correctly changes when an enclosing result changes.  A local
    boundary/field judgment may nevertheless remain semantically unchanged.
    This record separates the source semantic content and route role that must
    stay equal from that volatile signature receipt.  It never uses a source
    key, declaration, theorem name, or binder spelling to identify a match.
    """

    if association.get("schema") != 2:
        return None
    supplied_pin = _sha256(association.get("semantic_association_sha256"))
    identities = association.get("source_item_identities")
    if not supplied_pin or not isinstance(identities, list) or not identities:
        return None
    semantic_identities: list[str] = []
    for identity in identities:
        if not isinstance(identity, Mapping):
            return None
        digest = _sha256(identity.get("source_semantic_sha256"))
        if not digest:
            return None
        semantic_identities.append(digest)
    if len(set(semantic_identities)) != len(semantic_identities):
        return None
    signature = association.get("reviewed_elaborated_signature_identity")
    if not isinstance(signature, Mapping):
        return None
    # Delegate the generated-pin rule to the target-disposition module.  This
    # validates the current association rather than trusting a copied pin.
    is_statement_component = (
        str(association.get("association_origin") or "").strip()
        == STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN
        or str(association.get("role") or "").strip()
        == STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE
    )
    if is_statement_component:
        expected_pin, _component_error = (
            statement_source_component_effective_semantic_pin(association)
        )
    elif (
        str(association.get("association_origin") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN
        or str(association.get("role") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE
    ):
        expected_pin, _review_error = (
            statement_source_review_effective_semantic_pin(association)
        )
    else:
        expected_pin = semantic_association_record_digest(
            semantic_identities, signature
        )
    if not expected_pin or supplied_pin != expected_pin:
        return None
    content = {
        "schema": SEMANTIC_ASSOCIATION_REBIND_SCHEMA,
        "section": section,
        "association_field": field,
        "association_schema": 2,
        "source_item_semantic_identities": sorted(semantic_identities),
        "source_association_role": _association_role_projection(association),
    }
    return {
        "content": content,
        "content_sha256": _canonical_digest(content),
        "semantic_association_sha256": supplied_pin,
    }


def _group_direct_source_domain_parent_contract(
    group: Mapping[str, object], item: Mapping[str, Any]
) -> Mapping[str, object] | None:
    """Return the in-memory contract derived for this exact raw field item."""

    contracts = group.get(_DIRECT_SOURCE_DOMAIN_PARENT_CONTRACTS_FIELD)
    if not isinstance(contracts, Mapping):
        return None
    candidate = contracts.get(id(item))
    return candidate if isinstance(candidate, Mapping) else None


def _recursive_parent_route_semantic_association_rebind_record(
    *,
    section: str,
    item: Mapping[str, Any],
    direct_source_domain_parent_contract: Mapping[str, object] | None = None,
) -> dict[str, object] | None:
    """Return one exact recursive parent-route response-pin receipt.

    A recursive response can carry the generated parent association pin even
    though the association is stored inside its parent-route receipt rather
    than in a top-level association field.  This is not an inferred route: the
    common parent-route validator authenticates the route, source semantic
    identity, convention, and parent signature before this helper exposes it.
    A legacy route retains the exact-raw-group requirement.  A newer derived
    direct-source-domain contract instead binds all source pins and the full
    parent input domain while deliberately excluding the parent conclusion;
    it may rebind a changed parent signature only after that contract remains
    byte-identical.  The direct semantic-model result row is still reviewed
    through its full descriptor, independently of this child transport.
    """

    scope = _recursive_field_parent_route_semantic_scope(item)
    if scope is None:
        return None
    parent_pin = _sha256(scope.get("parent_source_association_sha256"))
    source_semantic = _sha256(scope.get("source_item_semantic_sha256"))
    if not parent_pin or not source_semantic:
        return None
    if direct_source_domain_parent_contract is not None:
        contract = dict(direct_source_domain_parent_contract)
        if contract.get("schema") != _DIRECT_SOURCE_DOMAIN_PARENT_CONTRACT_SCHEMA:
            return None
        source_pins = contract.get("source_item_anchor_pins")
        route = item.get("recursive_field_explicit_parent_route")
        route_identities = (
            route.get("source_item_identities") if isinstance(route, Mapping) else None
        )
        if (
            not isinstance(source_pins, list)
            or len(source_pins) != 1
            or not isinstance(source_pins[0], Mapping)
            or not isinstance(route_identities, list)
            or len(route_identities) != 1
            or not isinstance(route_identities[0], Mapping)
        ):
            return None
        source_map_item_sha = _sha256(source_pins[0].get("source_map_item_sha256"))
        route_source_map_item_sha = _sha256(
            route_identities[0].get("source_map_item_sha256")
        )
        if (
            not source_map_item_sha
            or source_map_item_sha != route_source_map_item_sha
            or _sha256(source_pins[0].get("source_semantic_sha256"))
            != source_semantic
        ):
            return None
        content = {
            "schema": SEMANTIC_ASSOCIATION_REBIND_SCHEMA,
            "section": section,
            "association_field": "recursive_field_direct_source_domain_parent_contract",
            "association_schema": "recursive_parent_direct_source_domain_v1",
            "source_item_semantic_identities": [source_semantic],
            "source_association_role": contract,
        }
        return {
            "content": content,
            "content_sha256": _canonical_digest(content),
            "semantic_association_sha256": parent_pin,
        }

    route_content = dict(scope)
    route_content.pop("parent_source_association_sha256", None)
    content = {
        "schema": SEMANTIC_ASSOCIATION_REBIND_SCHEMA,
        "section": section,
        "association_field": "recursive_field_explicit_parent_route",
        "association_schema": "recursive_parent_route_v1",
        "source_item_semantic_identities": [source_semantic],
        "source_association_role": route_content,
    }
    return {
        "content": content,
        "content_sha256": _canonical_digest(content),
        "semantic_association_sha256": parent_pin,
        "requires_exact_raw_group_identity": True,
    }


def _group_semantic_association_rebind_records(
    group: Mapping[str, object],
) -> list[dict[str, object]]:
    """Collect valid generated association receipts for one response group."""

    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list):
        return []
    records: list[dict[str, object]] = []
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return []
        section, item = member
        for field, association in _association_mappings(item):
            record = _semantic_association_rebind_record(
                section=section, field=field, association=association
            )
            if record is not None:
                records.append(record)
        route_record = _recursive_parent_route_semantic_association_rebind_record(
            section=section,
            item=item,
            direct_source_domain_parent_contract=(
                _group_direct_source_domain_parent_contract(group, item)
                if section == "recursive_field_items"
                else None
            ),
        )
        if route_record is not None:
            records.append(route_record)
    return records


def _semantic_association_rebind_receipt(
    response: Mapping[str, Any],
    *,
    prior_group: Mapping[str, object],
    current_group: Mapping[str, object],
) -> tuple[dict[str, object] | None, str]:
    """Derive a safe current semantic-association pin for one response.

    A response without this optional provenance field needs no rebind.  If it
    does claim a pin, the old pin must be present on an authenticated prior raw
    association and each matching source-content/role record must lead to one
    unambiguous current generated pin.  A change in source content, route
    role, schema, or ambiguity is therefore manual-review debt, not a reason
    to preserve a stale response.
    """

    if "semantic_association_sha256" not in response:
        return None, ""
    prior_response_pin = _sha256(response.get("semantic_association_sha256"))
    if not prior_response_pin:
        return None, "response semantic association pin is malformed"
    prior_records = _group_semantic_association_rebind_records(prior_group)
    current_records = _group_semantic_association_rebind_records(current_group)
    matching_prior = [
        record
        for record in prior_records
        if record.get("semantic_association_sha256") == prior_response_pin
    ]
    if not matching_prior:
        return None, "response semantic association pin is not present on the archived generated group"
    requires_exact_raw_group_identity = any(
        record.get("requires_exact_raw_group_identity") is True
        for record in matching_prior
    )
    exact_raw_group_identity: dict[str, object] | None = None
    if requires_exact_raw_group_identity:
        prior_identity, prior_identity_error = _complete_reissue_raw_group_identity(
            prior_group
        )
        current_identity, current_identity_error = _complete_reissue_raw_group_identity(
            current_group
        )
        if (
            prior_identity_error
            or current_identity_error
            or prior_identity is None
            or current_identity is None
        ):
            return (
                None,
                "recursive parent-route response pin lacks a complete raw-group identity",
            )
        exact_raw_group_identity = {
            "schema": SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_SCHEMA,
            "prior": prior_identity,
            "current": current_identity,
        }
        if identity_error := _complete_reissue_raw_group_identity_error(
            exact_raw_group_identity,
            prior_group=prior_group,
            current_group=current_group,
        ):
            return None, "recursive parent-route " + identity_error
    current_by_content: dict[str, list[dict[str, object]]] = {}
    for record in current_records:
        digest = _sha256(record.get("content_sha256"))
        content = record.get("content")
        if digest and isinstance(content, Mapping) and digest == _canonical_digest(content):
            current_by_content.setdefault(digest, []).append(record)

    current_pins: set[str] = set()
    content_descriptors: dict[str, Mapping[str, object]] = {}
    for prior_record in matching_prior:
        content = prior_record.get("content")
        content_digest = _sha256(prior_record.get("content_sha256"))
        if (
            not isinstance(content, Mapping)
            or not content_digest
            or content_digest != _canonical_digest(content)
        ):
            return None, "archived generated association content is malformed"
        candidates = [
            record
            for record in current_by_content.get(content_digest, [])
            if canonical_digest_payload(record.get("content"))
            == canonical_digest_payload(content)
        ]
        if len(candidates) != 1:
            return None, "current generated association content is absent or ambiguous"
        current_pin = _sha256(candidates[0].get("semantic_association_sha256"))
        if not current_pin:
            return None, "current generated association lacks a valid semantic pin"
        current_pins.add(current_pin)
        content_descriptors[content_digest] = dict(content)
    if len(current_pins) != 1:
        return None, "one response pin would need to bind multiple current semantic associations"
    current_pin = next(iter(current_pins))
    if requires_exact_raw_group_identity and current_pin != prior_response_pin:
        return (
            None,
            "recursive parent-route response pin does not name the identical current parent association",
        )
    receipt: dict[str, object] = {
        "schema": SEMANTIC_ASSOCIATION_REBIND_SCHEMA,
        "prior_response_semantic_association_sha256": prior_response_pin,
        "current_semantic_association_sha256": current_pin,
        "association_content_descriptors": [
            {
                "content": content_descriptors[digest],
                "content_sha256": digest,
            }
            for digest in sorted(content_descriptors)
        ],
    }
    if exact_raw_group_identity is not None:
        receipt["recursive_parent_route_raw_group_identity"] = (
            exact_raw_group_identity
        )
    return receipt, ""


def _semantic_association_rebind_matches(
    recorded: object, expected: Mapping[str, object]
) -> bool:
    """Check a persisted rebind receipt without accepting an assertion alone."""

    if not isinstance(recorded, Mapping):
        return False
    if recorded.get("schema") != SEMANTIC_ASSOCIATION_REBIND_SCHEMA:
        return False
    return canonical_digest_payload(recorded) == canonical_digest_payload(expected)


def _current_group_associations_for_semantic_pin(
    group: Mapping[str, object], semantic_pin: str
) -> list[Mapping[str, object]]:
    """Return exact generated receiving associations for one response pin.

    This deliberately selects by the complete generated semantic association
    pin already authenticated by the differential receipt, not by a source
    key, theorem/declaration spelling, judgment key, or route label.  Duplicate
    copies of one byte-identical association are harmless; distinct records
    remain ambiguous and reject the reuse below.
    """

    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list):
        return []
    candidates: dict[str, Mapping[str, object]] = {}
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[1], Mapping)
        ):
            return []
        for _field, association in _association_mappings(member[1]):
            if _sha256(association.get("semantic_association_sha256")) != semantic_pin:
                continue
            candidates.setdefault(_canonical_digest(association), association)
    return [candidates[digest] for digest in sorted(candidates)]


def _administrative_projection_rebind_loaded_response(
    response: Mapping[str, Any],
    *,
    current_group: Mapping[str, object],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> dict[str, Any] | None:
    """Apply one exact current association rebind to a loaded response.

    Differential reuse first validates the ordinary archived-to-current
    semantic-association receipt.  Only after that succeeds can this method
    advance its *current* response pin through a schema-4-to-schema-5 receipt.
    It cannot use an old association in the archive, a similarly named source
    item, or an arbitrary mapping shaped like a receipt.  More than one
    distinct resulting response is ambiguous and stays unavailable.
    """

    if administrative_projection_rebind is None:
        return dict(response)
    if not isinstance(
        administrative_projection_rebind, ValidatedAdministrativeProjectionRebind
    ):
        return None
    current_pin = _sha256(response.get("semantic_association_sha256"))
    if not current_pin:
        return dict(response)
    candidates = _current_group_associations_for_semantic_pin(
        current_group, current_pin
    )
    if not candidates:
        return None
    transported: dict[str, Mapping[str, object]] = {}
    for raw_association in candidates:
        effective_association = administrative_projection_rebound_association(
            raw_association, administrative_projection_rebind
        )
        effective_pin = _sha256(
            effective_association.get("semantic_association_sha256")
        )
        if not effective_pin:
            return None
        candidate = administrative_projection_rebound_response(
            response,
            raw_association,
            administrative_projection_rebind,
        )
        if _sha256(candidate.get("semantic_association_sha256")) != effective_pin:
            return None
        transported[_canonical_digest(candidate)] = candidate
    if len(transported) != 1:
        return None
    return dict(next(iter(transported.values())))


def _materialize_current_semantic_association_rebind(
    value: Mapping[str, Any],
    *,
    prior_group: Mapping[str, object],
    current_group: Mapping[str, object],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None = None,
    archived_source_status_bridge: ValidatedArchivedSourceStatusProjectionBridge | None = None,
) -> dict[str, Any] | None:
    """Return a loader-only response with a checked current association pin."""

    effective_value = rebound_archived_source_status_response(
        value, archived_source_status_bridge
    )
    if effective_value is None:
        return None
    expected, error = _semantic_association_rebind_receipt(
        effective_value,
        prior_group=prior_group,
        current_group=current_group,
    )
    if error:
        return None
    metadata = effective_value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD)
    if not isinstance(metadata, Mapping):
        return None
    recorded = metadata.get(SEMANTIC_ASSOCIATION_REBIND_FIELD)
    # Legacy v1 overlays predate this receipt.  They are usable only after the
    # exact archived/current groups independently reproduce it here; a copied
    # old association pin never receives a blanket exception.
    if expected is None:
        if recorded is not None:
            return None
        return dict(effective_value)
    if recorded is not None and not _semantic_association_rebind_matches(recorded, expected):
        return None
    result = dict(effective_value)
    result["semantic_association_sha256"] = expected[
        "current_semantic_association_sha256"
    ]
    refreshed_metadata = copy.deepcopy(dict(metadata))
    refreshed_metadata[SEMANTIC_ASSOCIATION_REBIND_FIELD] = expected
    result[SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD] = refreshed_metadata
    return _administrative_projection_rebind_loaded_response(
        result,
        current_group=current_group,
        administrative_projection_rebind=administrative_projection_rebind,
    )


def _semantic_association_rebind_receipt_error(value: object) -> str:
    """Validate transport shape before the loader recomputes the receipt."""

    if not isinstance(value, Mapping):
        return "is malformed"
    if value.get("schema") != SEMANTIC_ASSOCIATION_REBIND_SCHEMA:
        return "has an unsupported schema"
    for field in (
        "prior_response_semantic_association_sha256",
        "current_semantic_association_sha256",
    ):
        if not _sha256(value.get(field)):
            return f"has no valid `{field}`"
    descriptors = value.get("association_content_descriptors")
    if not isinstance(descriptors, list) or not descriptors:
        return "has no association-content descriptors"
    seen: set[str] = set()
    for entry in descriptors:
        if not isinstance(entry, Mapping):
            return "has a non-object association-content descriptor"
        content = entry.get("content")
        digest = _sha256(entry.get("content_sha256"))
        if not isinstance(content, Mapping) or not digest or digest != _canonical_digest(content):
            return "has an invalid association-content descriptor receipt"
        if digest in seen:
            return "has duplicate association-content descriptor receipts"
        seen.add(digest)
    exact_raw_group_identity = value.get(
        "recursive_parent_route_raw_group_identity"
    )
    if exact_raw_group_identity is not None:
        if error := _complete_reissue_raw_group_identity_error(
            exact_raw_group_identity
        ):
            return "has invalid recursive parent-route raw-group identity: " + error
    return ""


def _judgment_metadata_error(
    value: Mapping[str, Any],
    payload: Mapping[str, Any],
    group: Mapping[str, object],
    *,
    prior_audit_digest: str,
) -> str:
    if _payload_is_non_evidence(value):
        return "prior judgment is marked non-evidence"
    classification = str(
        value.get("classification")
        or value.get("judgment")
        or value.get("verdict")
        or value.get("status")
        or ""
    ).strip()
    if not classification:
        return "prior judgment lacks a classification"
    if (
        str(_effective(value, payload, "prompt_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return "prior judgment does not use the v10 source-record prompt"
    policy = str(
        _effective(value, payload, "source_record_policy_version") or ""
    ).strip()
    if policy and policy != SOURCE_RECORD_V10_PROMPT_VERSION:
        return "prior judgment records a different source-record policy"
    if _sha256(_effective(value, payload, "source_record_audit_sha256")) != prior_audit_digest:
        return "prior judgment is not tied to the archived prior raw receipt"
    validator = (
        value.get("validator")
        or value.get("model")
        or value.get("judge")
        or payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
    )
    timestamp = (
        value.get("validated_at")
        or value.get("timestamp")
        or value.get("generated_at")
        or payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
    )
    if not str(validator or "").strip() or not str(timestamp or "").strip():
        return "prior judgment lacks validator/timestamp metadata"

    for semantic_item in group.get("semantic_model_items") or []:
        if not isinstance(semantic_item, Mapping):
            return "prior semantic-model item is malformed"
        dimensions = semantic_item.get("dimensions")
        submitted = value.get("semantic_model_dimensions")
        if not isinstance(dimensions, list) or not isinstance(submitted, Mapping):
            return "prior semantic-model response is incomplete"
        for dimension in dimensions:
            if not isinstance(dimension, Mapping):
                return "prior semantic-model dimension is malformed"
            dimension_id = str(dimension.get("id") or "").strip()
            if not dimension_id or not isinstance(submitted.get(dimension_id), Mapping):
                return "prior semantic-model response is incomplete"
    return ""


def _materialize_prior_response(
    value: Mapping[str, Any], payload: Mapping[str, Any]
) -> dict[str, Any]:
    """Make inherited sidecar metadata explicit before loader authentication."""

    result = copy.deepcopy(dict(value))
    for field in (
        "prompt_version",
        "source_record_policy_version",
        "source_record_audit_sha256",
        "validator",
        "validated_at",
    ):
        if not result.get(field) and payload.get(field):
            result[field] = copy.deepcopy(payload[field])
    return result


def _descriptor_index(
    groups: Mapping[str, Mapping[str, object]]
) -> dict[str, list[tuple[str, Mapping[str, object]]]]:
    indexed: dict[str, list[tuple[str, Mapping[str, object]]]] = {}
    for key, group in groups.items():
        digest = _sha256(group.get("descriptor_sha256"))
        if digest:
            indexed.setdefault(digest, []).append((key, group))
    return indexed




def _overlay_without_integrity(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        str(key): value
        for key, value in payload.items()
        if str(key) != SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_INTEGRITY_FIELD
    }


def source_record_differential_revalidation_sha256(payload: Mapping[str, Any]) -> str:
    return _canonical_digest(_overlay_without_integrity(payload))






def _provenance_error(value: object, expected: Mapping[str, str]) -> str:
    if not isinstance(value, Mapping):
        return "is missing"
    for field, expected_value in expected.items():
        if str(value.get(field) or "") != str(expected_value):
            return f"has a different `{field}`"
    return ""


def _archived_source_status_projection_bridge_record_shape_error(value: object) -> str:
    if not isinstance(value, Mapping):
        return "is not an object"
    try:
        _repository_provenance_path(value.get("path"))
    except SourceRecordDifferentialRevalidationError as exc:
        return "has an invalid path: " + str(exc)
    for field in ("file_sha256", "receipt_sha256"):
        if not _sha256(value.get(field)):
            return f"has no valid `{field}`"
    return ""


def _source_free_recursive_structural_identity_shape_error(value: object) -> str:
    """Check serialized mapless-recursive witness shape before raw replay."""

    if not isinstance(value, Mapping):
        return "is not an object"
    if value.get("schema") != SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_SCHEMA:
        return "has an unsupported schema"
    if set(value) not in (
        {"schema", "raw_group_identity"},
        {"schema", "raw_group_identity", "semantic_content_identity"},
    ):
        return "has unsupported fields"
    raw_identity = value.get("raw_group_identity")
    if (
        not isinstance(raw_identity, Mapping)
        or set(raw_identity) != {"schema", "member_count", "canonical_sha256"}
        or raw_identity.get("schema")
        != SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_SCHEMA
        or not isinstance(raw_identity.get("member_count"), int)
        or raw_identity.get("member_count", 0) < 1
        or not _sha256(raw_identity.get("canonical_sha256"))
    ):
        return "has an invalid raw-group identity"
    content_identity = value.get("semantic_content_identity")
    if content_identity is not None and (
        not isinstance(content_identity, Mapping)
        or set(content_identity) != {"schema", "member_count", "canonical_sha256"}
        or content_identity.get("schema")
        != SOURCE_FREE_RECURSIVE_CONTENT_IDENTITY_SCHEMA
        or not isinstance(content_identity.get("member_count"), int)
        or content_identity.get("member_count", 0) < 1
        or not _sha256(content_identity.get("canonical_sha256"))
    ):
        return "has an invalid semantic-content identity"
    return ""


def _overlay_item_error(
    key: str, value: Mapping[str, Any], payload: Mapping[str, Any]
) -> str:
    metadata = value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD)
    if not isinstance(metadata, Mapping):
        return "is missing differential-revalidation provenance"
    if metadata.get("schema") != SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_SCHEMA:
        return "has an unsupported differential-revalidation schema"
    if (
        str(metadata.get("policy_version") or "").strip()
        != SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_POLICY_VERSION
    ):
        return "has an unsupported differential-revalidation policy"
    prior_key = str(metadata.get("prior_judgment_key") or "").strip()
    current_key = str(metadata.get("current_judgment_key") or "").strip()
    if not prior_key or not current_key:
        return "does not identify prior/current generated groups"
    descriptors: list[tuple[str, str]] = []
    for prefix in ("prior", "current"):
        descriptor = metadata.get(prefix + "_group_semantic_descriptor")
        digest = _sha256(metadata.get(prefix + "_group_semantic_descriptor_sha256"))
        if not isinstance(descriptor, Mapping) or not digest:
            return f"lacks {prefix} semantic descriptor provenance"
        if digest != _canonical_digest(descriptor):
            return f"has a malformed {prefix} semantic descriptor digest"
        descriptors.append((prefix, digest))
    bridge_record = metadata.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD)
    if bridge_record is None:
        if descriptors[0][1] != descriptors[1][1]:
            return "records different prior/current semantic descriptors"
        if (
            ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_FIELD in metadata
            or ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_SHA256_FIELD
            in metadata
        ):
            return "records a normalized archived source-status descriptor without a bridge"
    else:
        if error := _archived_source_status_projection_bridge_record_shape_error(
            bridge_record
        ):
            return "has invalid archived source-status bridge provenance: " + error
        top_level_bridge = payload.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD)
        if not isinstance(top_level_bridge, Mapping) or dict(bridge_record) != dict(
            top_level_bridge
        ):
            return "does not bind its archived source-status bridge to the overlay"
        normalized_descriptor = metadata.get(
            ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_FIELD
        )
        normalized_digest = _sha256(
            metadata.get(
                ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_SHA256_FIELD
            )
        )
        if (
            not isinstance(normalized_descriptor, Mapping)
            or not normalized_digest
            or normalized_digest != _canonical_digest(normalized_descriptor)
        ):
            return "has malformed normalized archived source-status descriptor provenance"
        if (
            normalized_digest != descriptors[1][1]
            or canonical_digest_payload(normalized_descriptor)
            != canonical_digest_payload(metadata.get("current_group_semantic_descriptor"))
        ):
            return "does not make the normalized archived descriptor exactly current"
    complete_reissue = SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD in payload
    complete_group_identity = metadata.get(
        SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_FIELD
    )
    if complete_reissue:
        if error := _complete_reissue_raw_group_identity_error(complete_group_identity):
            return error
    elif complete_group_identity is not None:
        return "records a complete receipt raw-group identity outside complete receipt mode"
    source_free_recursive_identity = metadata.get(
        SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD
    )
    if source_free_recursive_identity is not None:
        if complete_reissue:
            return "records a source-free recursive structural identity inside complete receipt mode"
        if bridge_record is not None:
            return "combines source-free recursive identity with a source-status bridge"
        if error := _source_free_recursive_structural_identity_shape_error(
            source_free_recursive_identity
        ):
            return "has invalid source-free recursive structural identity: " + error
    for field in ("prior_raw_audit", "current_raw_audit"):
        error = _provenance_error(metadata.get(field), payload.get(field, {}))
        if error:
            return f"{field} {error} from the overlay receipt"
    if not str(value.get("classification") or "").strip():
        return "has no inherited classification"
    if (
        str(value.get("prompt_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return "does not retain the v10 prompt version"
    if not _sha256(value.get("source_record_audit_sha256")):
        return "does not retain prior aggregate provenance"
    if not str(value.get("validator") or "").strip() or not str(
        value.get("validated_at") or ""
    ).strip():
        return "does not retain validator/timestamp metadata"
    rebind = metadata.get(SEMANTIC_ASSOCIATION_REBIND_FIELD)
    if "semantic_association_sha256" in value:
        # v1 overlays predate the persisted receipt.  The loader admits those
        # only after recomputing it from exact archived/current raw groups;
        # new overlays persist it and must have valid transport shape here.
        if rebind is not None and (
            error := _semantic_association_rebind_receipt_error(rebind)
        ):
            return "has invalid semantic-association rebind provenance: " + error
    elif rebind is not None:
        return "records semantic-association rebind provenance without a response pin"
    history = value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_HISTORY_FIELD)
    if history is not None and (
        not isinstance(history, list)
        or not history
        or not all(isinstance(entry, Mapping) for entry in history)
    ):
        return "has malformed prior differential-revalidation history"
    return ""


def _overlay_reuse_exclusions_error(
    payload: Mapping[str, Any],
    *,
    paper: str,
    current_raw_audit: Mapping[str, Any] | None = None,
) -> str:
    """Validate an optional reviewed exclusion artifact without name matching."""

    if SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_FIELD not in payload:
        return ""
    return _reuse_exclusions_record_error(
        payload.get(SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_FIELD),
        paper=paper,
        current_raw_audit=current_raw_audit,
    )


def _complete_reissue_identity_shape_error(identity: object) -> str:
    """Check the serialized shape before the loader recomputes it from raw."""

    if not isinstance(identity, Mapping):
        return "complete receipt reissue identity is not an object"
    if identity.get("schema") != SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_SCHEMA:
        return "complete receipt reissue has an unsupported identity schema"
    if (
        str(identity.get("mode") or "").strip()
        != SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_MODE
    ):
        return "complete receipt reissue has the wrong identity mode"
    for field in ("prior", "current"):
        if not isinstance(identity.get(field), Mapping):
            return f"complete receipt reissue lacks `{field}` reusable-section identity"
    aggregate = identity.get("allowed_aggregate_metadata_delta")
    if not isinstance(aggregate, Mapping):
        return "complete receipt reissue lacks aggregate metadata identity"
    for field in ("prior", "current"):
        if not isinstance(aggregate.get(field), Mapping):
            return f"complete receipt reissue lacks `{field}` aggregate metadata identity"
    return ""


def _complete_reissue_attested_current_revalidation_shape_error(value: object) -> str:
    """Check only serialized provenance shape before raw-side revalidation."""

    if not isinstance(value, Mapping):
        return "complete receipt reissue attested current-revalidation provenance is not an object"
    if value.get("schema") != SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_SCHEMA:
        return "complete receipt reissue attested current-revalidation provenance has an unsupported schema"
    for field in ("candidate_sidecar", "attestation"):
        record = value.get(field)
        if not isinstance(record, Mapping):
            return f"complete receipt reissue attested current-revalidation lacks `{field}` provenance"
        try:
            _repository_provenance_path(record.get("path"))
        except SourceRecordDifferentialRevalidationError as exc:
            return (
                "complete receipt reissue attested current-revalidation has invalid "
                f"`{field}` path: {exc}"
            )
        if not _sha256(record.get("file_sha256")):
            return (
                "complete receipt reissue attested current-revalidation has malformed "
                f"`{field}` file hash"
            )
    if not _sha256(value.get("archived_raw_source_record_audit_sha256")):
        return "complete receipt reissue attested current-revalidation has no archived raw receipt"
    return ""


def source_record_differential_revalidation_overlay_error(
    payload: object, *, paper: str
) -> str:
    """Validate serialized overlay transport before per-item current checks."""

    if not isinstance(payload, Mapping):
        return "differential revalidation overlay is not an object"
    if payload.get("schema") != 1:
        return "differential revalidation overlay lacks sidecar schema 1"
    if (
        str(payload.get("artifact_kind") or "").strip()
        != SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ARTIFACT_KIND
    ):
        return "differential revalidation overlay has the wrong artifact kind"
    if payload.get("revalidation_schema") != SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_SCHEMA:
        return "differential revalidation overlay has an unsupported schema"
    if (
        str(payload.get("revalidation_policy_version") or "").strip()
        != SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_POLICY_VERSION
    ):
        return "differential revalidation overlay has an unsupported policy"
    if payload.get("paper") != paper:
        return "differential revalidation overlay belongs to another paper"
    if (
        str(payload.get("prompt_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
        or str(payload.get("source_record_policy_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return "differential revalidation overlay does not record the v10 prompt family"
    if _payload_is_non_evidence(payload):
        return "differential revalidation overlay is marked non-evidence"
    integrity = _sha256(payload.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_INTEGRITY_FIELD))
    if not integrity:
        return "differential revalidation overlay lacks an integrity digest"
    if integrity != source_record_differential_revalidation_sha256(payload):
        return "differential revalidation overlay integrity digest does not match"
    for field in ("prior_raw_audit", "current_raw_audit"):
        provenance = payload.get(field)
        if not isinstance(provenance, Mapping):
            return f"differential revalidation overlay lacks {field} provenance"
        try:
            _repository_provenance_path(provenance.get("path"))
        except SourceRecordDifferentialRevalidationError as exc:
            return f"differential revalidation overlay has invalid {field} path: {exc}"
        for digest_field in (
            "file_sha256",
            "source_record_audit_sha256",
            "source_record_audit_integrity_sha256",
        ):
            if not _sha256(provenance.get(digest_field)):
                return (
                    "differential revalidation overlay has malformed "
                    f"{field}.{digest_field}"
                )
    prior_judgments = payload.get("prior_judgments")
    if not isinstance(prior_judgments, Mapping) or not _sha256(
        prior_judgments.get("file_sha256")
    ):
        return "differential revalidation overlay lacks prior-sidecar provenance"
    try:
        _repository_provenance_path(prior_judgments.get("path"))
    except SourceRecordDifferentialRevalidationError as exc:
        return f"differential revalidation overlay has invalid prior-sidecar path: {exc}"
    if error := _overlay_reuse_exclusions_error(payload, paper=paper):
        return "differential revalidation overlay has invalid reuse exclusions: " + error
    if ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD in payload and (
        error := _archived_source_status_projection_bridge_record_shape_error(
            payload.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD)
        )
    ):
        return "differential revalidation overlay has invalid archived source-status bridge: " + error
    if SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD in payload and (
        error := _complete_reissue_identity_shape_error(
            payload.get(SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD)
        )
    ):
        return "differential revalidation overlay has invalid complete receipt reissue: " + error
    if (
        SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_FIELD in payload
        and SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD not in payload
    ):
        return "differential revalidation overlay records attested current revalidation outside complete receipt mode"
    if SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_FIELD in payload and (
        error := _complete_reissue_attested_current_revalidation_shape_error(
            payload.get(SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_FIELD)
        )
    ):
        return "differential revalidation overlay has invalid attested current revalidation: " + error
    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        return "differential revalidation overlay items are not an object"
    for raw_key, raw_value in raw_items.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_value, Mapping):
            return "differential revalidation overlay has a malformed item"
        item_error = _overlay_item_error(key, raw_value, payload)
        if item_error:
            return f"differential revalidation item `{key}` {item_error}"
    return ""


def _archived_overlay_items_error(
    payload: Mapping[str, Any],
    *,
    prior_raw_audit: Mapping[str, Any],
    prior_judgments: Mapping[str, Any],
    prior_audit_digest: str,
) -> str:
    """Reauthenticate every serialized response against archived item evidence.

    This check is deliberately stronger than the overlay's transport check.
    It reads the exact sidecar bytes named by the overlay, recovers the prior
    group from the exact raw receipt, and re-runs the same metadata/group
    checks used at overlay issuance.  The serialized inherited response must
    then be byte-for-byte equivalent as JSON content to the archived response
    after only root metadata has been materialized.  Thus a stale sidecar root
    can never cause a blanket reuse, and a copied or altered overlay response
    cannot be accepted merely because it retained a prior storage key.
    """

    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        return "overlay has no item ledger"
    prior_responses = prior_judgments.get("items") or prior_judgments.get(
        "field_judgments"
    )
    if not isinstance(prior_responses, Mapping):
        return "archived sidecar has no item ledger"
    prior_groups, prior_group_errors = OBLIGATIONS.raw_source_record_obligation_groups(
        prior_raw_audit
    )
    if not prior_groups:
        return "archived raw audit has no generated judgment groups"
    complete_reissue = SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD in payload

    for serialized_key, serialized_value in raw_items.items():
        key = str(serialized_key or "").strip()
        if not key or not isinstance(serialized_value, Mapping):
            return "overlay has a malformed serialized item"
        metadata = serialized_value.get(
            SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD
        )
        if not isinstance(metadata, Mapping):
            return f"{key}: serialized item has no differential provenance"
        prior_key = str(metadata.get("prior_judgment_key") or "").strip()
        if not prior_key:
            return f"{key}: serialized item has no prior judgment key"
        if complete_reissue and str(
            metadata.get("current_judgment_key") or ""
        ).strip() != key:
            return f"{key}: complete receipt reissue changed its raw-group storage address"
        prior_group = prior_groups.get(prior_key)
        if prior_key in prior_group_errors or not isinstance(prior_group, Mapping):
            return f"{key}: archived prior group is missing or malformed"

        recorded_descriptor = metadata.get("prior_group_semantic_descriptor")
        recorded_descriptor_sha = _sha256(
            metadata.get("prior_group_semantic_descriptor_sha256")
        )
        actual_descriptor = prior_group.get("descriptor")
        actual_descriptor_sha = _sha256(prior_group.get("descriptor_sha256"))
        if (
            not isinstance(recorded_descriptor, Mapping)
            or not recorded_descriptor_sha
            or not isinstance(actual_descriptor, Mapping)
            or not actual_descriptor_sha
            or recorded_descriptor_sha != actual_descriptor_sha
            or recorded_descriptor_sha != _canonical_digest(recorded_descriptor)
            or canonical_digest_payload(recorded_descriptor)
            != canonical_digest_payload(actual_descriptor)
        ):
            return f"{key}: serialized prior semantic descriptor no longer matches archived raw"
        if complete_reissue:
            if group_identity_error := _complete_reissue_raw_group_identity_error(
                metadata.get(SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_FIELD),
                prior_group=prior_group,
            ):
                return f"{key}: {group_identity_error}"
        archived_response = prior_responses.get(prior_key)
        if not isinstance(archived_response, Mapping):
            return f"{key}: archived sidecar has no prior response"
        elif reuse_error := _group_differential_reuse_error(
            prior_group, response=archived_response
        ):
            return f"{key}: archived prior group is not reusable: {reuse_error}"
        recorded_source_free_recursive_identity = metadata.get(
            SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD
        )
        if recorded_source_free_recursive_identity is not None:
            if identity_error := _source_free_recursive_structural_identity_error(
                recorded_source_free_recursive_identity,
                group=prior_group,
                response=archived_response,
            ):
                return (
                    f"{key}: archived prior source-free recursive structural "
                    "identity is invalid: " + identity_error
                )
        if metadata_error := _judgment_metadata_error(
            archived_response,
            prior_judgments,
            prior_group,
            prior_audit_digest=prior_audit_digest,
        ):
            return f"{key}: archived prior response is invalid: {metadata_error}"
        if complete_reissue and (
            association_error := _complete_reissue_response_semantic_association_error(
                archived_response, prior_group
            )
        ):
            return f"{key}: archived prior response is invalid: {association_error}"

        expected = _materialize_prior_response(archived_response, prior_judgments)
        observed = dict(serialized_value)
        observed.pop(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD, None)
        # A new overlay keeps an earlier overlay receipt in an ordered history.
        # Restore the immediate prior receipt before comparing to the archived
        # response.  The current semantic descriptor is independently checked
        # above, so this is provenance preservation rather than an identity
        # heuristic based on a storage key or route name.
        history = observed.pop(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_HISTORY_FIELD, None)
        if history is not None:
            if not isinstance(history, list) or not history:
                return f"{key}: serialized response has malformed differential history"
            restored_history = copy.deepcopy(history)
            prior_metadata = restored_history.pop()
            if not isinstance(prior_metadata, Mapping):
                return f"{key}: serialized response has malformed differential history"
            observed[SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD] = dict(
                prior_metadata
            )
            if restored_history:
                observed[SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_HISTORY_FIELD] = (
                    restored_history
                )
        if canonical_digest_payload(observed) != canonical_digest_payload(expected):
            return f"{key}: serialized response differs from the archived materialized response"
    return ""


def _load_authenticated_source_record_differential_prior_raw(
    payload: Mapping[str, Any], *, paper: str
) -> tuple[dict[str, Any] | None, str]:
    """Return exact-byte-authenticated archived raw evidence, or an error.

    A historical sidecar can have a stale *root* aggregate receipt after a
    narrow earlier update while individual responses already carry the exact
    prior receipt.  That root value is not enough to discard those individual
    judgments, nor is it enough to trust them.  Every serialized overlay item
    is therefore revalidated below against the exact archived sidecar response
    and the exact archived raw group before this function admits the archive.
    """

    prior_provenance = payload.get("prior_raw_audit")
    prior_judgments_provenance = payload.get("prior_judgments")
    if not isinstance(prior_provenance, Mapping) or not isinstance(
        prior_judgments_provenance, Mapping
    ):
        return None, "overlay archive provenance is malformed"
    try:
        prior_raw_path = _repository_provenance_path(prior_provenance.get("path"))
        prior_judgments_path = _repository_provenance_path(
            prior_judgments_provenance.get("path")
        )
        prior_raw = _read_json_object(prior_raw_path)
        prior_judgments = _read_json_object(prior_judgments_path)
        actual_prior_provenance = _raw_audit_provenance(prior_raw, prior_raw_path)
    except (OSError, SourceRecordDifferentialRevalidationError) as exc:
        return None, f"could not authenticate archived differential evidence: {exc}"
    if _raw_audit_error(prior_raw, paper=paper, label="archived prior"):
        return None, "archived prior raw audit is not an admissible v10 receipt"
    if _provenance_error(prior_provenance, actual_prior_provenance):
        return None, "archived prior raw audit bytes or receipt differ from the overlay"
    if _file_sha256(prior_judgments_path) != str(
        prior_judgments_provenance.get("file_sha256") or ""
    ):
        return None, "archived prior judgment sidecar bytes differ from the overlay"
    if (
        prior_judgments.get("schema") != 1
        or prior_judgments.get("paper") != paper
        or _payload_is_non_evidence(prior_judgments)
        or str(prior_judgments.get("prompt_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return None, "archived prior judgment sidecar is not admissible v10 evidence"
    # The overlay itself must state the exact prior receipt even if the legacy
    # sidecar root is stale.  Individual overlay candidates are checked below;
    # no name- or root-level fallback is accepted.
    if _sha256(prior_judgments_provenance.get("source_record_audit_sha256")) != _sha256(
        prior_provenance.get("source_record_audit_sha256")
    ):
        return None, "overlay prior-sidecar provenance is not tied to the archived raw receipt"
    if not _sha256(prior_judgments.get("source_record_audit_sha256")):
        return None, "archived prior judgment sidecar has no aggregate receipt"
    if error := _archived_overlay_items_error(
        payload,
        prior_raw_audit=prior_raw,
        prior_judgments=prior_judgments,
        prior_audit_digest=_sha256(prior_provenance.get("source_record_audit_sha256")),
    ):
        return None, "archived differential response is not individually authenticated: " + error
    return prior_raw, ""






def _source_record_differential_revalidation_item_current_from_groups(
    value: Mapping[str, Any],
    *,
    current_provenance: Mapping[str, str],
    groups: Mapping[str, Mapping[str, object]],
    descriptor_index: Mapping[str, list[tuple[str, Mapping[str, object]]]],
    complete_reissue: bool = False,
    prior_groups: Mapping[str, Mapping[str, object]] | None = None,
    archived_source_status_bridge: ValidatedArchivedSourceStatusProjectionBridge | None = None,
) -> tuple[str, bool]:
    """Check one inherited response against an already-authenticated raw index.

    The public single-item helper remains useful for callers that possess only
    one response.  Batch loaders must not repeat receipt validation or rebuild
    the potentially large generated-obligation projection for every response.
    """

    metadata = value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD)
    if not isinstance(metadata, Mapping):
        return "", False
    if _current_raw_provenance_error(
        metadata.get("current_raw_audit"), current_provenance
    ):
        return "", False
    descriptor = metadata.get("current_group_semantic_descriptor")
    descriptor_sha = _sha256(metadata.get("current_group_semantic_descriptor_sha256"))
    if not isinstance(descriptor, Mapping) or not descriptor_sha:
        return "", False
    if descriptor_sha != _canonical_digest(descriptor):
        return "", False
    if complete_reissue:
        # This path deliberately does not resolve descriptor duplicates. The
        # enclosing complete-reissue receipt and the per-item raw-group
        # identity instead bind this response to the same exact raw ledger
        # address. A renamed address is rejected by the archived-side check.
        current_key = str(metadata.get("current_judgment_key") or "").strip()
        current_group = groups.get(current_key)
        if not current_key or not isinstance(current_group, Mapping):
            return "", False
        if canonical_digest_payload(current_group.get("descriptor")) != canonical_digest_payload(
            descriptor
        ):
            return "", False
        if _complete_reissue_raw_group_identity_error(
            metadata.get(SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_FIELD),
            current_group=current_group,
        ):
            return "", False
        if _complete_reissue_response_semantic_association_error(value, current_group):
            return "", False
        return current_key, True
    bridge_record = metadata.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD)
    if bridge_record is not None:
        if (
            not isinstance(bridge_record, Mapping)
            or not isinstance(archived_source_status_bridge, ValidatedArchivedSourceStatusProjectionBridge)
            or prior_groups is None
        ):
            return "", False
        prior_key = str(metadata.get("prior_judgment_key") or "").strip()
        prior_group = prior_groups.get(prior_key)
        if not prior_key or not isinstance(prior_group, Mapping):
            return "", False
        normalized_prior_group, changed, normalized_error = (
            _archived_source_status_projection_normalized_group(
                prior_group, archived_source_status_bridge
            )
        )
        normalized_descriptor = metadata.get(
            ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_FIELD
        )
        normalized_digest = _sha256(
            metadata.get(
                ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_SHA256_FIELD
            )
        )
        if (
            normalized_error
            or normalized_prior_group is None
            or not changed
            or not isinstance(normalized_descriptor, Mapping)
            or not normalized_digest
            or normalized_digest != _canonical_digest(normalized_descriptor)
            or canonical_digest_payload(normalized_prior_group.get("descriptor"))
            != canonical_digest_payload(normalized_descriptor)
        ):
            return "", False
        candidates = [
            (key, group)
            for key, group in descriptor_index.get(descriptor_sha, [])
            if canonical_digest_payload(group.get("descriptor"))
            == canonical_digest_payload(descriptor)
        ]
        if len(candidates) != 1:
            return "", False
        current_key, current_group = candidates[0]
        if canonical_digest_payload(normalized_prior_group.get("descriptor")) != canonical_digest_payload(
            current_group.get("descriptor")
        ):
            return "", False
        if _group_differential_reuse_error(current_group, response=value):
            return "", False
        return current_key, True
    source_free_recursive_identity = metadata.get(
        SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD
    )
    descriptor_candidates = [
        (key, group)
        for key, group in descriptor_index.get(descriptor_sha, [])
        if canonical_digest_payload(group.get("descriptor"))
        == canonical_digest_payload(descriptor)
    ]
    content_identity = (
        source_free_recursive_identity.get("semantic_content_identity")
        if isinstance(source_free_recursive_identity, Mapping)
        else None
    )
    candidates = (
        _source_free_recursive_content_identity_matches(
            descriptor_candidates, target=content_identity
        )
        if isinstance(content_identity, Mapping)
        else descriptor_candidates
    )
    if len(candidates) != 1:
        return "", False
    current_key, current_group = candidates[0]
    if isinstance(content_identity, Mapping) and _group_has_semantic_model_obligation(
        current_group
    ):
        return "", False
    if _group_differential_reuse_error(current_group, response=value):
        return "", False
    if source_free_recursive_identity is not None:
        if prior_groups is None:
            return "", False
        prior_key = str(metadata.get("prior_judgment_key") or "").strip()
        prior_group = prior_groups.get(prior_key)
        if not prior_key or not isinstance(prior_group, Mapping):
            return "", False
        if isinstance(content_identity, Mapping) and _group_has_semantic_model_obligation(
            prior_group
        ):
            return "", False
        if _source_free_recursive_structural_identity_error(
            source_free_recursive_identity,
            group=prior_group,
            response=value,
        ):
            return "", False
        current_identity, current_identity_error = (
            _source_free_recursive_structural_identity(
                current_group, response=value
            )
        )
        expected_current_identity = (
            current_identity
            if isinstance(content_identity, Mapping) or current_identity is None
            else {
                "schema": current_identity["schema"],
                "raw_group_identity": current_identity["raw_group_identity"],
            }
        )
        if (
            current_identity_error
            or current_identity is None
            or canonical_digest_payload(source_free_recursive_identity)
            != canonical_digest_payload(expected_current_identity)
        ):
            return "", False
    return current_key, True


def is_loaded_source_record_differential_revalidation_item(value: object) -> bool:
    return bool(
        isinstance(value, _LoadedSourceRecordDifferentialRevalidationItem)
        and value._source_record_differential_revalidation_loader_token
        is _LOADED_OVERLAY_ITEM_SENTINEL
        and isinstance(
            value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD), Mapping
        )
    )




def copy_loaded_source_record_differential_revalidation_item(
    value: Mapping[str, Any], updates: Mapping[str, Any] | None = None
) -> dict[str, Any]:
    copied: dict[str, Any] = dict(value)
    if updates is not None:
        copied.update(updates)
    if is_loaded_source_record_differential_revalidation_item(value):
        return _LoadedSourceRecordDifferentialRevalidationItem(copied)
    return copied


def source_record_differential_revalidation_overlay_path(paper_dir: Path) -> Path:
    return paper_dir / "audit" / SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_FILENAME


def _canonical_current_administrative_projection_rebind_context(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    current_raw_audit_path: Path,
) -> tuple[ValidatedAdministrativeProjectionRebind | None, str]:
    """Load only the default receipt bound to the canonical receiving raw audit.

    Differential overlays may also be checked against explicit historical raw
    files.  Do not make a canonical receipt an accidental waiver for those
    archives: automatic transport is limited to the current canonical audit.
    A caller that needs a historical transport must issue a separate
    receipt-bound workflow rather than inheriting this one by path resemblance.
    """

    canonical_raw_path = paper_dir / "audit" / "source_record_audit.json"
    try:
        if current_raw_audit_path.resolve() != canonical_raw_path.resolve():
            return None, ""
    except OSError:
        return None, ""
    receipt_path = (
        paper_dir / "audit" / SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
    )
    if not receipt_path.exists():
        return None, ""
    statement_map_path = paper_dir / "audit" / "paper_statement_map.json"
    try:
        statement_map = _read_json_object(statement_map_path)
    except SourceRecordDifferentialRevalidationError as exc:
        return None, "could not load current source map for administrative rebind: " + str(exc)
    context, _loaded_path, error = load_administrative_projection_rebind_context(
        paper=paper,
        paper_dir=paper_dir,
        raw_audit_path=current_raw_audit_path,
        raw_audit=current_raw_audit,
        statement_map_path=statement_map_path,
        statement_map=statement_map,
        receipt_path=receipt_path,
    )
    if error:
        return None, error
    if context is not None and not isinstance(
        context, ValidatedAdministrativeProjectionRebind
    ):
        return None, "administrative projection rebind did not yield a validated context"
    return context, ""


def load_current_source_record_differential_revalidation_items(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    path: Path | None = None,
    current_raw_audit_path: Path | None = None,
    current_raw_audit_provenance_path: Path | None = None,
) -> dict[str, dict[str, Any]]:
    """Load only authenticated overlay responses still exact for current raw.

    ``current_raw_audit_path`` is normally the canonical raw-audit path.  An
    explicit path permits an immutable historical current receipt to be
    rechecked without swapping the paper's live canonical files.  When that
    archived byte copy was originally issued at a different canonical path,
    ``current_raw_audit_provenance_path`` supplies that immutable logical
    receipt path.  Both paths authenticate evidence only; semantic matching
    still uses the complete generated descriptor groups in
    ``current_raw_audit``.
    """

    overlay_path = path or source_record_differential_revalidation_overlay_path(paper_dir)
    try:
        payload = json.loads(overlay_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if source_record_differential_revalidation_overlay_error(payload, paper=paper):
        return {}
    prior_raw_audit, archive_error = (
        _load_authenticated_source_record_differential_prior_raw(payload, paper=paper)
    )
    if archive_error or prior_raw_audit is None:
        return {}
    complete_reissue = SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD in payload
    if complete_reissue:
        try:
            prior_judgments_provenance = payload.get("prior_judgments")
            if not isinstance(prior_judgments_provenance, Mapping):
                return {}
            candidate_sidecar_path = _repository_provenance_path(
                prior_judgments_provenance.get("path")
            )
            candidate_sidecar = _read_json_object(candidate_sidecar_path)
        except (OSError, SourceRecordDifferentialRevalidationError):
            return {}
        candidate_metadata = candidate_sidecar.get("current_semantic_revalidation")
        attested_record = payload.get(
            SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_FIELD
        )
        if isinstance(candidate_metadata, Mapping):
            if attested_record is None:
                return {}
            if _complete_reissue_attested_current_revalidation_error(
                attested_record,
                paper=paper,
                paper_dir=paper_dir,
                raw_audit=prior_raw_audit,
                candidate_sidecar=candidate_sidecar,
                candidate_sidecar_path=candidate_sidecar_path,
            ):
                return {}
        elif attested_record is not None:
            return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        return {}
    if _raw_audit_error(current_raw_audit, paper=paper, label="current"):
        return {}
    if _overlay_reuse_exclusions_error(
        payload, paper=paper, current_raw_audit=current_raw_audit
    ):
        return {}
    receipt_path = current_raw_audit_path or (
        paper_dir / "audit" / "source_record_audit.json"
    )
    if not receipt_path.is_file():
        return {}
    try:
        # An explicit archive path is evidence, not merely a convenient file
        # location.  Refuse a caller-supplied in-memory receipt whose complete
        # JSON content differs from the archived bytes; otherwise a stale or
        # substituted archive could inherit the live mapping's provenance.
        if current_raw_audit_path is not None:
            archived_current = _read_json_object(receipt_path)
            if canonical_digest_payload(archived_current) != canonical_digest_payload(
                current_raw_audit
            ):
                return {}
        current_provenance = _raw_audit_provenance(current_raw_audit, receipt_path)
        if current_raw_audit_provenance_path is not None:
            current_provenance["path"] = _stable_provenance_path(
                current_raw_audit_provenance_path
            )
    except (OSError, SourceRecordDifferentialRevalidationError):
        return {}
    archived_source_status_bridge: ValidatedArchivedSourceStatusProjectionBridge | None = None
    if ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD in payload:
        if complete_reissue:
            return {}
        bridge_record = payload.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD)
        if not isinstance(bridge_record, Mapping):
            return {}
        try:
            prior_raw_record = payload.get("prior_raw_audit")
            prior_sidecar_record = payload.get("prior_judgments")
            if not isinstance(prior_raw_record, Mapping) or not isinstance(
                prior_sidecar_record, Mapping
            ):
                return {}
            prior_raw_path = _repository_provenance_path(prior_raw_record.get("path"))
            prior_judgments_path = _repository_provenance_path(
                prior_sidecar_record.get("path")
            )
            prior_judgments = _read_json_object(prior_judgments_path)
            bridge_path = _repository_provenance_path(bridge_record.get("path"))
        except (OSError, SourceRecordDifferentialRevalidationError):
            return {}
        archived_source_status_bridge, _bridge_actual_record, bridge_error = (
            _archived_source_status_projection_bridge_context(
                bridge_path=bridge_path,
                paper=paper,
                paper_dir=paper_dir,
                prior_raw_audit=prior_raw_audit,
                prior_raw_audit_path=prior_raw_path,
                prior_judgments=prior_judgments,
                prior_judgments_path=prior_judgments_path,
                current_raw_audit=current_raw_audit,
                current_raw_audit_path=receipt_path,
                recorded=bridge_record,
            )
        )
        if bridge_error or archived_source_status_bridge is None:
            return {}
    administrative_projection_rebind, rebind_error = (
        _canonical_current_administrative_projection_rebind_context(
            paper_dir,
            paper,
            current_raw_audit,
            receipt_path,
        )
    )
    if rebind_error:
        return {}
    groups, group_errors = OBLIGATIONS.raw_source_record_obligation_groups(
        current_raw_audit
    )
    if group_errors:
        return {}
    prior_groups: dict[str, dict[str, object]] | None = None
    prior_group_errors: dict[str, str] | None = None
    has_source_free_recursive_identity = any(
        isinstance(value, Mapping)
        and isinstance(
            value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD), Mapping
        )
        and value[SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD].get(
            SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD
        )
        is not None
        for value in raw_items.values()
    )
    if (
        complete_reissue
        or archived_source_status_bridge is not None
        or has_source_free_recursive_identity
    ):
        prior_groups, prior_group_errors = OBLIGATIONS.raw_source_record_obligation_groups(
            prior_raw_audit
        )
        if prior_group_errors:
            return {}
    if complete_reissue:
        if payload.get("manual_review_required") != []:
            return {}
        if set(raw_items) != set(groups):
            return {}
        complete_reissue_error = _complete_reusable_section_identity_error(
            payload.get(SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD),
            prior_raw_audit=prior_raw_audit,
            prior_groups=prior_groups,
            current_raw_audit=current_raw_audit,
            current_groups=groups,
        )
        if complete_reissue_error:
            return {}
    descriptor_index = _descriptor_index(groups)
    if SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_FIELD in payload:
        record = payload.get(SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_FIELD)
        if not isinstance(record, Mapping):
            return {}
        try:
            reasons = _reuse_exclusion_reason_ledger(
                record.get(
                    SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD
                ),
                label="overlay reuse-exclusions provenance",
            )
        except SourceRecordDifferentialRevalidationError:
            return {}
        if _reuse_exclusions_current_group_error(reasons, descriptor_index):
            return {}
    out: dict[str, dict[str, Any]] = {}
    for raw_value in raw_items.values():
        if not isinstance(raw_value, Mapping):
            continue
        current_key, is_current = _source_record_differential_revalidation_item_current_from_groups(
            raw_value,
            current_provenance=current_provenance,
            groups=groups,
            descriptor_index=descriptor_index,
            complete_reissue=complete_reissue,
            prior_groups=prior_groups,
            archived_source_status_bridge=archived_source_status_bridge,
        )
        if not is_current or not current_key or current_key in out:
            continue
        materialized: dict[str, Any] | None = dict(raw_value)
        metadata = raw_value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD)
        uses_archived_source_status_bridge = bool(
            isinstance(metadata, Mapping)
            and metadata.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD) is not None
        )
        if (
            ("semantic_association_sha256" in raw_value or uses_archived_source_status_bridge)
            and not complete_reissue
        ):
            if prior_groups is None:
                prior_groups, prior_group_errors = OBLIGATIONS.raw_source_record_obligation_groups(
                    prior_raw_audit
                )
            prior_key = (
                str(metadata.get("prior_judgment_key") or "").strip()
                if isinstance(metadata, Mapping)
                else ""
            )
            prior_group = prior_groups.get(prior_key) if prior_groups else None
            current_group = groups.get(current_key)
            prior_descriptor = (
                metadata.get("prior_group_semantic_descriptor")
                if isinstance(metadata, Mapping)
                else None
            )
            if (
                not prior_key
                or prior_group_errors is None
                or prior_key in prior_group_errors
                or not isinstance(prior_group, Mapping)
                or not isinstance(current_group, Mapping)
                or not isinstance(prior_descriptor, Mapping)
                or canonical_digest_payload(prior_group.get("descriptor"))
                != canonical_digest_payload(prior_descriptor)
            ):
                continue
            effective_prior_group: Mapping[str, object] = prior_group
            if uses_archived_source_status_bridge:
                if archived_source_status_bridge is None:
                    continue
                effective_prior_group, changed, normalized_error = (
                    _archived_source_status_projection_normalized_group(
                        prior_group, archived_source_status_bridge
                    )
                )
                normalized_descriptor = (
                    metadata.get(
                        ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_FIELD
                    )
                    if isinstance(metadata, Mapping)
                    else None
                )
                if (
                    normalized_error
                    or effective_prior_group is None
                    or not changed
                    or not isinstance(normalized_descriptor, Mapping)
                    or canonical_digest_payload(effective_prior_group.get("descriptor"))
                    != canonical_digest_payload(normalized_descriptor)
                ):
                    continue
            materialized = _materialize_current_semantic_association_rebind(
                raw_value,
                prior_group=effective_prior_group,
                current_group=current_group,
                administrative_projection_rebind=administrative_projection_rebind,
                archived_source_status_bridge=(
                    archived_source_status_bridge
                    if uses_archived_source_status_bridge
                    else None
                ),
            )
        if materialized is None:
            continue
        out[current_key] = _LoadedSourceRecordDifferentialRevalidationItem(materialized)
    if complete_reissue and set(out) != set(groups):
        return {}
    return out
