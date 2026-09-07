#!/usr/bin/env python3
"""Fast, fail-closed checks for paper-audit evidence integrity.

This complements ``audit_repository.py``.  It deliberately avoids Lean builds so
it can run on every push and pull request.  The checks target evidence failures
that can otherwise make a semantic audit look green: placeholder source
locations, divergent duplicate sidecars, unsupported status promotion, missing
source-artifact hashes, non-independent audit lanes, and untraceable human-review
counts.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import json
import re
import shlex
import subprocess
import sys
import tarfile
import threading
import time
from dataclasses import asdict, dataclass, field as dataclass_field
from pathlib import Path
from types import MappingProxyType
from typing import Any, Iterable, Mapping, MutableMapping

# Direct-file and package execution share one canonical import namespace. The
# issuer aliases below preserve the supported public module identities; all
# dependency imports themselves resolve through the repository's `scripts`
# package so an exact transaction cannot encounter duplicate capability types.
if __package__ in {None, ""}:
    repository_root = str(Path(__file__).resolve().parents[1])
    if repository_root not in sys.path:
        sys.path.insert(0, repository_root)


def _register_supported_import_aliases() -> None:
    """Keep every supported import path at one evidence-context issuer.

    Several source-record transport lanes import this module lazily so they can
    validate an in-process ``EvidenceRunContext`` capability.  The supported
    entrypoint/module identities are ``__main__`` (direct CLI),
    ``scripts.audit_evidence_integrity`` (package import), and
    ``audit_evidence_integrity`` (top-level import from ``scripts``).  Publish
    whichever supported origin loaded first under both module aliases before a
    lazy lane can load.  A pre-existing distinct issuer is an unsupported
    hybrid invocation and fails closed rather than silently mixing opaque
    capabilities.
    """

    if __name__ not in {
        "__main__",
        "scripts.audit_evidence_integrity",
        "audit_evidence_integrity",
    }:
        return
    module = sys.modules.get(__name__)
    if module is None:  # pragma: no cover - Python registers an executing module.
        raise RuntimeError("evidence issuer has no executing module")
    for alias in ("scripts.audit_evidence_integrity", "audit_evidence_integrity"):
        existing = sys.modules.get(alias)
        if existing is not None and existing is not module:
            raise RuntimeError(
                "evidence issuer cannot share an interpreter with "
                f"a distinct `{alias}` issuer"
            )
        sys.modules[alias] = module
    # ``from scripts import audit_evidence_integrity`` may return an already
    # bound parent-package attribute without consulting the alias above.  Check
    # and bind that second import cache explicitly so a stale attribute cannot
    # bypass the exact module/class identity used by opaque contexts.
    parent = sys.modules.get("scripts")
    if parent is not None:
        missing = object()
        existing_child = getattr(parent, "audit_evidence_integrity", missing)
        if existing_child is not missing and existing_child is not module:
            raise RuntimeError(
                "evidence issuer cannot share an interpreter with a distinct "
                "`scripts.audit_evidence_integrity` package attribute"
            )
        try:
            setattr(parent, "audit_evidence_integrity", module)
        except (AttributeError, TypeError) as exc:
            raise RuntimeError(
                "evidence issuer cannot bind the `scripts.audit_evidence_integrity` "
                "package attribute"
            ) from exc


_register_supported_import_aliases()


# Source-only validators have one owner; these remain supported exports.
from scripts.source_manifest_validation import (
    AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE,
    COMPONENT_LEVEL_EVIDENCE_ONLY_SCOPE_ROLE,
    CONDITIONAL_PROBABILITY_COMPOSITION_FIELD,
    CONDITIONAL_PROBABILITY_COMPOSITION_SEMANTIC_SHAPE,
    LEGACY_SOURCE_CLAIM_ATOM_IDENTITY_SCHEMA as LEGACY_SOURCE_CLAIM_ATOM_IDENTITY_SCHEMA,
    PLAIN_FORMALIZED,
    SOURCE_CLAIM_ATOMS_KEY,
    SOURCE_CLAIM_ATOMS_SCHEMA,
    SOURCE_CLAIM_ATOMS_SCHEMA_KEY,
    SOURCE_CLAIM_ATOM_IDENTITY_SCHEMA_FIELD as SOURCE_CLAIM_ATOM_IDENTITY_SCHEMA_FIELD,
    SOURCE_PROOF_MODEL_CONVENTION_REQUIRED_FIELDS,
    SOURCE_SPEC_CORRESPONDENCE_KEY,
    SOURCE_SPEC_CORRESPONDENCE_NONCLAIM_STATUSES,
    SOURCE_SPEC_CORRESPONDENCE_SCHEMA,
    SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY,
    WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE,
    _source_claim_atoms_current_quote_binding_errors,
    _source_map_proof_obligation_items,
    author_approved_corrected_scope,
    canonical_artifact_source_span_errors,
    canonical_json_digest,
    canonical_json_payload,
    canonical_source_map_has_source_defect_links,
    canonical_source_proof_ledger_has_defects,
    corrected_model_scope_role,
    explicit_source_routes_enabled,
    item_entries,
    repaired_source_defect_route_preflight_findings,
    semantic_contract_validation_errors,
    source_claim_atoms_validation_errors,
    source_proof_fidelity_config,
    source_proof_fidelity_ledger_findings,
    source_spec_correspondence_inventory_inputs,
    source_spec_correspondence_required,
    validated_presentation_alias_contract_exemptions,
    validated_subsumed_result_contract_exemptions,
    ROOT as ROOT,
    CLOSEOUT_STATUSES as CLOSEOUT_STATUSES,
    CONDITIONING_INFORMATION_COMPONENT_FIELDS as CONDITIONING_INFORMATION_COMPONENT_FIELDS,
    CONDITIONING_INFORMATION_CONDITIONALIZATION_SCOPES as CONDITIONING_INFORMATION_CONDITIONALIZATION_SCOPES,
    CONDITIONING_INFORMATION_CONTEXT_KIND as CONDITIONING_INFORMATION_CONTEXT_KIND,
    CONDITIONING_INFORMATION_CONTRACT_FIELD as CONDITIONING_INFORMATION_CONTRACT_FIELD,
    CONDITIONING_INFORMATION_CONTRACT_FIELDS as CONDITIONING_INFORMATION_CONTRACT_FIELDS,
    CONDITIONING_INFORMATION_CONTRACT_SCHEMA as CONDITIONING_INFORMATION_CONTRACT_SCHEMA,
    CONDITIONING_INFORMATION_LAW_POPULATIONS as CONDITIONING_INFORMATION_LAW_POPULATIONS,
    CONDITIONING_INFORMATION_SEMANTIC_ID_RE as CONDITIONING_INFORMATION_SEMANTIC_ID_RE,
    CONDITIONING_INFORMATION_STAGE_FIELDS as CONDITIONING_INFORMATION_STAGE_FIELDS,
    CONDITIONING_INFORMATION_VALUE_KINDS as CONDITIONING_INFORMATION_VALUE_KINDS,
    CORRECTED_SOURCE_STATEMENT_STATUS as CORRECTED_SOURCE_STATEMENT_STATUS,
    CORRECTED_TARGET_APPROVAL_KINDS as CORRECTED_TARGET_APPROVAL_KINDS,
    CORRECTED_TARGET_SCHEMA as CORRECTED_TARGET_SCHEMA,
    EQUALITY_DEFINED_PARTITION_CONTEXT_KIND as EQUALITY_DEFINED_PARTITION_CONTEXT_KIND,
    EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD as EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD,
    EQUALITY_DEFINED_PARTITION_CONTRACT_FIELDS as EQUALITY_DEFINED_PARTITION_CONTRACT_FIELDS,
    EQUALITY_DEFINED_PARTITION_CONTRACT_SCHEMA as EQUALITY_DEFINED_PARTITION_CONTRACT_SCHEMA,
    EQUALITY_DEFINED_PARTITION_RELATION as EQUALITY_DEFINED_PARTITION_RELATION,
    EQUALITY_DEFINED_PARTITION_REQUIRED_DIRECTIONS as EQUALITY_DEFINED_PARTITION_REQUIRED_DIRECTIONS,
    FULL_CLOSEOUT_STATUSES as FULL_CLOSEOUT_STATUSES,
    LEGACY_SOURCE_DIGEST_KEYS as LEGACY_SOURCE_DIGEST_KEYS,
    PLACEHOLDER_SOURCE_RE as PLACEHOLDER_SOURCE_RE,
    SEMANTIC_CONTEXT_REQUIREMENTS_KEY as SEMANTIC_CONTEXT_REQUIREMENTS_KEY,
    SEMANTIC_CONTEXT_REQUIREMENT_FIELDS as SEMANTIC_CONTEXT_REQUIREMENT_FIELDS,
    SEMANTIC_CONTEXT_REQUIREMENT_KIND_RE as SEMANTIC_CONTEXT_REQUIREMENT_KIND_RE,
    SEMANTIC_CONTRACT_SCHEMA as SEMANTIC_CONTRACT_SCHEMA,
    SEMANTIC_CONTRACT_SCHEMAS as SEMANTIC_CONTRACT_SCHEMAS,
    SEMANTIC_CONTRACT_SCHEMA_2 as SEMANTIC_CONTRACT_SCHEMA_2,
    SEMANTIC_SURFACE_ASSUMPTION_PATTERN_FIELDS as SEMANTIC_SURFACE_ASSUMPTION_PATTERN_FIELDS,
    SEMANTIC_SURFACE_CONCLUSION_COMPONENT_FIELDS as SEMANTIC_SURFACE_CONCLUSION_COMPONENT_FIELDS,
    SEMANTIC_SURFACE_CONCLUSION_FEATURES as SEMANTIC_SURFACE_CONCLUSION_FEATURES,
    SEMANTIC_SURFACE_CONCLUSION_LEFT_OPERANDS as SEMANTIC_SURFACE_CONCLUSION_LEFT_OPERANDS,
    SEMANTIC_SURFACE_CONCLUSION_RELATIONS as SEMANTIC_SURFACE_CONCLUSION_RELATIONS,
    SEMANTIC_SURFACE_CONCLUSION_SELECTORS as SEMANTIC_SURFACE_CONCLUSION_SELECTORS,
    SEMANTIC_SURFACE_LEGACY_SCHEMA as SEMANTIC_SURFACE_LEGACY_SCHEMA,
    SEMANTIC_SURFACE_RESULT_CAPTURE_FEATURES as SEMANTIC_SURFACE_RESULT_CAPTURE_FEATURES,
    SEMANTIC_SURFACE_RESULT_CAPTURE_FIELDS as SEMANTIC_SURFACE_RESULT_CAPTURE_FIELDS,
    SEMANTIC_SURFACE_RESULT_CAPTURE_MODES as SEMANTIC_SURFACE_RESULT_CAPTURE_MODES,
    SEMANTIC_SURFACE_RESULT_EQUALITY_ALIAS_CAPTURE_FIELDS as SEMANTIC_SURFACE_RESULT_EQUALITY_ALIAS_CAPTURE_FIELDS,
    SEMANTIC_SURFACE_RESULT_FEATURES as SEMANTIC_SURFACE_RESULT_FEATURES,
    SEMANTIC_SURFACE_RESULT_GUARD_PATTERN_FIELDS as SEMANTIC_SURFACE_RESULT_GUARD_PATTERN_FIELDS,
    SEMANTIC_SURFACE_RESULT_OPERAND_PATTERN_FIELDS as SEMANTIC_SURFACE_RESULT_OPERAND_PATTERN_FIELDS,
    SEMANTIC_SURFACE_RESULT_OPERAND_SIDES as SEMANTIC_SURFACE_RESULT_OPERAND_SIDES,
    SEMANTIC_SURFACE_RESULT_PATTERN_FIELDS as SEMANTIC_SURFACE_RESULT_PATTERN_FIELDS,
    SEMANTIC_SURFACE_RESULT_QUANTIFIER_FIELDS as SEMANTIC_SURFACE_RESULT_QUANTIFIER_FIELDS,
    SEMANTIC_SURFACE_RESULT_RELATIONS as SEMANTIC_SURFACE_RESULT_RELATIONS,
    SEMANTIC_SURFACE_RESULT_SCHEMA as SEMANTIC_SURFACE_RESULT_SCHEMA,
    SEMANTIC_SURFACE_SCHEMA as SEMANTIC_SURFACE_SCHEMA,
    SEMANTIC_SURFACE_SCHEMAS as SEMANTIC_SURFACE_SCHEMAS,
    SEMANTIC_SURFACE_STRUCTURAL_TOKENS as SEMANTIC_SURFACE_STRUCTURAL_TOKENS,
    SEMANTIC_SURFACE_V1_FIELDS as SEMANTIC_SURFACE_V1_FIELDS,
    SEMANTIC_SURFACE_V2_FIELDS as SEMANTIC_SURFACE_V2_FIELDS,
    SEMANTIC_SURFACE_V3_FIELDS as SEMANTIC_SURFACE_V3_FIELDS,
    SHA256_RE as SHA256_RE,
    SOURCE_ANCHOR_EVIDENCE_FIELDS as SOURCE_ANCHOR_EVIDENCE_FIELDS,
    SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY as SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY,
    SOURCE_FILE_LINE_RE as SOURCE_FILE_LINE_RE,
    SOURCE_MODEL_DERIVATION_COMPONENT_FIELDS as SOURCE_MODEL_DERIVATION_COMPONENT_FIELDS,
    SOURCE_MODEL_DERIVATION_CONCLUSION_FIELDS as SOURCE_MODEL_DERIVATION_CONCLUSION_FIELDS,
    SOURCE_MODEL_DERIVATION_CONTEXT_KIND as SOURCE_MODEL_DERIVATION_CONTEXT_KIND,
    SOURCE_MODEL_DERIVATION_CONTRACT_FIELD as SOURCE_MODEL_DERIVATION_CONTRACT_FIELD,
    SOURCE_MODEL_DERIVATION_CONTRACT_FIELDS as SOURCE_MODEL_DERIVATION_CONTRACT_FIELDS,
    SOURCE_MODEL_DERIVATION_CONTRACT_SCHEMA as SOURCE_MODEL_DERIVATION_CONTRACT_SCHEMA,
    SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY as SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY,
    SOURCE_NAMED_RESULT_INVENTORY_REVIEW_SCHEMA as SOURCE_NAMED_RESULT_INVENTORY_REVIEW_SCHEMA,
    SOURCE_PROOF_LOCATOR_RE as SOURCE_PROOF_LOCATOR_RE,
    STRATEGIC_OBSERVATION_TOTALITY_ACTION_SCOPES as STRATEGIC_OBSERVATION_TOTALITY_ACTION_SCOPES,
    STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES as STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES,
    STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES_FIELD as STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES_FIELD,
    STRATEGIC_OBSERVATION_TOTALITY_CONDITIONING_POPULATION_SCOPES as STRATEGIC_OBSERVATION_TOTALITY_CONDITIONING_POPULATION_SCOPES,
    STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_KIND as STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_KIND,
    STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_BASE_FIELDS as STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_BASE_FIELDS,
    STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD as STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD,
    STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELDS_BY_SCHEMA as STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELDS_BY_SCHEMA,
    STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA as STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA,
    STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMAS as STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMAS,
    STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONDITIONALIZATION_SCOPE_FIELD as STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONDITIONALIZATION_SCOPE_FIELD,
    STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA as STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA,
    STRATEGIC_OBSERVATION_TOTALITY_REQUIRED_CHECKS as STRATEGIC_OBSERVATION_TOTALITY_REQUIRED_CHECKS,
    STRATEGIC_OBSERVATION_TOTALITY_SELECTED_EVENT_HISTORY_SCOPES as STRATEGIC_OBSERVATION_TOTALITY_SELECTED_EVENT_HISTORY_SCOPES,
    STRATEGIC_OBSERVATION_TOTALITY_VALUE_KINDS as STRATEGIC_OBSERVATION_TOTALITY_VALUE_KINDS,
    TEXT_SOURCE_SUFFIXES as TEXT_SOURCE_SUFFIXES,
    _RENUMBERED_RESTATEMENT_TEXT_RE as _RENUMBERED_RESTATEMENT_TEXT_RE,
    _conditioning_information_semantic_entries_errors as _conditioning_information_semantic_entries_errors,
    _exact_file_bytes as _exact_file_bytes,
    _paper_local_artifact_path as _paper_local_artifact_path,
    _semantic_contract_scope_item_context as _semantic_contract_scope_item_context,
    _semantic_surface_assumption_schema_errors as _semantic_surface_assumption_schema_errors,
    _semantic_surface_pattern_string_list as _semantic_surface_pattern_string_list,
    _semantic_surface_result_schema_errors as _semantic_surface_result_schema_errors,
    _semantic_surface_string_list as _semantic_surface_string_list,
    _source_model_derivation_component_anchor_errors as _source_model_derivation_component_anchor_errors,
    canonical_sidecar as canonical_sidecar,
    check_source_manifest as check_source_manifest,
    concrete_source_locator as concrete_source_locator,
    conditioning_information_context_contract_errors as conditioning_information_context_contract_errors,
    corrected_source_statement_map_findings as corrected_source_statement_map_findings,
    corrected_target_primary_declaration as corrected_target_primary_declaration,
    corrected_target_record_digest as corrected_target_record_digest,
    corrected_target_semantic_bundle_declarations as corrected_target_semantic_bundle_declarations,
    equality_defined_partition_context_contract_errors as equality_defined_partition_context_contract_errors,
    finding_severity as finding_severity,
    legacy_source_digest_locations as legacy_source_digest_locations,
    load_json as load_json,
    meaningful_semantic_text as meaningful_semantic_text,
    normalized_source_line_excerpt as normalized_source_line_excerpt,
    normalized_source_lines as normalized_source_lines,
    normalized_source_text as normalized_source_text,
    rel as rel,
    renumbered_presentation_alias_evidence_error as renumbered_presentation_alias_evidence_error,
    resolve_paper_source_path as resolve_paper_source_path,
    schema_version_is_exact as schema_version_is_exact,
    schema_version_is_supported as schema_version_is_supported,
    scoped_computational_observation_nodes as scoped_computational_observation_nodes,
    scoped_source_map_payload as scoped_source_map_payload,
    semantic_context_requirement_anchor_findings as semantic_context_requirement_anchor_findings,
    semantic_context_requirement_findings as semantic_context_requirement_findings,
    semantic_context_requirement_shape_findings as semantic_context_requirement_shape_findings,
    semantic_surface_inventory_findings as semantic_surface_inventory_findings,
    semantic_surface_validation_errors as semantic_surface_validation_errors,
    sha256_file as sha256_file,
    source_anchor_evidence_findings as source_anchor_evidence_findings,
    source_anchor_evidence_nodes as source_anchor_evidence_nodes,
    source_artifact_pin_findings as source_artifact_pin_findings,
    source_coverage_mode_findings as source_coverage_mode_findings,
    source_file_line_anchor_errors as source_file_line_anchor_errors,
    source_index_byte_pinned_anchor_item_ids as source_index_byte_pinned_anchor_item_ids,
    source_map_scope_integrity_findings as source_map_scope_integrity_findings,
    source_model_derivation_context_contract_errors as source_model_derivation_context_contract_errors,
    source_named_result_inventory_findings as source_named_result_inventory_findings,
    source_named_result_inventory_review_errors as source_named_result_inventory_review_errors,
    source_named_result_presentation_kinds as source_named_result_presentation_kinds,
    source_proof_fidelity_ledger_path as source_proof_fidelity_ledger_path,
    strategic_observation_totality_context_contract_errors as strategic_observation_totality_context_contract_errors,
    transaction_json as transaction_json,
    transaction_sidecar as transaction_sidecar,
    user_approved_scope_exclusion_errors as user_approved_scope_exclusion_errors,
    user_approved_scope_exclusion_map_findings as user_approved_scope_exclusion_map_findings,
    user_approved_scope_exclusion_nodes as user_approved_scope_exclusion_nodes,
    walk_values as walk_values,
)


from scripts.source_model_process_obligations import (
    caller_supplied_derived_process_basis,  # noqa: F401 - public compatibility export.
    caller_supplied_model_construction_basis,  # noqa: F401 - public compatibility export.
)

from scripts import source_claim_atom_schema
from scripts.source_core_projection import validation_errors as _source_core_errors

from scripts.current_closeout.realization import (
    V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE,
    graph_native_realization_receipts_from_inventory,
)

from scripts.closeout_pipeline import (
    EvidenceRouteSet,
    typed_route_validation_required,
)

from scripts.obligation_routes import ObligationRouteError

from scripts.source_coverage_scope import (
    THEOREM_REALIZATION_SOURCE_KINDS,
    filter_source_map_items_for_coverage,
    source_named_result_environment_kinds_from_map,
    source_presentation_aliases,
    source_coverage_mode_from_map,
    source_named_presentation_in_coverage_scope as source_named_presentation_in_coverage_scope,
    source_item_effective_route_policy,
    source_item_in_coverage_scope,
    source_item_coverage_sha256,
    source_map_cache_semantic_sha256,
)
from scripts.source_claim_policy import (
    NON_NAMED_COMPUTATIONAL_ILLUSTRATION,
    SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION,
    USER_APPROVED_SCOPE_EXCLUSION,
    source_inventory_item_requires_proof_evidence,
    source_inventory_item_scope_classification_error,
    source_inventory_item_user_approved_scope_exclusion_error,
)
from scripts.source_review_input import (
    source_anchor_file_error,
    source_semantic_input_bundle,
    statement_digest,
)
from scripts.source_proof_fidelity_semantics import (
    source_proof_fidelity_semantic_projection,
)
from scripts.corrected_target_identity import (
    CORRECTED_TARGET_APPROVAL_PROTOCOL as CORRECTED_TARGET_APPROVAL_PROTOCOL,
    corrected_target_screening_binding_is_current,
)

from scripts.source_spec_protocol import (
    source_spec_correspondence_requested as _source_spec_correspondence_requested,
)

from scripts.source_artifact_companion import (
    semantic_review_source_identity,
)


from scripts.source_record_legacy_contract import (
    SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
    SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
    SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
    SOURCE_RECORD_SEMANTIC_REUSE_POLICY,
    SOURCE_RECORD_SEMANTIC_VALIDATION_BASENAME,
)
from scripts.semantic_reuse_authority import CurrentSemanticReuseAuthority
from scripts.legacy_source_record_boundary import (
    deferred_legacy_source_record_callable as _deferred_legacy_source_record_callable,
)

from scripts.check_formalization_engine_revision import (
    EngineRevisionError,
    validate_runtime_engine_registration,
)
from scripts.formalization_protocol import (
    CURRENT_SOURCE_RECORD_PROMPT_VERSION,
    formalization_judgment_review_protocol_is_current,
)

from scripts.configured_assumption_formalization_regularities import (
    CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE,
    ConfiguredAssumptionFormalizationRegularityContext,
    load_configured_assumption_formalization_regularity_context,
)
from scripts.configured_paper_inputs import (
    configured_assumption_review_rows_from_status,
)

from scripts.source_named_result_index import (
    named_result_presentations_sha256 as named_result_presentations_sha256,
    reviewed_source_presentation_inventory as reviewed_source_presentation_inventory,
)

from scripts.tomllib_compat import tomllib
from scripts.v11_screening_contract import validate_v11_screening_container
from scripts.evidence_run_context import (
    CommonEvidenceRunContextInputs as _CommonEvidenceRunContextInputs,
    EvidenceJSONSnapshot,
    EvidenceRunContext,
    EvidenceRunContextIssuerBinding as _EvidenceRunContextIssuerBinding,  # noqa: F401 - supported module API.
    Finding,
    LegacyEvidenceRunContext,
    LegacySourceRecordInputs,
    LegacySourceRecordState,
    V11EvidenceRunContext,
    has_current_primary_closeout_source_record_judgment_receipt as _has_current_primary_closeout_source_record_judgment_receipt,
    issue_primary_closeout_source_record_judgment_receipt as _issue_primary_closeout_source_record_judgment_receipt,  # noqa: F401 - supported module API.
    run_scoped_validation_findings as _run_scoped_validation_findings,
)
from scripts.immutable_json import freeze_json as _freeze_json
from scripts.current_closeout.evidence_transaction import (
    CurrentV11EvidenceSnapshotRoot,
    build_current_v11_context_with_graph_checkpoint,
)
from scripts.current_closeout.evidence_acceptance import (
    has_current_v11_evidence_integrity_acceptance,
)
from scripts.current_closeout.primary_gate_transaction import (
    accepted_current_v11_primary_gate,
)
from scripts.current_closeout import lean_review_graph as v11_graph
from scripts.current_closeout import review_surface as v11_review_surface
from scripts.current_closeout import source_route_gate as v11_source_route_gate
semantic_model_subanalysis_errors = _deferred_legacy_source_record_callable(
    "semantic_model_subanalysis_errors"
)
source_record_item_judgment_current = _deferred_legacy_source_record_callable(
    "source_record_item_judgment_current"
)
canonical_digest_payload = _deferred_legacy_source_record_callable(
    "canonical_digest_payload"
)
fingerprint_without_raw_producer_provenance = (
    _deferred_legacy_source_record_callable(
        "fingerprint_without_raw_producer_provenance"
    )
)
load_current_semantic_reuse_authority = _deferred_legacy_source_record_callable(
    "load_current_semantic_reuse_authority"
)
semantic_fingerprint_matches = _deferred_legacy_source_record_callable(
    "semantic_fingerprint_matches"
)
reusable_item_metadata_error = _deferred_legacy_source_record_callable(
    "reusable_item_metadata_error"
)
source_record_audit_receipt_error = _deferred_legacy_source_record_callable(
    "source_record_audit_receipt_error"
)
source_record_item_reuse_eligible = _deferred_legacy_source_record_callable(
    "source_record_item_reuse_eligible"
)
source_record_target_route_error = _deferred_legacy_source_record_callable(
    "source_record_target_route_error"
)
_raw_item_metadata_error = _deferred_legacy_source_record_callable(
    "source_record_raw_reusable_item_metadata_error"
)
raw_source_record_obligation_groups = _deferred_legacy_source_record_callable(
    "raw_source_record_obligation_groups"
)
serialized_source_record_overlay_labels = _deferred_legacy_source_record_callable(
    "serialized_source_record_overlay_labels"
)
source_record_overlay_labels_with_artifacts = (
    _deferred_legacy_source_record_callable(
        "source_record_overlay_labels_with_artifacts"
    )
)
archived_source_record_transport_artifacts = (
    _deferred_legacy_source_record_callable(
        "archived_source_record_transport_artifacts"
    )
)
archived_source_record_transport_item_field = (
    _deferred_legacy_source_record_callable(
        "archived_source_record_transport_item_field"
    )
)
load_administrative_projection_rebind_context = (
    _deferred_legacy_source_record_callable(
        "load_administrative_projection_rebind_context"
    )
)
model_convention_semantic_digest = _deferred_legacy_source_record_callable(
    "model_convention_semantic_digest"
)
project_source_record_response_association_pins = (
    _deferred_legacy_source_record_callable(
        "project_source_record_response_association_pins"
    )
)
recursive_field_target_disposition_errors = (
    _deferred_legacy_source_record_callable(
        "recursive_field_target_disposition_errors"
    )
)
semantic_target_disposition_errors = _deferred_legacy_source_record_callable(
    "semantic_target_disposition_errors"
)
source_input_target_disposition_errors = _deferred_legacy_source_record_callable(
    "source_input_target_disposition_errors"
)
current_auxiliary_routing_context = _deferred_legacy_source_record_callable(
    "current_auxiliary_routing_context"
)


PAPERS = ROOT / "papers"
AUDIT_CONFIG = PAPERS / "audit_config.json"
LAKEFILE = ROOT / "lakefile.toml"

_UNSET = object()
REPOSITORY_VISIBILITIES = frozenset({"public", "private_only"})
# Schema 2 contracts predate the probability-semantics dimensions below.  They
# remain auditable as historical evidence, while all newly created corrected
# model contracts must use schema 3 and cover the expanded set.
CORRECTED_MODEL_LEGACY_CONTRACT_SCHEMA = 2
CORRECTED_MODEL_CONTRACT_SCHEMA = 3
CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION = CURRENT_SOURCE_RECORD_PROMPT_VERSION
CORRECTED_MODEL_LEGACY_SEMANTIC_DIMENSIONS = {
    "expanded_binders_and_domain",
    "carrier_and_domain",
    "probability_support_endpoints",
    "joint_law_and_state_evolution",
    "extended_rate_codomain",
}
CORRECTED_MODEL_SEMANTIC_DIMENSIONS = {
    *CORRECTED_MODEL_LEGACY_SEMANTIC_DIMENSIONS,
    "conditioning_and_calibration_semantics",
    "expectation_definedness",
    "null_cell_totalization_and_partition_scope",
}
CORRECTED_MODEL_SEMANTIC_DISPOSITIONS = {
    "literal_source_formula",
    "literal_source_condition",
    "author_approved_correction",
    "author_approved_additional_assumption",
    "derived_checked_bridge",
    "archival_diagnostic",
}
CORRECTED_MODEL_ASSUMPTION_DISPOSITIONS = {
    "literal_source_condition",
    "author_approved_correction",
    "author_approved_additional_assumption",
}
CORRECTED_MODEL_DIMENSION_VERDICTS = {
    "matches_literal_source",
    "author_approved_correction",
    "archival_diagnostic",
    "not_applicable",
}
CORRECTED_MODEL_SOURCE_LOCATOR_RE = re.compile(
    r"(?:\b[\w./-]+\.(?:tex|txt|md|pdf):\d+|"
    r"\b(?:Appendix|Theorem|Lemma|Proposition|Corollary|Definition|Equation|Section)\s+)",
    re.I,
)
SEMANTIC_MODEL_REVIEW_CLASSIFICATION = "semantic_model_review"
SEMANTIC_MODEL_REVIEW_VERDICTS = {
    "matches_source_model",
    "matches_literal_source",
    "matches_approved_source_convention",
    "matches_approved_corrected_target",
    "not_applicable",
    "mismatch_or_open",
    "documented_partial_boundary",
}
SEMANTIC_MODEL_REVIEW_SCHEMA = 2
SEMANTIC_MODEL_REVIEW_DIMENSIONS = {
    "expanded_binders_and_domain",
    "carrier_and_domain",
    "probability_support_endpoints",
    "joint_law_and_state_evolution",
    "conditioning_and_calibration_semantics",
    "expectation_definedness",
    "null_cell_totalization_and_partition_scope",
    "extended_rate_codomain",
}
# These are not part of the universal schema-2 review checklist.  They are
# source-context-triggered extensions emitted only for a specific generated
# row, with their own source/signature association and response validator.
# Keeping them out of ``SEMANTIC_MODEL_REVIEW_DIMENSIONS`` avoids turning a
# repair for one source model into a new obligatory review dimension for every
# unrelated paper.
SOURCE_SCOPED_SEMANTIC_MODEL_DIMENSIONS = {
    "conditioning_information",
    "source_equality_partition",
    "source_model_derivation",
    "strategic_observation_totality",
}
SEMANTIC_MODEL_BRIDGE_DIMENSIONS = {
    "probability_support_endpoints",
    "joint_law_and_state_evolution",
    "conditioning_and_calibration_semantics",
    "expectation_definedness",
    "null_cell_totalization_and_partition_scope",
    "extended_rate_codomain",
}


def semantic_model_item_dimension_ids_error(raw_dimensions: object) -> str:
    """Validate one generated row's base and source-scoped dimensions.

    Every row has the fixed schema-2 base checklist.  A source-pinned
    generator may append a narrowly validated dimension, but arbitrary extras
    cannot be smuggled into the audit surface.  This is intentionally driven
    by generated context metadata rather than a declaration, binder, or map
    key.
    """

    if not isinstance(raw_dimensions, list) or not all(
        isinstance(dimension, dict) for dimension in raw_dimensions
    ):
        return "semantic dimensions must be a list of objects"
    dimension_ids = [
        str(dimension.get("id") or "").strip() for dimension in raw_dimensions
    ]
    if not dimension_ids or any(not dimension for dimension in dimension_ids):
        return "semantic dimensions must have nonempty ids"
    if len(dimension_ids) != len(set(dimension_ids)):
        return "semantic dimensions must not duplicate an id"
    dimension_id_set = set(dimension_ids)
    if not SEMANTIC_MODEL_REVIEW_DIMENSIONS.issubset(dimension_id_set):
        return "semantic dimensions omit a required schema-2 base dimension"
    extensions = dimension_id_set - SEMANTIC_MODEL_REVIEW_DIMENSIONS
    if not extensions.issubset(SOURCE_SCOPED_SEMANTIC_MODEL_DIMENSIONS):
        return "semantic dimensions contain an unsupported non-base extension"
    for dimension in raw_dimensions:
        if (
            str(dimension.get("id") or "").strip()
            == "source_equality_partition"
            and dimension.get("requires_source_equality_partition_analysis") is not True
        ):
            return (
                "source_equality_partition must be an explicitly generated "
                "source-pinned equality-partition obligation"
            )
        if (
            str(dimension.get("id") or "").strip()
            == "strategic_observation_totality"
            and dimension.get("requires_strategic_observation_totality_analysis")
            is not True
        ):
            return (
                "strategic_observation_totality must be an explicitly generated "
                "source-pinned game-observation totality obligation"
            )
        if (
            str(dimension.get("id") or "").strip()
            == "conditioning_information"
            and dimension.get("requires_conditioning_information_analysis") is not True
        ):
            return (
                "conditioning_information must be an explicitly generated "
                "source-pinned conditioning-information obligation"
            )
        if (
            str(dimension.get("id") or "").strip()
            == "source_model_derivation"
            and dimension.get("requires_source_model_derivation_analysis") is not True
        ):
            return (
                "source_model_derivation must be an explicitly generated "
                "source-pinned model-derivation obligation"
            )
    return ""
# A source-first closeout is not allowed to rely indefinitely on a legacy
# statement/coverage surface once it has both a curated source inventory and a
# canonical source-proof ledger.  These fields describe evidence artifacts and
# review schemas only; Lean declaration names are intentionally not inputs.
V10_STATEMENT_REVIEW_ARTIFACT_FIELDS = (
    "lean_to_tex_file",
    "match_judgment_file",
    "review_surface_audit_file",
)
V10_PAPER_COVERAGE_ARTIFACT_FIELDS = ("paper_coverage_audit_file",)
V10_SOURCE_RECORD_ARTIFACT_FIELDS = (
    "source_record_audit_file",
    "source_record_judgment_file",
)

AUDIT_SIDECARS = (
    # Lean's standalone transitive import closure is the formal-side root for
    # v11 review.  It is intentionally independent of source_record_audit.json
    # and is a non-accepting input carrier.
    "LEAN_IMPORT_CLOSURE_RECEIPT.json",
    "assumption_match_llm.json",
    "defect_support_match_llm.json",
    "lean_to_tex_llm.json",
    # v11 direct semantic-review artifacts are first-class closeout inputs.
    # Freeze the actual judgments with the transaction. The human-review
    # packet cache is a derived graph rendering and is intentionally excluded:
    # regenerating that transport cannot change or invalidate its evidence.
    "library_semantic_review.json",
    "paper_coverage_llm.json",
    "paper_semantic_prerequisites.json",
    "paper_statement_map.json",
    "review_surface_llm.json",
    "source_record_audit.json",
    "source_record_match_llm.json",
    "source_proof_fidelity.json",
    "statement_match_llm.json",
    "v11_raw_source_spec_screening.json",
)
V11_SUPERSEDED_SEMANTIC_SIDECARS = frozenset(
    {
        "lean_to_tex_llm.json",
        "paper_coverage_llm.json",
        "review_surface_llm.json",
        "statement_match_llm.json",
    }
)
V11_NONAUTHORITATIVE_LEGACY_SIDECARS = (
    V11_SUPERSEDED_SEMANTIC_SIDECARS
    | frozenset({"source_record_audit.json", "source_record_match_llm.json"})
)
INDEPENDENT_LANES = (
    "assumption_match_llm.json",
    "defect_support_match_llm.json",
    "lean_to_tex_llm.json",
    "paper_coverage_llm.json",
    "review_surface_llm.json",
    "source_record_match_llm.json",
    "statement_match_llm.json",
)
SOURCE_RECORD_OPTIONAL_AUTHORITY_SIDECARS = (
    "source_record_attested_selected_semantic_reuse.json",
    "source_record_auxiliary_routing_supplement.json",
    "source_record_differential_revalidation.json",
    "source_record_semantic_rebind.json",
    "source_record_scoped_receipt_rebind.json",
    # A narrow consumer-side structural replay is authority only when its
    # fixed receipt and, for transparent-Spec pairs, manifest authority are
    # both frozen with the raw audit transaction.
    "source_record_semantic_contract_revalidation.json",
    "lean_signature_manifest_cache_authority.json",
    "source_record_semantic_validation.json",
)
NAME_ONLY_REASON_RE = re.compile(
    r"exactly matches current dashboard row name|"
    r"exact source-key|"
    r"\bname[-_ ]?match(?:ed|es|ing)?\b|"
    r"\bmatched by name\b",
    re.I,
)
VACUOUS_ASSUMPTION_RE = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected)\s+)*"
    r"(?:def|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
    r"(?:(?!^\s*(?:def|abbrev|theorem|lemma|structure|class|inductive)\b).)*?"
    r":\s*Prop\s*:=\s*True\b",
    re.M | re.S,
)

# A strict source-record identity replay rehashes every external Lean artifact
# in the saved Lean-owned import closure, once before and once after its own
# TOCTOU boundary.  Coordinate only with fresh raw scans, which use the same
# repository-wide advisory lock while compiling and publishing new evidence.
# The evidence gate takes a nonblocking shared lock: it never treats a busy
# source-record scan as current evidence, and it avoids an opaque I/O fight.
SOURCE_RECORD_AUDIT_LOCK_RELATIVE_PATH = Path(".lake") / "source-record-audit.lock"
# This replays a whole Lean-owned closure and can hash thousands of external
# artifacts twice.  Match the repository's established generous-but-bounded
# paper-closeout limit rather than treating an I/O-heavy valid receipt like the
# short `lake env` discovery command used inside fresh generation.
SOURCE_RECORD_IDENTITY_HELPER_TIMEOUT_SECONDS = 600
SOURCE_RECORD_IDENTITY_PROGRESS_HEARTBEAT_SECONDS = 15.0
CORRECTED_TARGET_COVERAGE = "covered_corrected_target"
CORRECTED_TARGET_ROUTE_KIND = "approved_corrected_target"
CORRECTED_TARGET_ROUTE_RELATION = "proves_approved_corrected_target"
APPROVED_CORRECTED_TARGET_MATCH = "matches_approved_corrected_target"
PAPER_COVERAGE_ROW_SIGNATURE_PROMPT_VERSION = (
    "paper-coverage-v6-verbatim-source-anchor-proof-row-signature-pins"
)
DIRECT_PAPER_COVERAGE_JUDGMENTS = {
    "covered",
    "covered_by_rows",
    "conditional_boundary",
    "covered_with_boundary",
    CORRECTED_TARGET_COVERAGE,
}
# A theorem source item can contain several independently advertised claims.
# These atoms are source-first semantic inventory entries: their Lean route is
# checked only as an auditable endpoint, never used as evidence that an atom
# was present in the source.
# ``source_quote_sha256`` is intentionally optional in the general atom
# inventory.  Existing v10 maps may use source atoms as a source-first routing
# aid without opting into the v11 theorem-realization credential.  Once a map
# opts into source-Spec correspondence, however, it becomes mandatory and is
# checked against the exact current canonical source slice.
SOURCE_CLAIM_ATOM_REQUIRED_FIELDS = (
    source_claim_atom_schema.SOURCE_CLAIM_ATOM_REQUIRED_FIELDS
)
SOURCE_CLAIM_ATOM_IDENTITY_SCHEMA = (
    source_claim_atom_schema.EXACT_QUOTE_IDENTITY_SCHEMA
)
EXACT_SOURCE_CLAIM_ATOM_IDENTITY_SCHEMAS = (
    source_claim_atom_schema.EXACT_IDENTITY_SCHEMAS
)
SUPPORTED_SOURCE_CLAIM_ATOM_IDENTITY_SCHEMAS = (
    source_claim_atom_schema.SUPPORTED_IDENTITY_SCHEMAS
)
SOURCE_CLAIM_ATOM_FIELDS = source_claim_atom_schema.SOURCE_CLAIM_ATOM_FIELDS
SOURCE_CLAIM_ATOM_ID_RE = source_claim_atom_schema.SOURCE_CLAIM_ATOM_ID_RE
SOURCE_CLAIM_ATOM_THEOREM_LIKE_KINDS = (
    THEOREM_REALIZATION_SOURCE_KINDS - {"example"}
)
# V11 scopes its theorem-realization obligation from the independently curated
# source inventory, not from a paper-authored ``claim_bearing`` switch.  The
# latter is a receipt field once an item is in scope, never permission to omit
# a named source result.  Examples may contain a source-presented mathematical
# conclusion and are included when the normal named-theory inventory retains
# them.  Explicit defect/support-only entries are handled by their dedicated
# source-fidelity lanes and cannot masquerade as proved source claims.
# The realization correspondence is deliberately independent of the legacy
# semantic-contract schemas.  It is a new closeout lane: old maps stay
# readable, while a map that opts in must bind every individually source-pinned
# claim atom to an elaborated Spec component and account for every material
# closure node.  Neither a source-item key nor a theorem name is an identity in
# this protocol.
SOURCE_SPEC_CORRESPONDENCE_FIELDS = (
    source_claim_atom_schema.SOURCE_SPEC_CORRESPONDENCE_FIELDS
)
SOURCE_SPEC_ATOM_BINDING_FIELDS = frozenset(
    {
        "source_atom_sha256",
        "spec_component_sha256s",
        "semantic_bridge",
        "overlap_justification",
    }
)
SOURCE_SPEC_NODE_DISPOSITION_FIELDS = frozenset(
    {
        "closure_component_sha256",
        "source_atom_sha256",
        "semantic_basis",
        "pinned_declaration_identity_sha256",
    }
)
SOURCE_SPEC_SEMANTIC_BASIS_FIELDS = frozenset(
    {"artifact_path", "artifact_sha256", "source_locator", "semantic_statement"}
)


# ``definitionally_realizes`` is for source *definitions*, which are semantic
# review targets rather than propositions asserted to hold.  Its evidence is
# an exact Lean-checked equivalence between the independently written Spec and
# the paper-local definition; it is not a proof of the definition as a fact.
# Schema 1 can Lean-check only exact proposition proof/refutation. Specialized
# shapes need role-bearing fields and dedicated Meta checks before a label can
# count as semantic evidence.


def has_current_v11_primary_closeout_semantic_graph_receipt(
    context: object,
    *,
    folder: Path,
) -> bool:
    """Return whether one exact v11 transaction passed the whole primary gate.

    Current v11 closeout deliberately does not acquire the superseded raw
    source-record payload.  Deferred consumers may therefore reuse the
    primary gate only through this runtime-only capability, which additionally
    proves that the builder selected the Lean-owned claim-graph lane.  A
    caller-provided Boolean, a persisted sidecar, or a receipt from the legacy
    lane cannot satisfy this predicate.
    """

    return bool(
        isinstance(context, EvidenceRunContext)
        and context.issued_by_builder
        and context.folder == folder.resolve()
        and context.source_semantic_lane == V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
        and accepted_current_v11_primary_gate(context) is not None
    )


def has_current_v11_evidence_integrity_receipt(context: object) -> bool:
    """Recognize only the exact gate-issued current evidence acceptance."""

    return has_current_v11_evidence_integrity_acceptance(context)


EVIDENCE_DIAGNOSTIC_CONTEXTS = "evidence_contexts_built"
EVIDENCE_DIAGNOSTIC_WATCH_DIGESTS = "watched_input_digests"
EVIDENCE_DIAGNOSTIC_IDENTITY_VALIDATIONS = "source_record_identity_validations"
EVIDENCE_DIAGNOSTIC_CURRENT_JUDGMENTS = "current_judgment_materializations"
EVIDENCE_DIAGNOSTIC_CORRECTED_SCOPE = "corrected_scope_evaluations"
EVIDENCE_DIAGNOSTIC_INPUT_MUTATIONS = "watched_input_mutations"


def _increment_diagnostic(
    diagnostics: MutableMapping[str, int] | None, key: str
) -> None:
    if diagnostics is not None:
        diagnostics[key] = diagnostics.get(key, 0) + 1


_V11LeanReviewSurface = v11_review_surface.V11LeanReviewSurface
CurrentV11ReviewGraphProjection = (
    v11_review_surface.CurrentV11ReviewGraphProjection
)


def _v11_lean_review_surface(
    folder: Path,
    expected_specs: Iterable[str],
    *,
    context: EvidenceRunContext | None,
) -> _V11LeanReviewSurface:
    """Read the current transaction's Lean surface without preparing evidence."""

    if not isinstance(context, EvidenceRunContext):
        raise ValueError(
            "v11 Lean review graph requires a builder-issued evidence transaction"
        )
    return v11_review_surface.read_diagnostic_v11_review_surface(
        ROOT,
        folder,
        expected_specs,
        context=context,
    )


builder_issued_v11_lean_review_surface = (
    v11_review_surface.builder_issued_v11_lean_review_surface
)


def current_v11_review_graph_projection(
    folder: Path,
) -> CurrentV11ReviewGraphProjection | None:
    """Compatibility export of the current package's graph projection."""

    return v11_review_surface.load_current_v11_review_graph_projection(
        ROOT,
        folder,
    )


def current_v11_review_graph_target_material(
    folder: Path,
) -> Mapping[str, object] | None:
    """Return graph-native reviewer targets for a standalone writer command."""

    projection = current_v11_review_graph_projection(folder)
    return projection.target_material() if projection is not None else None


def build_evidence_run_context_with_v11_graph_checkpoint(
    folder: Path,
) -> EvidenceRunContext:
    """Build the current typed transaction and reuse one graph checkpoint."""

    return build_current_v11_context_with_graph_checkpoint(
        folder,
        repository_root=ROOT,
    )


def prepare_v11_lean_review_graph(
    folder: Path,
) -> Mapping[str, object]:
    """Compatibility export of the physical current-closeout graph producer."""

    from scripts.current_closeout.graph_preparation import (
        prepare_v11_lean_review_graph as prepare,
    )

    return prepare(ROOT, folder)


def unique_findings(findings: Iterable[Finding]) -> list[Finding]:
    """Preserve order while collapsing equivalent conclusions from audit lanes."""
    seen: set[tuple[str, str, str, str]] = set()
    unique: list[Finding] = []
    for finding in findings:
        key = (finding.severity, finding.paper, finding.path, finding.message)
        if key not in seen:
            seen.add(key)
            unique.append(finding)
    return unique


def paper_dirs(
    paper_filter: str | None = None,
    *,
    public_complete: bool = False,
) -> list[Path]:
    folders = sorted(
        path.parent
        for path in PAPERS.glob("*/status.json")
        if path.parent.name != "TEMPLATE"
    )
    if public_complete:
        selected: list[Path] = []
        for folder in folders:
            status, payload = paper_status(folder)
            if "repository_visibility" not in payload:
                raise ValueError(
                    f"{rel(folder / 'status.json')}: public release requires an "
                    "explicit repository_visibility (`public` or `private_only`)"
                )
            raw_visibility = payload.get("repository_visibility")
            if not isinstance(raw_visibility, str):
                visibility = ""
            else:
                visibility = raw_visibility.strip().lower()
            if visibility not in REPOSITORY_VISIBILITIES:
                expected = ", ".join(sorted(REPOSITORY_VISIBILITIES))
                raise ValueError(
                    f"{rel(folder / 'status.json')}: repository_visibility must be "
                    f"one of {expected}, got {raw_visibility!r}"
                )
            if visibility == "public" and status in FULL_CLOSEOUT_STATUSES:
                selected.append(folder)
        folders = selected
    if paper_filter is not None:
        folders = [folder for folder in folders if folder.name == paper_filter]
    return folders


def paper_status(folder: Path) -> tuple[str, dict[str, Any]]:
    payload = load_json(folder / "status.json") or {}
    return str(payload.get("status") or "").strip().lower(), payload


def source_record_judgment_freshness_severity(status: str) -> str:
    return "ERROR" if status in FULL_CLOSEOUT_STATUSES else "WARN"


def sidecar_has_items(payload: dict[str, Any]) -> bool:
    for key in ("items", "judgments"):
        value = payload.get(key)
        if isinstance(value, dict) and value:
            return True
        if isinstance(value, list) and value:
            return True
    return "judgment" in payload


def validators(payload: dict[str, Any]) -> set[str]:
    out: set[str] = set()
    for path, value in walk_values(payload):
        if path and path[-1] in {
            "validator",
            "model",
            "judge",
            "agent",
            "generator",
            "translator",
            "producer",
        }:
            text = str(value or "").strip()
            if text:
                out.add(text)
    return out


def identities_for_keys(payload: dict[str, Any], keys: set[str]) -> set[str]:
    """Collect free-form producer attestations for explicit workflow roles."""

    identities: set[str] = set()
    for path, value in walk_values(payload):
        if path and path[-1] in keys:
            identity = str(value or "").strip()
            if identity:
                identities.add(identity)
    return identities


def canonical_governing_corrections(
    status_payload: dict[str, Any],
) -> list[dict[str, Any]] | None:
    """Return every governing correction in a stable, content-complete order."""

    raw_corrections = status_payload.get("governing_corrections")
    if not isinstance(raw_corrections, list) or not raw_corrections:
        return None
    corrections: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    for correction in raw_corrections:
        if not isinstance(correction, dict):
            return None
        correction_id = str(correction.get("id") or "").strip()
        if not correction_id or correction_id in seen_ids:
            return None
        seen_ids.add(correction_id)
        corrections.append(canonical_json_payload(correction))
    return sorted(
        corrections,
        key=lambda correction: json.dumps(correction, sort_keys=True, separators=(",", ":")),
    )


def governing_corrections_sha256(status_payload: dict[str, Any]) -> str | None:
    """Return the current full-content governing-correction digest."""

    corrections = canonical_governing_corrections(status_payload)
    return canonical_json_digest(corrections) if corrections is not None else None


def _nonempty_string_list(value: object) -> list[str] | None:
    if not isinstance(value, list):
        return None
    items = [str(item).strip() for item in value if isinstance(item, str) and item.strip()]
    if len(items) != len(value) or not items or len(set(items)) != len(items):
        return None
    return sorted(items)


def _is_fully_qualified_lean_identity(value: str) -> bool:
    """Return whether one value is a non-short Lean declaration identity.

    The generator resolves these names independently.  This structural check
    only prevents a new multi-model scope from using a display label, a short
    type tail, or a comma-separated pseudo-list as a governing model root.
    """

    return bool(re.fullmatch(r"[^\s.]+(?:\.[^\s.]+)+", value))


@dataclass(frozen=True)
class CorrectedModelScopeModelBindings:
    """Normalized governing-model roots for one corrected formalization scope.

    Legacy scopes carry one scalar model and implicitly map every target to
    it.  New scopes make the target-to-model relationship explicit so a
    schedule-specific theorem cannot silently inherit a companion model.
    """

    model_spec_declarations: tuple[str, ...]
    target_model_spec_declarations: dict[str, str]
    uses_legacy_scalar: bool


def corrected_model_scope_model_bindings(
    scope: object,
    *,
    target_result_declarations: object | None = None,
) -> tuple[CorrectedModelScopeModelBindings | None, list[str]]:
    """Normalize legacy or explicit multi-model corrected-scope metadata.

    New metadata must provide both ``model_spec_declarations`` and an exact
    ``target_model_spec_declarations`` map.  A legacy scalar remains accepted
    unchanged and is normalized by mapping every declared target to it.
    """

    if not isinstance(scope, dict):
        return None, ["must be an object"]
    raw_targets = (
        scope.get("target_result_declarations")
        if target_result_declarations is None
        else target_result_declarations
    )
    targets = _nonempty_string_list(raw_targets)
    if targets is None:
        return None, ["requires unique nonempty target_result_declarations"]

    has_multi_fields = (
        "model_spec_declarations" in scope
        or "target_model_spec_declarations" in scope
    )
    raw_scalar = scope.get("model_spec_declaration")
    scalar = raw_scalar.strip() if isinstance(raw_scalar, str) else ""
    if not has_multi_fields:
        if not scalar:
            return None, ["requires a nonempty governing model_spec_declaration"]
        return (
            CorrectedModelScopeModelBindings(
                model_spec_declarations=(scalar,),
                target_model_spec_declarations={target: scalar for target in targets},
                uses_legacy_scalar=True,
            ),
            [],
        )

    errors: list[str] = []
    if raw_scalar is not None:
        errors.append(
            "must not combine legacy model_spec_declaration with multi-model metadata"
        )
    models = _nonempty_string_list(scope.get("model_spec_declarations"))
    if models is None:
        errors.append("requires unique nonempty model_spec_declarations")
        models = []
    elif any(not _is_fully_qualified_lean_identity(model) for model in models):
        errors.append("model_spec_declarations must contain fully qualified Lean identities")

    raw_target_models = scope.get("target_model_spec_declarations")
    target_models: dict[str, str] = {}
    if not isinstance(raw_target_models, dict):
        errors.append("requires target_model_spec_declarations object")
    else:
        for raw_target, raw_model in raw_target_models.items():
            if not isinstance(raw_target, str) or not raw_target.strip():
                errors.append(
                    "target_model_spec_declarations has a nonempty-string target key requirement"
                )
                continue
            if not isinstance(raw_model, str) or not raw_model.strip():
                errors.append(
                    "target_model_spec_declarations has a nonempty-string model value requirement"
                )
                continue
            target = raw_target.strip()
            model = raw_model.strip()
            if target in target_models:
                errors.append(
                    "target_model_spec_declarations has duplicate normalized target keys"
                )
                continue
            target_models[target] = model
        if set(target_models) != set(targets):
            errors.append(
                "target_model_spec_declarations must map exactly every target_result_declaration"
            )
        for target, model in target_models.items():
            if not _is_fully_qualified_lean_identity(target):
                errors.append(
                    "target_model_spec_declarations target keys must be fully qualified Lean identities"
                )
            if not _is_fully_qualified_lean_identity(model):
                errors.append(
                    "target_model_spec_declarations values must be fully qualified Lean identities"
                )
            elif model not in models:
                errors.append(
                    "target_model_spec_declarations values must be declared model_spec_declarations"
                )
    if errors:
        return None, errors
    return (
        CorrectedModelScopeModelBindings(
            model_spec_declarations=tuple(models),
            target_model_spec_declarations={
                target: target_models[target] for target in sorted(target_models)
            },
            uses_legacy_scalar=False,
        ),
        [],
    )


def corrected_model_scope_model_metadata(
    bindings: CorrectedModelScopeModelBindings,
) -> dict[str, object]:
    """Return the canonical persisted shape for normalized model bindings."""

    if bindings.uses_legacy_scalar:
        return {"model_spec_declaration": bindings.model_spec_declarations[0]}
    return {
        "model_spec_declarations": list(bindings.model_spec_declarations),
        "target_model_spec_declarations": {
            target: bindings.target_model_spec_declarations[target]
            for target in sorted(bindings.target_model_spec_declarations)
        },
    }


def corrected_model_contract_dimensions(schema: object) -> set[str] | None:
    """Return the dimension set pinned by one corrected-model contract schema.

    Schema 2 is a historical record format.  It is intentionally not upgraded
    in place: doing so would make old evidence appear to have reviewed new
    probability semantics.  New schema-3 contracts must review all eight
    dimensions.
    """

    if schema_version_is_exact(schema, CORRECTED_MODEL_LEGACY_CONTRACT_SCHEMA):
        return CORRECTED_MODEL_LEGACY_SEMANTIC_DIMENSIONS
    if schema_version_is_exact(schema, CORRECTED_MODEL_CONTRACT_SCHEMA):
        return CORRECTED_MODEL_SEMANTIC_DIMENSIONS
    return None


def corrected_model_raw_item_freshness_mode(
    item: object,
) -> tuple[str | None, str]:
    """Classify a raw corrected-model item by its generated freshness mode.

    An item-level digest is valid only when the generator explicitly marked the
    item reusable.  Conversely, an explicitly non-reusable item may be covered
    only by the contract's current aggregate source-record audit pin.  This
    keeps an absent source identity from becoming a name-based synthetic item
    key while still requiring a complete fresh audit of its semantic surface.
    """

    if not isinstance(item, dict):
        return None, "must be an object"
    eligibility = item.get("source_record_item_reuse_eligibility")
    if not isinstance(eligibility, dict):
        return None, "requires generated source_record_item_reuse_eligibility"
    eligible = eligibility.get("eligible")
    blockers = eligibility.get("blockers")
    if not isinstance(eligible, bool) or not isinstance(blockers, list) or any(
        not isinstance(blocker, str) or not blocker.strip() for blocker in blockers
    ):
        return None, "has malformed source_record_item_reuse_eligibility"

    digest = str(item.get("source_record_item_sha256") or "").strip()
    metadata_error = reusable_item_metadata_error(
        item,
        expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
    )
    if metadata_error:
        return None, metadata_error
    if eligible:
        if blockers:
            return None, "is reusable but lists item-reuse blockers"
        if not SHA256_RE.fullmatch(digest):  # defensive: helper already checks this
            return None, "is reusable but lacks a SHA-256 item digest"
        return "item", ""

    if not blockers:
        return None, "is aggregate-only but has no item-reuse blocker"
    generated_item_fields = (
        "source_record_item_digest_schema",
        "source_record_item_semantic_id",
        "source_record_item_context_sha256",
        "source_record_item_sha256",
    )
    if any(item.get(field) not in (None, "", []) for field in generated_item_fields):
        return None, "is aggregate-only but retains item-level digest metadata"
    return "aggregate", ""


def corrected_model_mapping_freshness_error(
    mapping: object,
    item: object,
) -> str:
    """Return an exact/aggregate freshness error for one contract mapping."""

    if not isinstance(mapping, dict):
        return "must be an object"
    mode, item_error = corrected_model_raw_item_freshness_mode(item)
    if item_error:
        return f"references a raw item that {item_error}"
    mapped_digest_value = mapping.get("source_record_item_sha256")
    if mapped_digest_value is None:
        mapped_digest = ""
    elif isinstance(mapped_digest_value, str):
        mapped_digest = mapped_digest_value.strip()
    else:
        return "has a non-string source_record_item_sha256"
    aggregate_only = mapping.get("aggregate_audit_freshness_only")
    if mode == "item":
        if aggregate_only not in (None, False):
            return "claims aggregate-only freshness for a reusable raw item"
        raw_digest = str(item.get("source_record_item_sha256") or "").strip()
        if mapped_digest != raw_digest:
            return "is not pinned to the current expanded-item digest"
        return ""
    if aggregate_only is not True:
        return "must set aggregate_audit_freshness_only for a non-reusable raw item"
    if mapped_digest:
        return "must not retain an item digest for aggregate-only freshness"
    return ""


def corrected_model_transitively_reachable_field_items(
    audit_payload: object,
    *,
    model_spec_declaration: object | None = None,
    model_spec_declarations: object | None = None,
    target_model_spec_declarations: object | None = None,
    target_result_declarations: object,
) -> tuple[dict[str, dict[str, Any]], list[str]]:
    """Return exact field items reached through mapped corrected model records.

    The raw recursive-field collection is de-duplicated by declaration, so a
    nested field can be stored under its immediate record root rather than the
    top-level corrected-model path.  The generated semantic item's
    ``record_field_types`` retains that transitive graph.  This helper joins
    the two generated surfaces using complete declaration identities: it never
    guesses from suffixes, field spelling, or a record-name convention.

    Every path rooted at each target's declared governing model must have a
    structurally complete chain whose nodes are generated recursive-field
    items. A malformed, cross-mapped, or incomplete graph yields errors,
    rather than silently treating a nested record as covered by another
    target's model.
    """

    errors: list[str] = []
    if isinstance(target_result_declarations, tuple):
        target_result_declarations = list(target_result_declarations)
    scope_metadata: dict[str, object] = {
        "target_result_declarations": target_result_declarations,
    }
    if model_spec_declarations is not None or target_model_spec_declarations is not None:
        if model_spec_declaration is not None:
            scope_metadata["model_spec_declaration"] = model_spec_declaration
        scope_metadata["model_spec_declarations"] = model_spec_declarations
        scope_metadata["target_model_spec_declarations"] = (
            target_model_spec_declarations
        )
    else:
        scope_metadata["model_spec_declaration"] = model_spec_declaration
    model_bindings, model_binding_errors = corrected_model_scope_model_bindings(
        scope_metadata,
        target_result_declarations=target_result_declarations,
    )
    if model_binding_errors or model_bindings is None:
        return {}, [
            "governing model metadata " + error
            for error in model_binding_errors
        ]
    targets = sorted(model_bindings.target_model_spec_declarations)
    if not isinstance(audit_payload, dict):
        return {}, ["source-record audit payload must be an object"]

    raw_field_items = audit_payload.get("recursive_field_items")
    if not isinstance(raw_field_items, list):
        return {}, ["source-record audit requires a recursive_field_items list"]
    field_items: dict[str, dict[str, Any]] = {}
    field_paths: dict[str, tuple[str, ...]] = {}
    for index, raw_item in enumerate(raw_field_items):
        if not isinstance(raw_item, dict):
            errors.append(f"recursive_field_items[{index}] must be an object")
            continue
        key = str(raw_item.get("judgment_key") or "").strip()
        raw_path = str(raw_item.get("path") or "").strip()
        path_segments = tuple(segment.strip() for segment in raw_path.split(" -> "))
        if not key or key in field_items:
            errors.append(
                f"recursive_field_items[{index}] has a missing or duplicate judgment_key"
            )
            continue
        if (
            len(path_segments) < 2
            or any(not segment for segment in path_segments)
            or path_segments[-1] != key
        ):
            errors.append(
                f"recursive_field_items[{index}] lacks a structural path ending in its exact declaration"
            )
            continue
        field_items[key] = raw_item
        field_paths[key] = path_segments

    raw_semantic_items = audit_payload.get("semantic_model_items")
    if not isinstance(raw_semantic_items, list):
        return {}, errors + ["source-record audit requires a semantic_model_items list"]
    semantic_items_by_declaration: dict[str, dict[str, Any]] = {}
    for index, raw_item in enumerate(raw_semantic_items):
        if not isinstance(raw_item, dict):
            errors.append(f"semantic_model_items[{index}] must be an object")
            continue
        declaration = str(raw_item.get("qualified_declaration") or "").strip()
        if not declaration or declaration in semantic_items_by_declaration:
            errors.append(
                f"semantic_model_items[{index}] has a missing or duplicate fully qualified declaration"
            )
            continue
        semantic_items_by_declaration[declaration] = raw_item

    reachable: dict[str, dict[str, Any]] = {}
    for target in targets:
        model_spec = model_bindings.target_model_spec_declarations[target]
        model_prefix = f"{model_spec} ->"
        semantic_item = semantic_items_by_declaration.get(target)
        if semantic_item is None:
            errors.append(
                "corrected target `"
                + target
                + "` has no generated semantic-model item for its structural field graph"
            )
            continue
        surface = semantic_item.get("expanded_lean_surface")
        if not isinstance(surface, dict):
            errors.append(
                "corrected target `"
                + target
                + "` lacks an expanded_lean_surface for structural field reachability"
            )
            continue
        raw_paths = surface.get("record_field_types")
        if not isinstance(raw_paths, list):
            errors.append(
                "corrected target `"
                + target
                + "` lacks generated record_field_types for structural field reachability"
            )
            continue
        rooted_paths = 0
        for path_index, raw_path_item in enumerate(raw_paths):
            if not isinstance(raw_path_item, dict):
                errors.append(
                    f"corrected target `{target}` record_field_types[{path_index}] must be an object"
                )
                continue
            raw_path = str(raw_path_item.get("path") or "").strip()
            if not raw_path.startswith(model_prefix):
                continue
            rooted_paths += 1
            segments = tuple(segment.strip() for segment in raw_path.split(" -> "))
            if (
                len(segments) < 2
                or segments[0] != model_spec
                or any(not segment for segment in segments)
            ):
                errors.append(
                    f"corrected target `{target}` has malformed generated model-field path `{raw_path}`"
                )
                continue
            terminal = segments[-1]
            terminal_item = field_items.get(terminal)
            if terminal_item is None:
                errors.append(
                    "corrected target `"
                    + target
                    + "` generated model-field path terminates at `"
                    + terminal
                    + "`, which has no exact recursive-field item"
                )
                continue
            # Every intermediate edge must name a generated field declaration.
            # This is what makes the route transitive structural evidence rather
            # than a string prefix that happens to begin with the model name.
            missing_intermediate = [
                segment for segment in segments[1:-1] if segment not in field_items
            ]
            if missing_intermediate:
                errors.append(
                    "corrected target `"
                    + target
                    + "` generated model-field path has no exact recursive-field item for "
                    + ", ".join(sorted(set(missing_intermediate)))
                )
                continue
            terminal_field_path = field_paths.get(terminal, ())
            if len(terminal_field_path) < 2 or terminal_field_path[-1] != terminal:
                errors.append(
                    "corrected target `"
                    + target
                    + "` terminal field `"
                    + terminal
                    + "` has no structurally valid recursive-field path"
                )
                continue
            reachable[terminal] = terminal_item
        if rooted_paths == 0:
            errors.append(
                "corrected target `"
                + target
                + "` has no generated record-field path rooted at its mapped governing model `"
                + model_spec
                + "`"
            )
    return reachable, errors


def component_corrected_scope_findings(
    folder: Path,
    status: str,
    raw_scope: dict[str, Any],
    status_payload: dict[str, Any],
) -> list[Finding]:
    """Validate an approved component boundary without granting source credit.

    A component scope records exactly what the user approved, but it is not a
    substitute for the ordinary source-map, fidelity-ledger, source-record, or
    closeout checks.  In particular, it deliberately does not validate a
    semantic contract or return a value that any waiver path can consume.
    """

    findings: list[Finding] = []
    path = rel(folder / "status.json")

    def add(message: str) -> None:
        findings.append(Finding("ERROR", folder.name, path, message))

    if status in FULL_CLOSEOUT_STATUSES:
        add(
            "component_level_evidence_only formalization_scope cannot support "
            f"full-closeout status `{status}`"
        )
    if raw_scope.get("whole_paper_closeout_claimed") is not False:
        add(
            "component_level_evidence_only formalization_scope must set "
            "whole_paper_closeout_claimed to false"
        )
    if str(raw_scope.get("kind") or "").strip() != AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE:
        add(
            "component-level formalization_scope.kind must be "
            f"`{AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE}`"
        )
    if not str(raw_scope.get("scope_id") or "").strip():
        add("component-level formalization_scope requires a nonempty scope_id")
    if raw_scope.get("archival_equivalence_claimed") is not False:
        add(
            "component-level formalization_scope must set "
            "archival_equivalence_claimed to false"
        )
    _model_bindings, model_binding_errors = corrected_model_scope_model_bindings(
        raw_scope
    )
    for error in model_binding_errors:
        add("component-level formalization_scope " + error)

    approval = raw_scope.get("approval")
    if not isinstance(approval, dict):
        add("component-level formalization_scope requires approval metadata")
    else:
        approval_path = _paper_local_artifact_path(folder, approval.get("artifact_path"))
        approval_digest = str(approval.get("artifact_sha256") or "").strip().lower()
        if not str(approval.get("recorded_at") or "").strip():
            add("component corrected-target approval requires recorded_at")
        if not str(approval.get("statement") or "").strip():
            add("component corrected-target approval requires a precise statement")
        if approval_path is None or not approval_path.is_file():
            add("component corrected-target approval artifact_path must name an existing paper-local file")
        elif not SHA256_RE.fullmatch(approval_digest) or sha256_file(approval_path) != approval_digest:
            add("component corrected-target approval artifact_sha256 is stale or malformed")

    base_archive = raw_scope.get("base_archive")
    if not isinstance(base_archive, dict):
        add("component-level formalization_scope requires base_archive metadata")
    else:
        archive_path = _paper_local_artifact_path(folder, base_archive.get("path"))
        archive_digest = str(base_archive.get("sha256") or "").strip().lower()
        if archive_path is None or not archive_path.is_file():
            add("component corrected-target base_archive.path must name an existing paper-local archive")
        elif not SHA256_RE.fullmatch(archive_digest) or sha256_file(archive_path) != archive_digest:
            add("component corrected-target base_archive.sha256 is stale or malformed")

    correction_ids = _nonempty_string_list(raw_scope.get("correction_ids"))
    if correction_ids is None:
        add("component-level formalization_scope requires unique nonempty correction_ids")
    else:
        governing = {
            str(item.get("id") or "").strip()
            for item in status_payload.get("governing_corrections") or []
            if isinstance(item, dict) and str(item.get("id") or "").strip()
        }
        if not set(correction_ids).issubset(governing):
            add(
                "component-level formalization_scope.correction_ids must cite declared "
                "governing_corrections"
            )
    return findings


def _corrected_model_scope_contract_findings(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
    *,
    audit_payload_override: object = _UNSET,
    prevalidated_source_record_identity_error: object = _UNSET,
    validated_field_items_out: MutableMapping[str, dict[str, Any]] | None = None,
    artifact_snapshots_override: (
        Mapping[Path, EvidenceJSONSnapshot] | None
    ) = None,
) -> list[Finding]:
    """Validate an author-approved corrected target as a separate source scope.

    This is deliberately not a waiver for a stale source audit.  It requires a
    pinned author-approved correction artifact, a current structural
    source-record digest, complete semantic-dimension coverage, and a mapping
    for each expanded field of the corrected model record.  The archived TeX
    remains pinned as a distinct baseline and may not be claimed equivalent.
    """

    raw_scope = status_payload.get("formalization_scope")
    if raw_scope is None:
        return []
    severity = finding_severity(status)
    if not isinstance(raw_scope, dict):
        return [
            Finding(
                severity,
                folder.name,
                rel(folder / "status.json"),
                "formalization_scope must be an object when declared",
            )
        ]
    scope_role, scope_role_error = corrected_model_scope_role(raw_scope)
    if scope_role_error:
        return [
            Finding(severity, folder.name, rel(folder / "status.json"), scope_role_error)
        ]
    # This branch is intentionally before the legacy whole-paper contract.
    # Component metadata, even malformed beyond the role pair, must never fall
    # through to a waiver-capable path.
    if scope_role == COMPONENT_LEVEL_EVIDENCE_ONLY_SCOPE_ROLE:
        return component_corrected_scope_findings(
            folder, status, raw_scope, status_payload
        )
    kind = str(raw_scope.get("kind") or "").strip()
    if kind != AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE:
        return [
            Finding(
                severity,
                folder.name,
                rel(folder / "status.json"),
                "formalization_scope.kind must be "
                f"`{AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE}` when a corrected target is declared",
            )
        ]
    if scope_role != WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE:
        return [
            Finding(
                severity,
                folder.name,
                rel(folder / "status.json"),
                "formalization_scope has no waiver-capable whole-paper role",
            )
        ]

    findings: list[Finding] = []

    def artifact_snapshot(path: Path | None) -> EvidenceJSONSnapshot | None:
        if path is None or artifact_snapshots_override is None:
            return None
        try:
            return artifact_snapshots_override.get(path.resolve())
        except (OSError, RuntimeError):
            return None

    def artifact_digest(path: Path | None) -> str | None:
        if artifact_snapshots_override is None:
            if path is None or not path.exists():
                return None
            try:
                return sha256_file(path)
            except OSError:
                return None
        snapshot = artifact_snapshot(path)
        return snapshot.sha256 if snapshot is not None else None

    def add(message: str) -> None:
        findings.append(
            Finding(severity, folder.name, rel(folder / "status.json"), message)
        )

    scope_id = str(raw_scope.get("scope_id") or "").strip()
    if not scope_id:
        add("author-approved corrected formalization_scope requires a nonempty scope_id")
    if raw_scope.get("archival_equivalence_claimed") is not False:
        add(
            "author-approved corrected formalization_scope must set "
            "archival_equivalence_claimed to false"
        )
    targets = _nonempty_string_list(raw_scope.get("target_result_declarations"))
    if targets is None:
        add(
            "author-approved corrected formalization_scope requires unique nonempty "
            "target_result_declarations"
        )
        targets = []
    scope_model_bindings, scope_model_binding_errors = (
        corrected_model_scope_model_bindings(
            raw_scope,
            target_result_declarations=targets,
        )
    )
    for error in scope_model_binding_errors:
        add("author-approved corrected formalization_scope " + error)
    correction_ids = _nonempty_string_list(raw_scope.get("correction_ids"))
    if correction_ids is None:
        add(
            "author-approved corrected formalization_scope requires unique nonempty correction_ids"
        )
        correction_ids = []

    approval = raw_scope.get("approval")
    if not isinstance(approval, dict):
        add("author-approved corrected formalization_scope requires approval metadata")
        approval = {}
    approval_path = _paper_local_artifact_path(folder, approval.get("artifact_path"))
    approval_digest = str(approval.get("artifact_sha256") or "").strip().lower()
    if not str(approval.get("recorded_at") or "").strip():
        add("corrected-model approval requires recorded_at")
    if not str(approval.get("statement") or "").strip():
        add("corrected-model approval requires a precise statement")
    approval_actual_digest = artifact_digest(approval_path)
    if approval_path is None or approval_actual_digest is None:
        add("corrected-model approval artifact_path must name an existing paper-local file")
    if not SHA256_RE.fullmatch(approval_digest):
        add("corrected-model approval artifact_sha256 must be a SHA-256 digest")
    elif approval_actual_digest is not None and approval_actual_digest != approval_digest:
        add("corrected-model approval artifact_sha256 does not match its tracked artifact")

    base_archive = raw_scope.get("base_archive")
    if not isinstance(base_archive, dict):
        add("author-approved corrected formalization_scope requires base_archive metadata")
        base_archive = {}
    archive_path = _paper_local_artifact_path(folder, base_archive.get("path"))
    archive_digest = str(base_archive.get("sha256") or "").strip().lower()
    archive_actual_digest = artifact_digest(archive_path)
    if archive_path is None or archive_actual_digest is None:
        add("corrected-model base_archive.path must name an existing paper-local archive")
    if not SHA256_RE.fullmatch(archive_digest):
        add("corrected-model base_archive.sha256 must be a SHA-256 digest")
    elif archive_actual_digest is not None and archive_actual_digest != archive_digest:
        add("corrected-model base_archive.sha256 does not match its pinned archive")

    corrections = status_payload.get("governing_corrections")
    if not isinstance(corrections, list):
        add("corrected-model status requires a governing_corrections list")
        corrections = []
    correction_by_id: dict[str, dict[str, Any]] = {}
    for index, correction in enumerate(corrections):
        if not isinstance(correction, dict):
            add(f"governing_corrections[{index}] must be an object")
            continue
        correction_id = str(correction.get("id") or "").strip()
        if not correction_id or correction_id in correction_by_id:
            add(f"governing_corrections[{index}] has a missing or duplicate id")
            continue
        correction_by_id[correction_id] = correction
        for key in ("clause", "source_anchor", "relation", "model_evidence"):
            if not str(correction.get(key) or "").strip():
                add(f"governing correction `{correction_id}` requires {key}")
        if correction.get("does_not_claim_archive_derivation") is not True:
            add(
                f"governing correction `{correction_id}` must explicitly reject an archive-derivation claim"
            )
    if correction_ids and set(correction_ids) != set(correction_by_id):
        add(
            "formalization_scope.correction_ids must exactly match governing_corrections ids"
        )
    correction_digest = governing_corrections_sha256(status_payload)
    if correction_digest is None:
        add("corrected-model status has no canonicalizable governing_corrections content")

    contract_ref = raw_scope.get("semantic_contract")
    if not isinstance(contract_ref, dict):
        add("author-approved corrected formalization_scope requires semantic_contract metadata")
        return findings
    contract_path = _paper_local_artifact_path(folder, contract_ref.get("path"))
    contract_digest = str(contract_ref.get("sha256") or "").strip().lower()
    contract_snapshot = artifact_snapshot(contract_path)
    contract_actual_digest = artifact_digest(contract_path)
    if contract_path is None or contract_actual_digest is None:
        add("corrected-model semantic_contract.path must name an existing paper-local file")
        return findings
    if not SHA256_RE.fullmatch(contract_digest):
        add("corrected-model semantic_contract.sha256 must be a SHA-256 digest")
        return findings
    if contract_actual_digest != contract_digest:
        add("corrected-model semantic_contract.sha256 does not match its tracked artifact")
        return findings
    contract = (
        contract_snapshot.payload
        if contract_snapshot is not None
        else load_json(contract_path)
    )
    if not isinstance(contract, dict):
        add("corrected-model semantic contract must be valid JSON")
        return findings
    contract_dimension_set = corrected_model_contract_dimensions(contract.get("schema"))
    if contract_dimension_set is None:
        add("corrected-model semantic contract has an unsupported schema")
        # Continue with the current shape only to provide useful diagnostics
        # for the remaining fields. The unsupported-schema finding is already
        # fail-closed.
        contract_dimension_set = CORRECTED_MODEL_SEMANTIC_DIMENSIONS
    expected_contract_values = {
        "scope_id": scope_id,
        "approval_artifact_sha256": approval_digest,
        "base_archive_sha256": archive_digest,
    }
    for key, expected in expected_contract_values.items():
        if str(contract.get(key) or "").strip().lower() != str(expected).strip().lower():
            add(f"corrected-model semantic contract `{key}` does not match formalization_scope")
    if _nonempty_string_list(contract.get("target_result_declarations")) != targets:
        add("corrected-model semantic contract target_result_declarations do not match scope")
    contract_model_bindings, contract_model_binding_errors = (
        corrected_model_scope_model_bindings(
            contract,
            target_result_declarations=targets,
        )
    )
    for error in contract_model_binding_errors:
        add("corrected-model semantic contract " + error)
    if (
        scope_model_bindings is not None
        and contract_model_bindings is not None
        and scope_model_bindings != contract_model_bindings
    ):
        add(
            "corrected-model semantic contract governing model bindings do not match "
            "formalization_scope"
        )
    if _nonempty_string_list(contract.get("correction_ids")) != correction_ids:
        add("corrected-model semantic contract correction_ids do not match scope")
    contract_correction_digest = str(
        contract.get("governing_corrections_sha256") or ""
    ).strip()
    if not SHA256_RE.fullmatch(contract_correction_digest) or contract_correction_digest != str(
        correction_digest or ""
    ):
        add(
            "corrected-model semantic contract governing_corrections_sha256 does not match "
            "the complete current correction content"
        )
    if contract.get("archival_equivalence_claimed") is not False:
        add("corrected-model semantic contract must set archival_equivalence_claimed to false")
    dimensions = contract.get("semantic_dimensions")
    if not isinstance(dimensions, list) or set(dimensions) != contract_dimension_set:
        add("corrected-model semantic contract must cover every semantic-model dimension")

    audit_path, audit_path_error = source_record_review_sidecar_path(
        folder,
        status_payload,
        config_field="source_record_audit_file",
        default_basename="source_record_audit.json",
    )
    if audit_path_error:
        add(audit_path_error)
        return findings
    assert audit_path is not None
    audit_payload = (
        load_json(audit_path)
        if audit_payload_override is _UNSET
        else audit_payload_override
    )
    if not isinstance(audit_payload, dict):
        add("corrected-model formalization requires a current source-record audit payload")
        return findings
    if prevalidated_source_record_identity_error is _UNSET:
        audit_identity_error = source_record_audit_identity_error(
            audit_payload,
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    else:
        audit_identity_error = str(prevalidated_source_record_identity_error)
    if audit_identity_error:
        add(
            "corrected-model formalization requires a current generated source-record "
            "audit: "
            + audit_identity_error
        )
    expected_import_module = f"{folder.name}.PaperInterface"
    if str(audit_payload.get("prompt_version") or "").strip() != (
        CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
    ):
        add("corrected-model formalization requires the current source-record prompt version")
    if str(audit_payload.get("import_module") or "").strip() != expected_import_module:
        add(
            "corrected-model formalization requires a source-record audit generated from "
            f"`{expected_import_module}`"
        )
    audit_scope = audit_payload.get("formalization_scope")
    if not isinstance(audit_scope, dict):
        add("source-record audit is missing the corrected formalization-scope context")
        return findings
    expected_scope_values = {
        "kind": AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE,
        "scope_id": scope_id,
        "approval_artifact_sha256": approval_digest,
        "base_archive_sha256": archive_digest,
    }
    for key, expected in expected_scope_values.items():
        if str(audit_scope.get(key) or "").strip().lower() != str(expected).strip().lower():
            add(f"source-record audit corrected scope `{key}` is stale or mismatched")
    if _nonempty_string_list(audit_scope.get("target_result_declarations")) != targets:
        add("source-record audit corrected scope target declarations are stale or mismatched")
    audit_model_bindings, audit_model_binding_errors = (
        corrected_model_scope_model_bindings(
            audit_scope,
            target_result_declarations=targets,
        )
    )
    for error in audit_model_binding_errors:
        add("source-record audit corrected scope " + error)
    if (
        scope_model_bindings is not None
        and audit_model_bindings is not None
        and scope_model_bindings != audit_model_bindings
    ):
        add(
            "source-record audit corrected scope governing model bindings are stale "
            "or mismatched"
        )
    if _nonempty_string_list(audit_scope.get("correction_ids")) != correction_ids:
        add("source-record audit corrected scope correction ids are stale or mismatched")
    if str(audit_scope.get("governing_corrections_sha256") or "").strip() != str(
        correction_digest or ""
    ):
        add(
            "source-record audit corrected scope governing-correction content is stale or mismatched"
        )
    if audit_scope.get("archival_equivalence_claimed") is not False:
        add("source-record audit corrected scope must not claim archival equivalence")

    audit_digest = str(audit_payload.get("source_record_audit_sha256") or "").strip()
    audit_integrity_digest = str(
        audit_payload.get("source_record_audit_integrity_sha256") or ""
    ).strip()
    audit_scope_digest = str(audit_scope.get("scope_sha256") or "").strip()
    if not SHA256_RE.fullmatch(audit_digest):
        add("corrected-model source-record audit requires a SHA-256 audit digest")
    if not SHA256_RE.fullmatch(audit_integrity_digest):
        add(
            "corrected-model source-record audit requires a SHA-256 raw-integrity receipt"
        )
    if not SHA256_RE.fullmatch(audit_scope_digest):
        add("corrected-model source-record audit requires a SHA-256 formalization-scope digest")
    if str(contract.get("source_record_audit_sha256") or "").strip() != audit_digest:
        add("corrected-model semantic contract is stale for the current source-record audit digest")
    if str(contract.get("source_record_audit_integrity_sha256") or "").strip() != audit_integrity_digest:
        add(
            "corrected-model semantic contract is stale for the current source-record raw-integrity receipt"
        )
    if str(contract.get("source_record_scope_sha256") or "").strip() != str(
        audit_scope_digest
    ).strip():
        add("corrected-model semantic contract is stale for the current formalization-scope digest")

    expected_semantic_keys = {
        str(key).strip()
        for key in audit_payload.get("expected_semantic_model_judgment_keys") or []
        if str(key).strip()
    }
    semantic_items_by_key: dict[str, dict[str, Any]] = {}
    semantic_items_by_qualified: dict[str, dict[str, Any]] = {}
    raw_semantic_items = audit_payload.get("semantic_model_items")
    if not isinstance(raw_semantic_items, list) or not raw_semantic_items:
        add("corrected-model formalization requires generated semantic_model_items")
        raw_semantic_items = []
    for index, item in enumerate(raw_semantic_items):
        if not isinstance(item, dict):
            add(f"semantic_model_items[{index}] must be an object")
            continue
        key = str(item.get("judgment_key") or "").strip()
        qualified = str(item.get("qualified_declaration") or "").strip()
        freshness_mode, freshness_error = corrected_model_raw_item_freshness_mode(
            item
        )
        if not key or not qualified:
            add(
                f"semantic_model_items[{index}] requires judgment_key and "
                "qualified_declaration"
            )
            continue
        if freshness_error or freshness_mode is None:
            add(
                f"semantic_model_items[{index}] has invalid generated freshness metadata: "
                + (freshness_error or "unknown freshness mode")
            )
            continue
        if key in semantic_items_by_key or qualified in semantic_items_by_qualified:
            add(
                f"semantic_model_items[{index}] has a duplicate key or qualified declaration"
            )
            continue
        semantic_items_by_key[key] = item
        semantic_items_by_qualified[qualified] = item
    if expected_semantic_keys != set(semantic_items_by_key):
        add(
            "corrected-model source-record audit must expose exactly one current "
            "semantic item for every expected semantic-model key"
        )
    available_local_declarations = {
        str(declaration).strip()
        for declaration in audit_payload.get("available_local_lean_declarations") or []
        if str(declaration).strip()
    }
    if not available_local_declarations:
        add(
            "corrected-model source-record audit requires available_local_lean_declarations "
            "for bridge identity validation"
        )

    review_surface = status_payload.get("review_surface")
    included_rows: set[str] = set()
    assumption_rows: set[str] = set()
    if isinstance(review_surface, dict):
        raw_included_rows = review_surface.get("include_names")
        if isinstance(raw_included_rows, list):
            included_rows = {
                name.strip()
                for name in raw_included_rows
                if isinstance(name, str) and name.strip()
            }
        raw_assumption_rows = review_surface.get("assumption_names")
        if isinstance(raw_assumption_rows, list):
            assumption_rows = {
                name.strip()
                for name in raw_assumption_rows
                if isinstance(name, str) and name.strip()
            }

    semantic_mapping_by_key: dict[str, dict[str, Any]] = {}
    semantic_item_mappings = contract.get("semantic_item_mappings")
    if not isinstance(semantic_item_mappings, list) or not semantic_item_mappings:
        add("corrected-model semantic contract requires semantic_item_mappings")
    else:
        mapped_semantic_keys: set[str] = set()
        for index, mapping in enumerate(semantic_item_mappings):
            if not isinstance(mapping, dict):
                add(f"semantic_item_mappings[{index}] must be an object")
                continue
            key = str(mapping.get("source_record_item_key") or "").strip()
            item = semantic_items_by_key.get(key)
            if not key or key in mapped_semantic_keys:
                add(
                    f"semantic_item_mappings[{index}] has a missing or duplicate source-record key"
                )
                continue
            mapped_semantic_keys.add(key)
            semantic_mapping_by_key[key] = mapping
            if item is None:
                add(
                    f"semantic_item_mappings[{index}] references a semantic item absent from "
                    "the current source-record audit"
                )
                continue
            freshness_error = corrected_model_mapping_freshness_error(mapping, item)
            if freshness_error:
                add(f"semantic_item_mappings[{index}] {freshness_error}")
            if str(mapping.get("qualified_declaration") or "").strip() != str(
                item.get("qualified_declaration") or ""
            ).strip():
                add(
                    f"semantic_item_mappings[{index}] does not name the generated fully "
                    "qualified declaration"
                )
            disposition = str(mapping.get("disposition") or "").strip()
            if disposition not in CORRECTED_MODEL_SEMANTIC_DISPOSITIONS:
                add(f"semantic_item_mappings[{index}] has an unsupported disposition")
            if disposition in {
                "author_approved_correction",
                "author_approved_additional_assumption",
            }:
                if str(mapping.get("approval_artifact_path") or "").strip() != str(
                    approval.get("artifact_path") or ""
                ).strip() or str(mapping.get("approval_artifact_sha256") or "").strip().lower() != approval_digest:
                    add(
                        f"semantic_item_mappings[{index}] must pin the current author-approval artifact"
                    )
            mapped_corrections = _nonempty_string_list(mapping.get("correction_ids"))
            if mapped_corrections is None or not set(mapped_corrections).issubset(
                set(correction_ids)
            ):
                add(
                    f"semantic_item_mappings[{index}] must cite declared correction_ids"
                )
            for required_key in ("source_anchor", "semantic_comparison", "lean_evidence"):
                value = str(mapping.get(required_key) or "").strip()
                if not value:
                    add(f"semantic_item_mappings[{index}] requires {required_key}")
                elif required_key == "source_anchor" and not CORRECTED_MODEL_SOURCE_LOCATOR_RE.search(value):
                    add(
                        f"semantic_item_mappings[{index}] source_anchor needs an exact "
                        "source or approval-artifact locator"
                    )
                elif required_key == "source_anchor":
                    for error in corrected_model_anchor_errors(folder, value):
                        add(f"semantic_item_mappings[{index}] {error}")
            dimensions = item.get("dimensions")
            responses = mapping.get("dimensions")
            expected_dimensions = {
                str(dimension.get("id") or "").strip()
                for dimension in (dimensions if isinstance(dimensions, list) else [])
                if isinstance(dimension, dict) and str(dimension.get("id") or "").strip()
            }
            if not expected_dimensions or not isinstance(responses, dict) or set(responses) != expected_dimensions:
                add(
                    f"semantic_item_mappings[{index}] must answer exactly every generated "
                    "semantic dimension"
                )
                continue
            for raw_dimension in dimensions if isinstance(dimensions, list) else []:
                if not isinstance(raw_dimension, dict):
                    continue
                dimension = str(raw_dimension.get("id") or "").strip()
                response = responses.get(dimension)
                if not isinstance(response, dict):
                    continue
                verdict = str(response.get("verdict") or "").strip()
                if verdict not in CORRECTED_MODEL_DIMENSION_VERDICTS:
                    add(
                        f"semantic_item_mappings[{index}].dimensions.{dimension} has an "
                        "unsupported verdict"
                    )
                detected = raw_dimension.get("detected_from_expanded_surface") is True
                if detected and verdict == "not_applicable":
                    add(
                        f"semantic_item_mappings[{index}].dimensions.{dimension} cannot mark "
                        "a generated semantic boundary not_applicable"
                    )
                for required_key in ("source_locator", "semantic_comparison", "lean_evidence"):
                    value = str(response.get(required_key) or "").strip()
                    if not value:
                        add(
                            f"semantic_item_mappings[{index}].dimensions.{dimension} requires "
                            f"{required_key}"
                        )
                    elif required_key == "source_locator" and not CORRECTED_MODEL_SOURCE_LOCATOR_RE.search(value):
                        add(
                            f"semantic_item_mappings[{index}].dimensions.{dimension} source_locator "
                            "needs an exact source or approval-artifact locator"
                        )
                    elif required_key == "source_locator":
                        for error in corrected_model_anchor_errors(folder, value):
                            add(
                                f"semantic_item_mappings[{index}].dimensions.{dimension} {error}"
                            )
                if detected and raw_dimension.get("requires_checked_bridge_when_detected") is True:
                    bridges = _nonempty_string_list(
                        response.get("checked_bridge_declarations")
                    )
                    if bridges is None or not all(
                        bridge in available_local_declarations for bridge in bridges
                    ):
                        add(
                            f"semantic_item_mappings[{index}].dimensions.{dimension} needs fully "
                            "qualified checked_bridge_declarations from the current local Lean closure"
                        )
        if mapped_semantic_keys != set(semantic_items_by_key):
            add(
                "semantic_item_mappings must cover exactly every generated semantic-model item"
            )

    target_mappings = contract.get("target_result_mappings")
    if not isinstance(target_mappings, list) or not target_mappings:
        add("corrected-model semantic contract requires target_result_mappings")
    else:
        mapped_targets: set[str] = set()
        for index, mapping in enumerate(target_mappings):
            if not isinstance(mapping, dict):
                add(f"target_result_mappings[{index}] must be an object")
                continue
            target = str(mapping.get("target_declaration") or "").strip()
            item = semantic_items_by_qualified.get(target)
            if not target or target in mapped_targets:
                add(f"target_result_mappings[{index}] has a missing or duplicate target_declaration")
                continue
            mapped_targets.add(target)
            if item is None:
                add(
                    f"target_result_mappings[{index}] does not match a generated fully "
                    "qualified PaperInterface semantic item"
                )
                continue
            row = str(item.get("row") or "").strip()
            if row not in included_rows:
                add(
                    f"target_result_mappings[{index}] targets a declaration that is not "
                    "an included PaperInterface review row"
                )
            if str(mapping.get("source_record_item_key") or "").strip() != str(
                item.get("judgment_key") or ""
            ).strip():
                add(
                    f"target_result_mappings[{index}] does not name the current expanded item"
                )
            freshness_error = corrected_model_mapping_freshness_error(mapping, item)
            if freshness_error:
                add(f"target_result_mappings[{index}] {freshness_error}")
            expected_model_spec = (
                scope_model_bindings.target_model_spec_declarations.get(target)
                if scope_model_bindings is not None
                else None
            )
            declared_model_spec = str(
                mapping.get("model_spec_declaration") or ""
            ).strip()
            if expected_model_spec is None:
                add(
                    f"target_result_mappings[{index}] has no validated target-to-model "
                    "scope binding"
                )
            elif (
                declared_model_spec != expected_model_spec
                and not (
                    not declared_model_spec
                    and scope_model_bindings is not None
                    and scope_model_bindings.uses_legacy_scalar
                )
            ):
                add(
                    f"target_result_mappings[{index}] must name its exact mapped "
                    "governing model_spec_declaration"
                )
            surface = item.get("expanded_lean_surface")
            roots = (
                {
                    str(root).strip()
                    for root in surface.get("record_roots") or []
                    if str(root).strip()
                }
                if isinstance(surface, dict)
                else set()
            )
            if expected_model_spec is not None and expected_model_spec not in roots:
                add(
                    f"target_result_mappings[{index}] target does not consume the exact "
                    "governing model record mapped to it in its expanded Lean surface"
                )
            mapped_corrections = _nonempty_string_list(mapping.get("correction_ids"))
            if mapped_corrections is None or not set(mapped_corrections).issubset(
                set(correction_ids)
            ):
                add(f"target_result_mappings[{index}] must cite declared correction_ids")
            for required_key in ("source_anchor", "semantic_comparison", "lean_evidence"):
                value = str(mapping.get(required_key) or "").strip()
                if not value:
                    add(f"target_result_mappings[{index}] requires {required_key}")
                elif required_key == "source_anchor" and not CORRECTED_MODEL_SOURCE_LOCATOR_RE.search(value):
                    add(
                        f"target_result_mappings[{index}] source_anchor needs an exact source "
                        "or approval-artifact locator"
                    )
                elif required_key == "source_anchor":
                    for error in corrected_model_anchor_errors(folder, value):
                        add(f"target_result_mappings[{index}] {error}")
            if str(mapping.get("approval_artifact_path") or "").strip() != str(
                approval.get("artifact_path") or ""
            ).strip() or str(mapping.get("approval_artifact_sha256") or "").strip().lower() != approval_digest:
                add(
                    f"target_result_mappings[{index}] must pin the current author-approval artifact"
                )
        if mapped_targets != set(targets):
            add(
                "target_result_mappings must cover exactly the corrected target_result_declarations"
            )

    expected_assumption_declarations = {
        str(item.get("qualified_declaration") or "").strip()
        for item in semantic_items_by_key.values()
        if str(item.get("row") or "").strip() in assumption_rows
        and str(item.get("qualified_declaration") or "").strip()
    }
    if assumption_rows and len(expected_assumption_declarations) != len(assumption_rows):
        add(
            "every explicit corrected-model assumption must have a generated fully qualified semantic item"
        )
    assumption_mappings = contract.get("assumption_mappings")
    if assumption_rows and (not isinstance(assumption_mappings, list) or not assumption_mappings):
        add("corrected-model semantic contract requires assumption_mappings")
    elif isinstance(assumption_mappings, list):
        mapped_assumptions: set[str] = set()
        for index, mapping in enumerate(assumption_mappings):
            if not isinstance(mapping, dict):
                add(f"assumption_mappings[{index}] must be an object")
                continue
            declaration = str(mapping.get("assumption_declaration") or "").strip()
            item = semantic_items_by_qualified.get(declaration)
            if not declaration or declaration in mapped_assumptions:
                add(f"assumption_mappings[{index}] has a missing or duplicate assumption_declaration")
                continue
            mapped_assumptions.add(declaration)
            if item is None or str(item.get("row") or "").strip() not in assumption_rows:
                add(
                    f"assumption_mappings[{index}] does not identify a configured explicit assumption"
                )
                continue
            if str(mapping.get("source_record_item_key") or "").strip() != str(
                item.get("judgment_key") or ""
            ).strip():
                add(
                    f"assumption_mappings[{index}] does not name the current expanded item"
                )
            freshness_error = corrected_model_mapping_freshness_error(mapping, item)
            if freshness_error:
                add(f"assumption_mappings[{index}] {freshness_error}")
            item_key = str(item.get("judgment_key") or "").strip()
            if item_key not in semantic_mapping_by_key:
                add(
                    f"assumption_mappings[{index}] lacks the required detailed semantic-item mapping"
                )
            disposition = str(mapping.get("disposition") or "").strip()
            if disposition not in CORRECTED_MODEL_ASSUMPTION_DISPOSITIONS:
                add(f"assumption_mappings[{index}] has an unsupported disposition")
            mapped_corrections = _nonempty_string_list(mapping.get("correction_ids"))
            if mapped_corrections is None or not set(mapped_corrections).issubset(
                set(correction_ids)
            ):
                add(f"assumption_mappings[{index}] must cite declared correction_ids")
            for required_key in ("source_anchor", "semantic_comparison", "lean_evidence"):
                value = str(mapping.get(required_key) or "").strip()
                if not value:
                    add(f"assumption_mappings[{index}] requires {required_key}")
                elif required_key == "source_anchor" and not CORRECTED_MODEL_SOURCE_LOCATOR_RE.search(value):
                    add(
                        f"assumption_mappings[{index}] source_anchor needs an exact source "
                        "or approval-artifact locator"
                    )
                elif required_key == "source_anchor":
                    for error in corrected_model_anchor_errors(folder, value):
                        add(f"assumption_mappings[{index}] {error}")
            if disposition in {
                "author_approved_correction",
                "author_approved_additional_assumption",
            }:
                if str(mapping.get("approval_artifact_path") or "").strip() != str(
                    approval.get("artifact_path") or ""
                ).strip() or str(mapping.get("approval_artifact_sha256") or "").strip().lower() != approval_digest:
                    add(
                        f"assumption_mappings[{index}] must pin the current author-approval artifact"
                    )
        if mapped_assumptions != expected_assumption_declarations:
            add(
                "assumption_mappings must cover exactly every configured explicit assumption"
            )
    contract_semantic_keys = _nonempty_string_list(contract.get("semantic_item_keys"))
    if contract_semantic_keys is None or set(contract_semantic_keys) != expected_semantic_keys:
        add(
            "corrected-model semantic contract must enumerate exactly the current expanded semantic-model rows"
        )
    groups = contract.get("semantic_review_groups")
    if not isinstance(groups, list) or not groups:
        add("corrected-model semantic contract requires semantic_review_groups")
    else:
        covered: set[str] = set()
        duplicate_coverage: set[str] = set()
        for index, group in enumerate(groups):
            if not isinstance(group, dict):
                add(f"semantic_review_groups[{index}] must be an object")
                continue
            group_keys = _nonempty_string_list(group.get("item_keys"))
            if group_keys is None:
                add(f"semantic_review_groups[{index}] requires unique nonempty item_keys")
                continue
            for key in group_keys:
                if key in covered:
                    duplicate_coverage.add(key)
                covered.add(key)
            group_corrections = _nonempty_string_list(group.get("correction_ids"))
            if group_corrections is None or not set(group_corrections).issubset(set(correction_ids)):
                add(f"semantic_review_groups[{index}] must cite declared correction_ids")
            responses = group.get("dimensions")
            if not isinstance(responses, dict) or set(responses) != contract_dimension_set:
                add(f"semantic_review_groups[{index}] must cover every semantic dimension")
                continue
            for dimension, response in responses.items():
                if not isinstance(response, dict) or not all(
                    str(response.get(key) or "").strip()
                    for key in ("disposition", "rationale", "lean_evidence")
                ):
                    add(
                        f"semantic_review_groups[{index}].dimensions.{dimension} requires "
                        "disposition, rationale, and lean_evidence"
                    )
        if covered != expected_semantic_keys:
            add("semantic_review_groups must cover each current semantic-model row exactly once")
        if duplicate_coverage:
            add("semantic_review_groups duplicate semantic-model row coverage")

    if scope_model_bindings is None:
        field_items: dict[str, dict[str, Any]] = {}
        field_graph_errors = ["cannot resolve validated governing model bindings"]
    else:
        field_items, field_graph_errors = corrected_model_transitively_reachable_field_items(
            audit_payload,
            target_result_declarations=targets,
            **corrected_model_scope_model_metadata(scope_model_bindings),
        )
    for error in field_graph_errors:
        add("corrected-model structural field graph " + error)
    reachable_model_field_keys = set(field_items)
    mappings = contract.get("model_field_mappings")
    if not isinstance(mappings, list) or not mappings:
        add("corrected-model semantic contract requires model_field_mappings")
    else:
        mapped_keys: set[str] = set()
        for index, mapping in enumerate(mappings):
            if not isinstance(mapping, dict):
                add(f"model_field_mappings[{index}] must be an object")
                continue
            key = str(mapping.get("source_record_item_key") or "").strip()
            correction_id = str(mapping.get("correction_id") or "").strip()
            if not key or key in mapped_keys:
                add(f"model_field_mappings[{index}] has a missing or duplicate source-record key")
                continue
            mapped_keys.add(key)
            if key not in field_items:
                add(
                    f"model_field_mappings[{index}] references a field absent from the "
                    "current transitive governing-model field graph"
                )
            else:
                freshness_error = corrected_model_mapping_freshness_error(
                    mapping, field_items[key]
                )
                if freshness_error:
                    add(f"model_field_mappings[{index}] {freshness_error}")
            if correction_id not in correction_by_id:
                add(f"model_field_mappings[{index}] cites an undeclared correction_id")
            for required_key in ("semantic_role", "rationale", "lean_evidence"):
                if not str(mapping.get(required_key) or "").strip():
                    add(f"model_field_mappings[{index}] requires {required_key}")
        if mapped_keys != reachable_model_field_keys:
            add(
                "model_field_mappings must cover exactly every expanded corrected-model "
                "field reachable from the governing model record"
            )
    if not findings and validated_field_items_out is not None:
        validated_field_items_out.clear()
        validated_field_items_out.update(field_items)
    return findings


def corrected_model_scope_contract_findings(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
) -> list[Finding]:
    """Validate corrected scope without accepting prevalidated caller evidence."""

    return _corrected_model_scope_contract_findings(folder, status, status_payload)


def author_approved_corrected_scope_contract_is_current(
    folder: Path, status_payload: dict[str, Any]
) -> bool:
    """Whether a waiver-capable whole-paper contract is current.

    Component-only receipts are useful evidence, but intentionally return
    ``False`` here so no caller can use them to exempt source obligations.
    """

    scope = author_approved_corrected_scope(status_payload)
    if scope is None:
        return False
    scope_role, scope_role_error = corrected_model_scope_role(scope)
    if scope_role_error or scope_role != WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE:
        return False

    return not (
        corrected_model_scope_contract_findings(
            folder, str(status_payload.get("status") or ""), status_payload
        )
    )


def current_author_approved_corrected_model_field_items(
    folder: Path, status_payload: dict[str, Any]
) -> dict[str, dict[str, Any]] | None:
    """Return the exact current transitive governing-model field graph.

    Consumers that need to exempt a nested corrected-model input must use this
    helper rather than reconstructing reachability from declaration spelling.
    ``None`` means that either no corrected scope is active, its full semantic
    contract is stale/invalid, or the checked contract no longer maps every
    structurally reachable field with the required freshness receipt.
    """

    if not author_approved_corrected_scope_contract_is_current(folder, status_payload):
        return None
    scope = author_approved_corrected_scope(status_payload)
    if scope is None:
        return None
    targets = _nonempty_string_list(scope.get("target_result_declarations"))
    contract_ref = scope.get("semantic_contract")
    if targets is None or not isinstance(contract_ref, dict):
        return None
    model_bindings, model_binding_errors = corrected_model_scope_model_bindings(
        scope,
        target_result_declarations=targets,
    )
    if model_binding_errors or model_bindings is None:
        return None
    contract_path = _paper_local_artifact_path(folder, contract_ref.get("path"))
    contract = load_json(contract_path) if contract_path is not None else None
    if not isinstance(contract, dict):
        return None
    audit_path, audit_path_error = source_record_review_sidecar_path(
        folder,
        status_payload,
        config_field="source_record_audit_file",
        default_basename="source_record_audit.json",
    )
    if audit_path_error or audit_path is None:
        return None
    audit_payload = load_json(audit_path)
    if not isinstance(audit_payload, dict):
        return None
    field_items, graph_errors = corrected_model_transitively_reachable_field_items(
        audit_payload,
        target_result_declarations=targets,
        **corrected_model_scope_model_metadata(model_bindings),
    )
    if graph_errors or not field_items:
        return None
    raw_mappings = contract.get("model_field_mappings")
    if not isinstance(raw_mappings, list):
        return None
    mapped_keys: set[str] = set()
    for mapping in raw_mappings:
        if not isinstance(mapping, dict):
            return None
        key = str(mapping.get("source_record_item_key") or "").strip()
        item = field_items.get(key)
        if (
            not key
            or item is None
            or key in mapped_keys
            or corrected_model_mapping_freshness_error(mapping, item)
        ):
            return None
        mapped_keys.add(key)
    if mapped_keys != set(field_items):
        return None
    return field_items


def semantic_context_requirement_nodes(
    payload: dict[str, Any],
) -> Iterable[tuple[str, str, int, object]]:
    """Yield declared source-map semantic context without inspecting Lean names.

    A context requirement belongs to a source inventory item, but it is not an
    additional result and cannot receive proof or coverage credit. The source
    item key is returned only as a stable inventory trace; callers must compare
    the literal context kind, explanation, and byte-pinned source excerpt with
    expanded Lean semantics rather than treating the key as mathematical
    evidence.
    """

    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return
    for raw_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict):
            continue
        if SEMANTIC_CONTEXT_REQUIREMENTS_KEY not in raw_item:
            continue
        raw_requirements = raw_item.get(SEMANTIC_CONTEXT_REQUIREMENTS_KEY)
        if not isinstance(raw_requirements, list):
            continue
        source_key = str(raw_key)
        for index, requirement in enumerate(raw_requirements):
            yield (
                f"$.items.{source_key}.{SEMANTIC_CONTEXT_REQUIREMENTS_KEY}[{index}]",
                source_key,
                index,
                requirement,
            )


def semantic_context_requirements(payload: dict[str, Any]) -> list[dict[str, Any]]:
    """Project declared source context into a deterministic audit-only payload.

    This projection intentionally carries no Lean declaration, proof route, or
    coverage disposition. It preserves the exact byte-pinned source anchor so
    the source-record judge can use the context semantically without being able
    to mistake a declaration/function name for evidence.
    """

    items: list[dict[str, Any]] = []
    for _path, source_key, index, raw_requirement in semantic_context_requirement_nodes(
        payload
    ):
        if not isinstance(raw_requirement, dict):
            continue
        item = {
            "source_item_key": source_key,
            "requirement_index": index,
            "source_anchor_evidence": raw_requirement.get(
                "source_anchor_evidence"
            ),
        }
        # Do not synthesize absent legacy fields.  That keeps historical
        # projections byte-stable while letting a role-only v11 context be an
        # explicitly source-text-only object.
        for field in ("kind", "source_location", "explanation"):
            if field in raw_requirement:
                item[field] = raw_requirement.get(field)
        # The bounded role is part of the v11 semantic input contract.  Keep
        # it out of legacy projections when absent so historical raw receipts
        # remain replayable until that paper enters the v11 re-audit lane.
        if "semantic_role" in raw_requirement:
            item["semantic_role"] = raw_requirement.get("semantic_role")
        # Preserve source-scoped contracts in the judge-visible projection.
        # Do not add absent/null fields to ordinary contexts: those existing
        # v10 context digests must remain byte-for-byte stable.
        if (
            raw_requirement.get("kind")
            == EQUALITY_DEFINED_PARTITION_CONTEXT_KIND
        ):
            item[EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD] = raw_requirement.get(
                EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD
            )
        if (
            raw_requirement.get("kind")
            == STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_KIND
        ):
            item[STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD] = (
                raw_requirement.get(STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD)
            )
        if raw_requirement.get("kind") == CONDITIONING_INFORMATION_CONTEXT_KIND:
            item[CONDITIONING_INFORMATION_CONTRACT_FIELD] = raw_requirement.get(
                CONDITIONING_INFORMATION_CONTRACT_FIELD
            )
        if raw_requirement.get("kind") == SOURCE_MODEL_DERIVATION_CONTEXT_KIND:
            item[SOURCE_MODEL_DERIVATION_CONTRACT_FIELD] = raw_requirement.get(
                SOURCE_MODEL_DERIVATION_CONTRACT_FIELD
            )
        items.append(item)
    return sorted(
        items,
        key=lambda item: (
            str(item.get("source_item_key") or ""),
            int(item.get("requirement_index") or 0),
        ),
    )


def check_duplicate_sidecars(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    differing: list[str] = []
    identical: list[str] = []
    for basename in AUDIT_SIDECARS:
        if (
            context is not None
            and context.v11_lean_claim_graph_selected
            and basename in V11_NONAUTHORITATIVE_LEGACY_SIDECARS
        ):
            continue
        legacy = folder / basename
        organized = folder / "audit" / basename
        if context is not None:
            legacy_snapshot = context.json_snapshot(legacy)
            organized_snapshot = context.json_snapshot(organized)
            legacy_digest = (
                legacy_snapshot.sha256 if legacy_snapshot is not None else None
            )
            organized_digest = (
                organized_snapshot.sha256 if organized_snapshot is not None else None
            )
            if legacy_digest is None or organized_digest is None:
                continue
            same_bytes = legacy_digest == organized_digest
        else:
            if not legacy.exists() or not organized.exists():
                continue
            same_bytes = legacy.read_bytes() == organized.read_bytes()
        if same_bytes:
            identical.append(basename)
        else:
            differing.append(basename)

    findings: list[Finding] = []
    if differing:
        findings.append(
            Finding(
                finding_severity(status),
                folder.name,
                rel(folder / "audit"),
                "legacy-root and canonical audit sidecars diverge: " + ", ".join(differing),
            )
        )
    if identical:
        findings.append(
            Finding(
                "WARN",
                folder.name,
                rel(folder / "audit"),
                "byte-identical legacy sidecars still duplicate the canonical audit copy: "
                + ", ".join(identical),
            )
        )
    return findings


def historical_statement_manifest_replay_evidence_findings(
    folder: Path,
    _status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Run the no-Lean persisted-artifact gate only when a sidecar uses it.

    Ordinary papers never pay for this replay check.  A transported statement
    receipt, however, is evidence only while its historical carrier/authority,
    archive, current source-record closure, and static Git/current-file recipe
    can all be reopened from their byte-pinned retrieval coordinates.
    """

    if (
        context is not None
        and context.v11_lean_claim_graph_selected
    ):
        return []

    try:
        from scripts import statement_receipt_reissue as reissue
    except Exception as exc:  # pragma: no cover - import boundary is fail-closed.
        return [
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "audit" / "statement_match_llm.json"),
                "historical statement-manifest replay integrity gate is unavailable: "
                f"{type(exc).__name__}",
            )
        ]
    match_path = transaction_sidecar(folder, "statement_match_llm.json", context)
    match_payload = transaction_json(match_path, context)
    items = match_payload.get("items") if isinstance(match_payload, Mapping) else None
    if not isinstance(items, Mapping) or not any(
        isinstance(entry, Mapping)
        and reissue.HISTORICAL_REPLAY_PROVENANCE_FIELD in entry
        for entry in items.values()
    ):
        return []
    try:
        errors = reissue.historical_manifest_replay_persisted_evidence_errors(folder)
    except Exception as exc:  # noqa: BLE001 - evidence-gate exceptions fail closed.
        errors = [f"static replay validator raised {type(exc).__name__}"]
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(match_path),
            "historical statement-manifest replay integrity failure: " + error,
        )
        for error in errors
    ]


def check_placeholder_evidence(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    findings: list[Finding] = []
    v11_selected = bool(
        context is not None and context.v11_lean_claim_graph_selected
    )
    for basename in AUDIT_SIDECARS:
        if (
            v11_selected
            and basename in V11_NONAUTHORITATIVE_LEGACY_SIDECARS
        ):
            # These files remain historical provenance after a paper selects a
            # v11 raw-source/expanded-Spec lane. Whether that lane passes is a
            # separate question decided by its own strict validators; replaying
            # name-based v10 prose would double-count an obsolete surface and
            # can mask the actual v11 failure.
            continue
        path = transaction_sidecar(folder, basename, context)
        payload = transaction_json(path, context)
        if payload is None:
            continue
        placeholders: list[str] = []
        name_only: list[str] = []
        for key_path, value in walk_values(payload):
            if not key_path or not isinstance(value, str):
                continue
            leaf = key_path[-1]
            dotted = ".".join(key_path)
            if leaf in {"source_location", "source_evidence", "source_note", "source_status"}:
                if PLACEHOLDER_SOURCE_RE.search(value):
                    placeholders.append(dotted)
            if leaf == "reason" and NAME_ONLY_REASON_RE.search(value):
                name_only.append(dotted)
        if placeholders:
            findings.append(
                Finding(
                    finding_severity(status),
                    folder.name,
                    rel(path),
                    f"{len(placeholders)} placeholder/generic source-provenance value(s): "
                    + ", ".join(placeholders[:5])
                    + ("; ..." if len(placeholders) > 5 else ""),
                )
            )
        if name_only:
            findings.append(
                Finding(
                    finding_severity(status),
                    folder.name,
                    rel(path),
                    f"{len(name_only)} coverage reason(s) use name matching as semantic evidence: "
                    + ", ".join(name_only[:5])
                    + ("; ..." if len(name_only) > 5 else ""),
                )
            )
    return findings


def coverage_row_signature_pin_findings(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Check the structural half of v6 direct-coverage signature binding.

    This fast integrity audit intentionally does not run Lean.  It ensures that
    a v6 direct source-to-row claim records one syntactically valid signature
    pin for exactly each named row.  ``review_dashboard.py`` recomputes the
    current normalized elaborated manifest and rejects a stale pin, so neither
    check treats row names or source routes as semantic evidence.
    """

    if context is not None and context.v11_lean_claim_graph_selected:
        return []

    path = transaction_sidecar(folder, "paper_coverage_llm.json", context)
    payload = transaction_json(path, context)
    if not isinstance(payload, dict):
        return []
    if (
        str(payload.get("prompt_version") or "").strip()
        != PAPER_COVERAGE_ROW_SIGNATURE_PROMPT_VERSION
    ):
        return []

    malformed: list[str] = []
    for source_key, item in item_entries(payload):
        coverage = str(
            item.get("coverage")
            or item.get("judgment")
            or item.get("verdict")
            or item.get("status")
            or ""
        ).strip().lower().replace("-", "_")
        coverage = re.sub(r"\s+", "_", coverage)
        if coverage in {"match", "matches", "yes", "true", "represented", "present"}:
            coverage = "covered"
        elif coverage in {
            "conditional",
            "visible_premise_boundary",
            "covered_conditionally",
            "additional_assumption",
            "covered_with_additional_assumption",
        }:
            coverage = "conditional_boundary"
        if coverage not in DIRECT_PAPER_COVERAGE_JUDGMENTS:
            continue
        raw_rows = item.get("review_rows")
        if isinstance(raw_rows, list):
            rows = [str(row).strip() for row in raw_rows if str(row).strip()]
        elif raw_rows is None:
            rows = []
        else:
            rows = [
                value.strip()
                for value in str(raw_rows).split(",")
                if value.strip()
            ]
        # A no-row direct verdict is separately rejected by the coverage audit.
        if not rows:
            continue
        raw_pins = item.get("review_row_signature_sha256")
        if not isinstance(raw_pins, dict):
            malformed.append(
                f"{source_key}: missing review_row_signature_sha256 object"
            )
            continue
        pins = {
            str(name).strip(): value
            for name, value in raw_pins.items()
            if str(name).strip()
        }
        if len(set(rows)) != len(rows):
            malformed.append(f"{source_key}: duplicate review_rows entry")
        if set(pins) != set(rows):
            malformed.append(
                f"{source_key}: review_row_signature_sha256 keys do not exactly match review_rows"
            )
        for row in sorted(set(rows)):
            digest = pins.get(row)
            if not isinstance(digest, str) or not SHA256_RE.fullmatch(digest.strip()):
                malformed.append(
                    f"{source_key} -> {row}: missing or malformed Lean signature digest"
                )
    if not malformed:
        return []
    return [
        Finding(
            finding_severity(status),
            folder.name,
            rel(path),
            f"{len(malformed)} v5 direct-coverage row-signature pin error(s): "
            + "; ".join(malformed[:4])
            + ("; ..." if len(malformed) > 4 else ""),
        )
    ]


def corrected_target_coverage_findings(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Reject coverage that launders a corrected target into ordinary proof credit.

    This fast lane does not inspect Lean. It binds a source-to-row coverage
    verdict to the archival and corrected record hashes before the dashboard
    performs its fuller semantic and elaborated-signature review.
    """

    if context is not None and context.v11_lean_claim_graph_selected:
        # The selected v11 screening owns the archival-source/corrected-Spec
        # route. A failed current judgment still blocks through that lane; the
        # older aggregate coverage row is historical and cannot become fallback
        # acceptance evidence.
        return []
    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    map_payload = transaction_json(map_path, context)
    if not isinstance(map_payload, dict):
        return []
    map_items = map_payload.get("items")
    if not isinstance(map_items, dict):
        return []
    presentation_aliases, _alias_errors = source_presentation_aliases(map_items)
    corrected_items = {
        str(key).strip(): item
        for key, item in map_items.items()
        if isinstance(item, dict)
        and str(key).strip() not in presentation_aliases
        and str(item.get("coverage_status") or "").strip().lower()
        == CORRECTED_SOURCE_STATEMENT_STATUS
        and corrected_target_primary_declaration(item) is not None
    }
    if not corrected_items:
        return []
    coverage_path = transaction_sidecar(folder, "paper_coverage_llm.json", context)
    coverage_payload = transaction_json(coverage_path, context)
    if not isinstance(coverage_payload, dict):
        return []
    raw_items = coverage_payload.get("items")
    if not isinstance(raw_items, dict):
        return []

    malformed: list[str] = []
    for key, target_item in corrected_items.items():
        raw_coverage = raw_items.get(key)
        if not isinstance(raw_coverage, dict):
            continue
        primary_declaration = corrected_target_primary_declaration(target_item)
        if primary_declaration is None:
            malformed.append(
                f"{key}: source map has no sole corrected-target endpoint in lean_declarations"
            )
            continue
        coverage = re.sub(
            r"\s+",
            "_",
            str(raw_coverage.get("coverage") or "").strip().lower().replace("-", "_"),
        )
        if coverage != CORRECTED_TARGET_COVERAGE:
            malformed.append(
                f"{key}: corrected source item uses `{coverage or 'missing'}` instead of `{CORRECTED_TARGET_COVERAGE}`"
            )
            continue
        target = target_item.get("corrected_target")
        if not isinstance(target, dict):
            # Map validation provides the primary structural diagnosis.
            continue
        target_statement = re.sub(
            r"\s+", " ", str(target.get("statement") or "").strip()
        )
        archival_statement = re.sub(
            r"\s+", " ", str(target_item.get("statement") or "").strip()
        )
        expected_target_digest = hashlib.sha256(target_statement.encode("utf-8")).hexdigest()
        expected_archival_digest = hashlib.sha256(
            archival_statement.encode("utf-8")
        ).hexdigest()
        if str(raw_coverage.get("target_kind") or "").strip().lower() != CORRECTED_TARGET_ROUTE_KIND:
            malformed.append(f"{key}: missing target_kind approved_corrected_target")
        raw_rows = raw_coverage.get("review_rows")
        if isinstance(raw_rows, list):
            review_rows = [str(row).strip() for row in raw_rows if str(row).strip()]
        elif raw_rows is None:
            review_rows = []
        else:
            review_rows = [
                value.strip() for value in str(raw_rows).split(",") if value.strip()
            ]
        direct_owner_matches = corrected_target_coverage_rows_match_primary(
            primary_declaration,
            review_rows,
            map_items,
            folder.name,
        )
        contract_spec_matches = (
            corrected_target_coverage_rows_match_contract_spec(
                target_item,
                primary_declaration,
                review_rows,
                map_items,
                folder.name,
                semantic_contract_schema=map_payload.get("semantic_contract_schema"),
            )
            if not direct_owner_matches
            else False
        )
        if not direct_owner_matches and not contract_spec_matches:
            malformed.append(
                f"{key}: covered_corrected_target must link exactly the sole "
                "corrected-target endpoint in lean_declarations or its exact "
                "contract-backed transparent Spec"
            )
        if str(raw_coverage.get("statement_sha256") or "").strip().lower() != expected_target_digest:
            malformed.append(f"{key}: stale corrected target statement digest")
        if str(raw_coverage.get("archival_statement_sha256") or "").strip().lower() != expected_archival_digest:
            malformed.append(f"{key}: stale archival statement digest")
        if str(raw_coverage.get("corrected_target_sha256") or "").strip().lower() != corrected_target_record_digest(target):
            malformed.append(f"{key}: stale corrected-target record digest")
        governing = target.get("governing_defect_ids")
        recorded_governing = raw_coverage.get("governing_defect_ids")
        if (
            not isinstance(governing, list)
            or not isinstance(recorded_governing, list)
            or [str(value).strip() for value in recorded_governing]
            != [str(value).strip() for value in governing]
        ):
            malformed.append(
                f"{key}: governing source-statement defect ids do not match corrected target"
            )
        if raw_coverage.get("archival_equivalence_claimed") is not False:
            malformed.append(
                f"{key}: coverage must set archival_equivalence_claimed to false"
            )
    for key, raw_coverage in raw_items.items():
        if (
            not isinstance(raw_coverage, dict)
            or str(key).strip() in corrected_items
            or str(key).strip() in presentation_aliases
        ):
            continue
        coverage = re.sub(
            r"\s+",
            "_",
            str(raw_coverage.get("coverage") or "").strip().lower().replace("-", "_"),
        )
        if coverage == CORRECTED_TARGET_COVERAGE:
            malformed.append(
                f"{str(key).strip() or '<unnamed>'}: corrected-target coverage has no corrected source-map item"
            )
    if not malformed:
        return []
    return [
        Finding(
            finding_severity(status),
            folder.name,
            rel(coverage_path),
            f"{len(malformed)} corrected-target coverage pin error(s): "
            + "; ".join(malformed[:4])
            + ("; ..." if len(malformed) > 4 else ""),
        )
    ]


def formalized_note_rows(payload: dict[str, Any]) -> set[str]:
    raw = payload.get("formalized_note_rows")
    if raw is None:
        raw = payload.get("formalized_note_boundary_rows")
    if not isinstance(raw, list):
        return set()
    return {str(item).strip() for item in raw if str(item).strip()}


def is_formalized_note_boundary(
    row_key: str, item: dict[str, Any], note_rows: set[str]
) -> bool:
    status_impact = str(
        item.get("status_impact")
        or item.get("status_alignment")
        or item.get("boundary_status_impact")
        or ""
    ).strip()
    return status_impact == "formalized_note" or row_key in note_rows


NONWAIVABLE_FORMALIZED_NOTE_ASSUMPTION_JUDGMENTS = {
    "documented_additional_assumption",
    "partial_boundary",
    "not_paper_assumption",
}


def formalized_note_waives_assumption_judgment(
    row_key: str, item: dict[str, Any], note_rows: set[str]
) -> bool:
    """Return whether a note may retain this assumption-provenance judgment.

    A source correction or explicit source convention can be documented as a
    note when the advertised endpoint is actually proved.  A non-source
    assumption, an open partial boundary, or an assumption added to the paper
    cannot be converted into that note merely by listing its row in
    ``formalized_note_rows``.
    """

    judgment = str(item.get("judgment") or "").strip().lower()
    return (
        judgment not in NONWAIVABLE_FORMALIZED_NOTE_ASSUMPTION_JUDGMENTS
        and is_formalized_note_boundary(row_key, item, note_rows)
    )


def configured_assumption_review_rows(
    folder: Path, *, context: EvidenceRunContext | None = None
) -> set[str] | None:
    """Return the explicitly selected assumption-review rows, when available.

    ``assumption_match_llm.json`` is a current review artifact, not an archive
    of every historical premise a paper has ever exposed.  A status file with
    an explicit ``assumption_names`` list therefore defines the active rows
    whose provenance judgments can affect closeout.  This is only a routing
    control: it does not accept any mathematical claim based on a row name.

    Keep the legacy fail-closed behavior when the configuration is absent or
    malformed.  In that situation the gate cannot establish an active scope,
    so every serialized judgment remains relevant rather than being silently
    discarded.
    """

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    return configured_assumption_review_rows_from_status(status_payload)


def assumption_sidecar_entry_review_rows(
    row_key: str, item: Mapping[str, Any]
) -> set[str]:
    """Return explicit navigation coordinates declared by one sidecar entry.

    Schema-1 sidecars historically used their object key as the configured
    row identifier.  Newer entries may additionally carry an exact reviewed
    declaration field.  These coordinates select an already-configured audit
    row only; they never serve as source or semantic-match evidence.
    """

    rows = {str(row_key).strip()} if str(row_key).strip() else set()
    for field in (
        "assumption_declaration",
        "qualified_declaration",
        "reviewed_declaration",
    ):
        value = item.get(field)
        if isinstance(value, str) and value.strip():
            rows.add(value.strip())
    return rows


def active_assumption_sidecar_entries(
    folder: Path,
    payload: dict[str, Any],
    *,
    context: EvidenceRunContext | None = None,
) -> list[tuple[str, dict[str, Any]]]:
    """Filter provenance rows to the current explicit assumption surface.

    An empty configured set deliberately returns no active entries.  This
    prevents an archived, retired boundary in the canonical sidecar from
    demoting a paper after its proof is completed.  The source-record and
    Lean-premise gates remain responsible for detecting any currently exposed
    premise that was omitted from the configured surface.
    """

    entries = item_entries(payload)
    configured_rows = configured_assumption_review_rows(folder, context=context)
    if configured_rows is None:
        return entries
    return [
        (row_key, item)
        for row_key, item in entries
        if assumption_sidecar_entry_review_rows(row_key, item).intersection(
            configured_rows
        )
    ]


def author_approved_corrected_assumption_rows(
    folder: Path, *, context: EvidenceRunContext | None = None
) -> set[str]:
    """Return current assumption rows explicitly approved by a corrected scope.

    An author-approved corrected-model scope may legitimately add or repair a
    premise while retaining a full-closeout status.  Source-backed conditions
    in that same current contract are also safe when a provenance reviewer
    conservatively labels their composite predicate as additional.  The
    exception is narrow: it uses the current generated source-record row and
    the current semantic contract's exact assumption declaration, never a
    short declaration name or a source-looking predicate name.  Partial and
    unreviewed assumptions remain nonwaivable.
    """

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    corrected_scope_current = (
        context.corrected_scope_current
        if context is not None
        else author_approved_corrected_scope_contract_is_current(
            folder, status_payload
        )
    )
    if not corrected_scope_current:
        return set()
    scope = author_approved_corrected_scope(status_payload)
    if scope is None:
        return set()
    approval = scope.get("approval")
    if not isinstance(approval, dict):
        return set()
    approval_path = str(approval.get("artifact_path") or "").strip()
    approval_digest = str(approval.get("artifact_sha256") or "").strip().lower()
    contract_ref = scope.get("semantic_contract")
    if not isinstance(contract_ref, dict):
        return set()
    contract_path = _paper_local_artifact_path(folder, contract_ref.get("path"))
    contract = (
        transaction_json(contract_path, context)
        if contract_path is not None
        else None
    )
    audit_payload = (
        context.require_legacy_source_record_state().inputs.audit_snapshot.payload
        if context is not None
        else load_json(canonical_sidecar(folder, "source_record_audit.json"))
    )
    if not isinstance(contract, dict) or not isinstance(audit_payload, dict):
        return set()

    rows_by_declaration = {
        str(item.get("qualified_declaration") or "").strip(): str(
            item.get("row") or ""
        ).strip()
        for item in audit_payload.get("semantic_model_items") or []
        if isinstance(item, dict)
        and str(item.get("qualified_declaration") or "").strip()
        and str(item.get("row") or "").strip()
    }
    approved_rows: set[str] = set()
    for mapping in contract.get("assumption_mappings") or []:
        if not isinstance(mapping, dict):
            continue
        if str(mapping.get("disposition") or "").strip() not in {
            "literal_source_condition",
            "author_approved_correction",
            "author_approved_additional_assumption",
        }:
            continue
        disposition = str(mapping.get("disposition") or "").strip()
        if disposition != "literal_source_condition" and (
            str(mapping.get("approval_artifact_path") or "").strip()
            != approval_path
            or str(mapping.get("approval_artifact_sha256") or "").strip().lower()
            != approval_digest
        ):
            continue
        row = rows_by_declaration.get(
            str(mapping.get("assumption_declaration") or "").strip()
        )
        if row:
            approved_rows.add(row)
    return approved_rows


def current_v11_author_approved_assumption_rows(
    status_payload: Mapping[str, Any],
    assumptions: Mapping[str, Any],
) -> set[str]:
    """Return explicitly authorized corrected-model rows for a v11 transaction.

    Current schema-2 evidence does not inherit a superseded source-record
    contract merely to determine whether an already approved correction changes
    the paper's status.  It still requires an assumption-sidecar row to name
    the exact whole-paper corrected scope, approval artifact, and one or more
    declared correction ids.  This helper is used only by the builder-issued
    v11 lane; historical closeout retains the source-record-backed rule above.
    """

    scope = author_approved_corrected_scope(dict(status_payload))
    if scope is None:
        return set()
    scope_role, scope_role_error = corrected_model_scope_role(scope)
    if scope_role_error or scope_role != WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE:
        return set()
    approval = scope.get("approval")
    if not isinstance(approval, Mapping):
        return set()
    scope_id = str(scope.get("scope_id") or "").strip()
    approval_path = str(approval.get("artifact_path") or "").strip()
    approval_digest = str(approval.get("artifact_sha256") or "").strip().lower()
    declared_corrections = {
        str(correction.get("id") or "").strip()
        for correction in status_payload.get("governing_corrections") or []
        if isinstance(correction, Mapping)
        and str(correction.get("id") or "").strip()
    }
    if not scope_id or not approval_path or not SHA256_RE.fullmatch(approval_digest):
        return set()

    approved_rows: set[str] = set()
    for row_key, item in item_entries(dict(assumptions)):
        if str(item.get("judgment") or "").strip().lower() not in {
            "documented_additional_assumption",
            "documented_caveat",
        }:
            continue
        endorsement = item.get("author_approved_corrected_scope")
        if not isinstance(endorsement, Mapping):
            continue
        correction_ids = _nonempty_string_list(endorsement.get("correction_ids"))
        if (
            str(endorsement.get("scope_id") or "").strip() != scope_id
            or str(endorsement.get("approval_artifact_path") or "").strip()
            != approval_path
            or str(endorsement.get("approval_artifact_sha256") or "").strip().lower()
            != approval_digest
            or correction_ids is None
            or not set(correction_ids).issubset(declared_corrections)
        ):
            continue
        approved_rows.add(str(row_key).strip())
    return approved_rows


def check_full_closeout_assumption_alignment(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Keep non-source and partial assumptions out of either full status."""

    if status not in FULL_CLOSEOUT_STATUSES:
        return []
    assumption_path = transaction_sidecar(
        folder, "assumption_match_llm.json", context
    )
    assumptions = transaction_json(assumption_path, context) or {}
    assumption_note_rows = formalized_note_rows(assumptions)
    corrected_scope_rows = author_approved_corrected_assumption_rows(
        folder, context=context
    )
    current_v11_scope_rows = (
        current_v11_author_approved_assumption_rows(
            context.status_payload,
            assumptions,
        )
        if isinstance(context, V11EvidenceRunContext)
        else set()
    )
    non_source_assumptions = [
        item
        for key, item in active_assumption_sidecar_entries(
            folder, assumptions, context=context
        )
        if str(item.get("judgment") or "").strip().lower()
        in {
            "documented_additional_assumption",
            "documented_caveat",
            "not_paper_assumption",
            "partial_boundary",
        }
        and not formalized_note_waives_assumption_judgment(
            key, item, assumption_note_rows
        )
        and not (
            (key in corrected_scope_rows or key in current_v11_scope_rows)
            and str(item.get("judgment") or "").strip().lower()
            in {"documented_additional_assumption", "documented_caveat"}
        )
    ]
    if not non_source_assumptions:
        return []
    label = (
        "plain `formalized`"
        if status == PLAIN_FORMALIZED
        else f"full-closeout status `{status}`"
    )
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(assumption_path),
            f"{label} conflicts with {len(non_source_assumptions)} "
            "non-source/caveat assumption judgment(s)",
        )
    ]


def check_status_alignment(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    if status not in FULL_CLOSEOUT_STATUSES:
        return []

    findings = check_full_closeout_assumption_alignment(
        folder, status, context=context
    )
    if status != PLAIN_FORMALIZED:
        return findings

    # The v11 direct lane replaces the historical aggregate statement and
    # coverage sidecars with one raw-source-to-transparent-Spec screen per
    # current source claim.  Do not let an explicitly superseded v10
    # ``formalized note`` (which recorded an old presentation boundary) change
    # the mathematical status after the current v11 gate has independently
    # checked the same source surface.  The v11 validators run later in this
    # transaction and fail closed if their raw-source screens, paper-local
    # prerequisites, or material-library checks are absent or stale.
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    source_map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    source_map = transaction_json(source_map_path, context)
    if isinstance(source_map, dict) and raw_source_spec_screening_requested(
        status_payload, source_map, folder=folder
    ):
        return findings

    coverage_path = transaction_sidecar(folder, "paper_coverage_llm.json", context)
    coverage = transaction_json(coverage_path, context) or {}
    coverage_note_rows = formalized_note_rows(coverage)
    conditional_coverage: list[dict[str, Any]] = []
    for key, item in item_entries(coverage):
        coverage_status = str(
            item.get("coverage") or item.get("judgment") or ""
        ).strip().lower()
        if coverage_status not in {
            "conditional_boundary",
            "visible_premise_boundary",
            "covered_with_boundary",
            "partially_covered",
            "missing",
        }:
            continue
        if not is_formalized_note_boundary(key, item, coverage_note_rows):
            conditional_coverage.append(item)
            continue
        note_error = approved_source_convention_formalized_note_error(
            folder, item, context=context
        )
        if note_error:
            findings.append(
                Finding(
                    "ERROR",
                    folder.name,
                    rel(coverage_path),
                    f"formalized-note coverage row `{key}` is not a current approved "
                    f"source-convention receipt: {note_error}",
                )
            )
            conditional_coverage.append(item)
        elif coverage_status != "covered_with_boundary":
            findings.append(
                Finding(
                    "ERROR",
                    folder.name,
                    rel(coverage_path),
                    f"formalized-note coverage row `{key}` must be "
                    "`covered_with_boundary`, not a partial or missing result",
                )
            )
            conditional_coverage.append(item)
    if conditional_coverage:
        findings.append(
            Finding(
                "ERROR",
                folder.name,
                rel(coverage_path),
                f"plain `formalized` status conflicts with {len(conditional_coverage)} visible-premise/partial coverage row(s)",
            )
        )

    statement_path = transaction_sidecar(folder, "statement_match_llm.json", context)
    statement = transaction_json(statement_path, context) or {}
    statement_note_rows = formalized_note_rows(statement)
    conditional_statements: list[dict[str, Any]] = []
    for key, item in item_entries(statement):
        if (
            str(item.get("judgment") or "").strip().lower() != "mismatch"
            or str(item.get("resolution") or "").strip().lower()
            not in {"conditional_boundary", "visible_premise_boundary"}
        ):
            continue
        if not is_formalized_note_boundary(key, item, statement_note_rows):
            conditional_statements.append(item)
            continue
        note_error = approved_source_convention_formalized_note_error(
            folder, item, context=context
        )
        if note_error:
            findings.append(
                Finding(
                    "ERROR",
                    folder.name,
                    rel(statement_path),
                    f"formalized-note statement row `{key}` is not a current approved "
                    f"source-convention receipt: {note_error}",
                )
            )
            conditional_statements.append(item)
    if conditional_statements:
        findings.append(
            Finding(
                "ERROR",
                folder.name,
                rel(statement_path),
                f"plain `formalized` status conflicts with {len(conditional_statements)} accepted statement mismatch(es)",
            )
        )

    return findings


source_claim_atom_semantic_sha256 = (
    source_claim_atom_schema.source_claim_atom_semantic_sha256
)
source_claim_atoms_semantic_sha256 = (
    source_claim_atom_schema.source_claim_atoms_semantic_sha256
)


def _source_spec_semantic_basis_validation_errors(raw_basis: object) -> list[str]:
    """Validate an explicit, pinned supplemental semantic basis shape.

    This is intentionally not a route taxonomy.  A basis can document a
    correction, an additional assumption, or an external primitive, but it
    always has to expose the exact semantic statement and a version-pinned
    artifact/anchor.  It never receives credit merely because a caller calls
    it a convention, data object, or derivation.
    """

    if not isinstance(raw_basis, dict):
        return ["semantic_basis must be an object"]
    errors: list[str] = []
    unexpected = sorted(set(raw_basis) - SOURCE_SPEC_SEMANTIC_BASIS_FIELDS)
    if unexpected:
        errors.append("semantic_basis has unsupported field(s): " + ", ".join(unexpected))
    missing = sorted(SOURCE_SPEC_SEMANTIC_BASIS_FIELDS - set(raw_basis))
    if missing:
        errors.append("semantic_basis is missing required field(s): " + ", ".join(missing))
    artifact_path = raw_basis.get("artifact_path")
    if not isinstance(artifact_path, str) or not artifact_path.strip():
        errors.append("semantic_basis.artifact_path must be a nonempty paper-local path")
    artifact_sha = raw_basis.get("artifact_sha256")
    if not isinstance(artifact_sha, str) or not SHA256_RE.fullmatch(artifact_sha.strip()):
        errors.append("semantic_basis.artifact_sha256 must be a SHA-256 digest")
    locator = raw_basis.get("source_locator")
    if not isinstance(locator, str) or len(list(SOURCE_FILE_LINE_RE.finditer(locator))) != 1:
        errors.append("semantic_basis.source_locator must contain exactly one file:line anchor")
    if not meaningful_semantic_text(raw_basis.get("semantic_statement")):
        errors.append("semantic_basis.semantic_statement must be substantive source-facing text")
    return errors


source_spec_correspondence_item_identity_sha256 = (
    source_claim_atom_schema.source_spec_correspondence_item_identity_sha256
)


def source_spec_correspondence_validation_errors(
    raw_correspondence: object,
    *,
    raw_atoms: object,
    raw_contract: object,
) -> list[str]:
    """Validate the static, atom-level realization correspondence record.

    Lean later verifies that the supplied component hashes actually occur in
    the current elaborated `Spec` closure.  This fast validator intentionally
    checks only content-addressed structure and source atom completeness; it
    never grants credit from a source item key, a declaration name, a data
    classification, or free-form convention prose.
    """

    if not isinstance(raw_correspondence, dict):
        return ["source_spec_correspondence must be an object"]
    errors: list[str] = []
    unexpected = sorted(set(raw_correspondence) - SOURCE_SPEC_CORRESPONDENCE_FIELDS)
    if unexpected:
        errors.append(
            "source_spec_correspondence has unsupported field(s): "
            + ", ".join(unexpected)
        )
    missing = sorted(SOURCE_SPEC_CORRESPONDENCE_FIELDS - set(raw_correspondence))
    if missing:
        errors.append(
            "source_spec_correspondence is missing required field(s): "
            + ", ".join(missing)
        )
    if not schema_version_is_exact(
        raw_correspondence.get("schema"), SOURCE_SPEC_CORRESPONDENCE_SCHEMA
    ):
        errors.append(
            "source_spec_correspondence.schema must be "
            + str(SOURCE_SPEC_CORRESPONDENCE_SCHEMA)
        )
    for field in (
        "source_atoms_sha256",
        "spec_closure_sha256",
        "spec_surface_sha256",
        "closure_environment_sha256",
        "item_identity_sha256",
    ):
        value = raw_correspondence.get(field)
        if not isinstance(value, str) or not SHA256_RE.fullmatch(value.strip()):
            errors.append(f"source_spec_correspondence.{field} must be a SHA-256 digest")

    # A record in this validator is itself the strict realization
    # correspondence.  Its atom identities must therefore contain the exact
    # source-slice receipt, not merely a line locator plus an audited
    # paraphrase.  The inventory pass below verifies those digest bytes against
    # the current canonical artifact.
    atom_errors = source_claim_atoms_validation_errors(
        raw_atoms, require_source_quote=True
    )
    if atom_errors:
        errors.extend("source_claim_atoms " + error for error in atom_errors)
        atom_hashes: set[str] = set()
        atoms_digest = ""
    else:
        assert isinstance(raw_atoms, list)
        atom_hashes = {
            source_claim_atom_semantic_sha256(atom) for atom in raw_atoms
        }
        atoms_digest = source_claim_atoms_semantic_sha256(raw_atoms)
        if not atoms_digest:
            errors.append(
                "source_claim_atoms have duplicate or noncanonical semantic identities; "
                "split or distinguish the source clauses before binding them"
            )
        elif str(raw_correspondence.get("source_atoms_sha256") or "").strip().lower() != atoms_digest:
            errors.append(
                "source_spec_correspondence.source_atoms_sha256 does not match the "
                "current individually anchored source_claim_atoms content"
            )

    bindings = raw_correspondence.get("source_atom_bindings")
    seen_atoms: set[str] = set()
    component_to_bindings: dict[str, list[dict[str, Any]]] = {}
    if not isinstance(bindings, list) or not bindings:
        errors.append("source_spec_correspondence.source_atom_bindings must be a nonempty list")
    else:
        for index, raw_binding in enumerate(bindings):
            prefix = f"source_spec_correspondence.source_atom_bindings[{index}]"
            if not isinstance(raw_binding, dict):
                errors.append(f"{prefix} must be an object")
                continue
            unexpected_binding = sorted(
                set(raw_binding) - SOURCE_SPEC_ATOM_BINDING_FIELDS
            )
            if unexpected_binding:
                errors.append(
                    f"{prefix} has unsupported field(s): "
                    + ", ".join(unexpected_binding)
                )
            missing_binding = sorted(
                SOURCE_SPEC_ATOM_BINDING_FIELDS - {"overlap_justification"} - set(raw_binding)
            )
            if missing_binding:
                errors.append(
                    f"{prefix} is missing required field(s): "
                    + ", ".join(missing_binding)
                )
            atom_hash = str(raw_binding.get("source_atom_sha256") or "").strip().lower()
            if not SHA256_RE.fullmatch(atom_hash):
                errors.append(f"{prefix}.source_atom_sha256 must be a SHA-256 digest")
            elif atom_hash not in atom_hashes:
                errors.append(
                    f"{prefix}.source_atom_sha256 does not identify a current source claim atom"
                )
            elif atom_hash in seen_atoms:
                errors.append(
                    f"{prefix}.source_atom_sha256 duplicates a source atom; each atom has one repair handoff row"
                )
            else:
                seen_atoms.add(atom_hash)

            raw_components = raw_binding.get("spec_component_sha256s")
            if (
                not isinstance(raw_components, list)
                or not raw_components
                or any(
                    not isinstance(component, str)
                    or not SHA256_RE.fullmatch(component.strip())
                    for component in raw_components
                )
                or len({str(component).strip().lower() for component in raw_components})
                != len(raw_components)
            ):
                errors.append(
                    f"{prefix}.spec_component_sha256s must be a nonempty list of unique SHA-256 digests"
                )
            else:
                for component in raw_components:
                    component_to_bindings.setdefault(
                        str(component).strip().lower(), []
                    ).append(raw_binding)
            if not meaningful_semantic_text(raw_binding.get("semantic_bridge")):
                errors.append(
                    f"{prefix}.semantic_bridge must explain the source-clause to Spec-component correspondence"
                )

    if atom_hashes and seen_atoms != atom_hashes:
        missing_atoms = sorted(atom_hashes - seen_atoms)
        extra_atoms = sorted(seen_atoms - atom_hashes)
        detail: list[str] = []
        if missing_atoms:
            detail.append("missing " + ", ".join(missing_atoms[:3]))
        if extra_atoms:
            detail.append("unknown " + ", ".join(extra_atoms[:3]))
        errors.append(
            "source_spec_correspondence.source_atom_bindings must cover every current "
            "source claim atom exactly once" + (": " + "; ".join(detail) if detail else "")
        )
    for component, component_bindings in component_to_bindings.items():
        if len(component_bindings) <= 1:
            continue
        if any(
            not meaningful_semantic_text(binding.get("overlap_justification"))
            for binding in component_bindings
        ):
            errors.append(
                "source_spec_correspondence source atoms overlap on Spec component `"
                + component
                + "` without an explicit substantive overlap_justification on every row"
            )

    dispositions = raw_correspondence.get("closure_node_dispositions")
    if not isinstance(dispositions, list):
        errors.append("source_spec_correspondence.closure_node_dispositions must be a list")
    else:
        seen_components: set[str] = set()
        for index, raw_disposition in enumerate(dispositions):
            prefix = f"source_spec_correspondence.closure_node_dispositions[{index}]"
            if not isinstance(raw_disposition, dict):
                errors.append(f"{prefix} must be an object")
                continue
            unexpected_disposition = sorted(
                set(raw_disposition) - SOURCE_SPEC_NODE_DISPOSITION_FIELDS
            )
            if unexpected_disposition:
                errors.append(
                    f"{prefix} has unsupported field(s): "
                    + ", ".join(unexpected_disposition)
                )
            component = str(raw_disposition.get("closure_component_sha256") or "").strip().lower()
            if not SHA256_RE.fullmatch(component):
                errors.append(f"{prefix}.closure_component_sha256 must be a SHA-256 digest")
            elif component in seen_components:
                errors.append(
                    f"{prefix}.closure_component_sha256 duplicates a material closure node disposition"
                )
            else:
                seen_components.add(component)
            atom_hash = raw_disposition.get("source_atom_sha256")
            if atom_hash is not None:
                atom_text = str(atom_hash).strip().lower()
                if not SHA256_RE.fullmatch(atom_text) or atom_text not in atom_hashes:
                    errors.append(
                        f"{prefix}.source_atom_sha256 must identify a current source claim atom"
                    )
            basis = raw_disposition.get("semantic_basis")
            if atom_hash is None and basis is None:
                errors.append(
                    f"{prefix} needs a current source_atom_sha256 or an explicit pinned semantic_basis"
                )
            if basis is not None:
                errors.extend(
                    f"{prefix}." + error
                    for error in _source_spec_semantic_basis_validation_errors(basis)
                )
            node_pin = raw_disposition.get("pinned_declaration_identity_sha256")
            if node_pin is not None and (
                not isinstance(node_pin, str)
                or not SHA256_RE.fullmatch(node_pin.strip())
            ):
                errors.append(
                    f"{prefix}.pinned_declaration_identity_sha256 must be a SHA-256 digest when present"
                )

    expected_identity = source_spec_correspondence_item_identity_sha256(
        raw_contract, raw_correspondence
    )
    recorded_identity = str(raw_correspondence.get("item_identity_sha256") or "").strip().lower()
    if expected_identity and recorded_identity != expected_identity:
        errors.append(
            "source_spec_correspondence.item_identity_sha256 does not match the current "
            "atom-level source/Spec realization record"
        )
    return errors


def graph_native_source_spec_realization_receipts(
    root: Path,
    folder: Path,
    payload: Mapping[str, Any],
    selected: Iterable[tuple[str, Mapping[str, Any]]],
    *,
    evidence_context: object | None,
) -> tuple[dict[str, dict[str, str]], list[str]] | None:
    """Mint runtime realization identities from one accepted v11 graph.

    This is the current-protocol replacement for a second persisted
    ``source_spec_correspondence`` worksheet.  It is available only after the
    exact source-to-expanded-Spec and material-prerequisite reviews are current
    in the same builder-issued transaction.  Lean's graph then supplies the
    exact Spec/proof contract, recursive semantic closure, axiom closure, and
    imported environment.  Python merely projects those already validated
    identities into the runtime capability consumed by occurrence checks.

    ``None`` means that the current graph lane is not selected.  A selected
    graph returns explicit errors and never falls back to a legacy receipt or
    another Lean discovery pass.
    """

    if not isinstance(evidence_context, EvidenceRunContext):
        return None
    if (
        not evidence_context.issued_by_builder
        or evidence_context.folder.resolve() != folder.resolve()
        or getattr(evidence_context, "source_semantic_lane", "")
        != V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
    ):
        return None
    status_payload = getattr(evidence_context, "status_payload", None)
    if not isinstance(status_payload, Mapping):
        # Historical authority fixtures/contexts may carry a graph-shaped
        # capability without the current exact status snapshot.  They can
        # still use the established correspondence validator below, but they
        # cannot mint the new graph-native receipt.
        return None
    status = str(status_payload.get("status") or "").strip()
    semantic_current, semantic_error = v11_direct_semantic_review_state(
        folder,
        status,
        context=evidence_context,
    )
    if not semantic_current:
        return {}, [
            "current v11 semantic review is incomplete: "
            + (semantic_error or "unknown semantic-review failure")
        ]
    try:
        graph_surface = builder_issued_v11_lean_review_surface(
            folder,
            evidence_context,
        )
    except ValueError as exc:
        return {}, ["current v11 realization graph is unavailable: " + str(exc)]
    if graph_surface is None:
        return {}, ["current v11 realization graph is unavailable"]

    exact_items = evidence_context.statement_map.get("items")
    supplied_items = payload.get("items")
    if not isinstance(exact_items, Mapping) or not isinstance(
        supplied_items, Mapping
    ):
        return {}, ["current v11 statement map has no item ledger"]
    selected_rows = list(selected)
    selected_keys = {str(key) for key, _raw_item in selected_rows}
    for key, raw_item in selected_rows:
        if exact_items.get(key) != supplied_items.get(key) or exact_items.get(
            key
        ) != raw_item:
            return {}, [
                f"{key}: source item is not bound to this evidence transaction"
            ]

    receipts, errors = graph_native_realization_receipts_from_inventory(
        source_map=payload,
        inventory=graph_surface.declaration_inventory,
        context_input_sha256=v11_graph.graph_context_input_sha256(
            evidence_context,
            repository_root=ROOT,
        ),
        expected_paper_declarations=graph_surface.paper_semantic_targets,
        expected_library_declarations=graph_surface.library_semantic_targets,
    )
    if errors:
        return {}, errors
    selected_receipts = {
        key: receipts[key] for key in sorted(selected_keys) if key in receipts
    }
    if set(selected_receipts) != selected_keys:
        detail = sorted(selected_keys - set(selected_receipts))
        return {}, [
            "current v11 graph selected a different realization surface: "
            + ", ".join(detail[:4])
        ]
    return selected_receipts, []


def _authority_source_spec_correspondence_errors(
    root: Path,
    folder: Path,
    payload: Mapping[str, Any],
    selected: Iterable[tuple[str, Mapping[str, Any]]],
    *,
    evidence_context: object | None,
    require_proof_pair_authority: bool,
) -> list[str] | None:
    """Validate retained correspondence under current semantic/graph authority.

    ``None`` means that no builder-issued authority lane covers every selected
    item at the requested strength.  The current raw import graph plus typed
    correspondence receipts can authenticate a Spec closure without also
    authenticating Lean Meta's exact Spec/proof type comparison.  Callers that
    need the latter must set ``require_proof_pair_authority``; either the
    current declaration-level semantic authority or the current unified v11
    graph can then skip that duplicate Lean check.

    This is deliberately engine-pair agnostic: the authority is accepted from
    current semantic identities, never from a version bridge or matching
    implementation hashes.
    """

    if not isinstance(evidence_context, EvidenceRunContext):
        return None
    if not evidence_context.issued_by_builder:
        return None
    legacy_state = evidence_context.legacy_source_record_state
    authority = (
        legacy_state.semantic_reuse_authority
        if legacy_state is not None
        else None
    )
    semantic_authority_current = isinstance(
        authority, CurrentSemanticReuseAuthority
    )
    graph_surface: _V11LeanReviewSurface | None = None
    if (
        getattr(evidence_context, "source_semantic_lane", "")
        == V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
    ):
        try:
            graph_surface = builder_issued_v11_lean_review_surface(
                folder,
                evidence_context,
            )
        except ValueError as exc:
            return ["current v11 Lean graph is ambiguous: " + str(exc)]
    graph_authority_current = graph_surface is not None
    if graph_authority_current:
        graph_receipts = graph_native_source_spec_realization_receipts(
            root,
            folder,
            payload,
            selected,
            evidence_context=evidence_context,
        )
        if graph_receipts is not None:
            receipts, graph_errors = graph_receipts
            selected_keys = {str(key) for key, _item in selected}
            if graph_errors:
                return graph_errors
            if set(receipts) != selected_keys:
                missing = sorted(selected_keys - set(receipts))
                return [
                    "current v11 graph omitted realization item(s): "
                    + ", ".join(missing[:4])
                ]
            return []
    graph_identity_context = (
        legacy_state.source_record_identity_context
        if legacy_state is not None
        else None
    )
    if (
        not semantic_authority_current
        and not graph_authority_current
        and graph_identity_context is None
    ):
        return None
    if (
        require_proof_pair_authority
        and not semantic_authority_current
        and not graph_authority_current
    ):
        # A typed route identifies the intended endpoint; it does not prove
        # that the endpoint's elaborated type is the selected Spec.  Fresh
        # admission runs Lean Meta once.  A retained current v11 review graph
        # is sufficient here because its construction already rejected every
        # nonmatching, unsafe, sorry-bearing, or unchecked-axiom endpoint.
        return None
    if evidence_context.folder.resolve() != folder.resolve():
        return ["semantic authority belongs to a different paper"]
    if (
        legacy_state is not None
        and legacy_state.source_record_identity_error
    ):
        return [
            "semantic authority has a stale source-record identity: "
            + legacy_state.source_record_identity_error
        ]
    exact_items = evidence_context.statement_map.get("items")
    supplied_items = payload.get("items")
    if not isinstance(exact_items, Mapping) or not isinstance(
        supplied_items, Mapping
    ):
        return ["semantic authority statement map has no item ledger"]
    raw_audit = (
        legacy_state.inputs.audit_snapshot.payload
        if legacy_state is not None
        else None
    )
    if not graph_authority_current and not isinstance(raw_audit, Mapping):
        return ["semantic authority has no canonical raw audit"]
    if not semantic_authority_current and not graph_authority_current:
        assert isinstance(raw_audit, Mapping)
        graph_identity_error = current_source_record_identity_context_error(
            graph_identity_context,
            paper_dir=folder,
            paper=folder.name,
            current_raw_audit=raw_audit,
            expected_paper_statement_map_sha256=(
                evidence_context.paper_statement_map_sha256
            ),
        )
        if graph_identity_error:
            return [
                "typed correspondence graph has a stale source-record identity: "
                + graph_identity_error
            ]
    raw_rows = (
        raw_audit.get("configured_review_rows")
        if isinstance(raw_audit, Mapping)
        else None
    )
    if semantic_authority_current and not isinstance(raw_rows, list):
        return ["semantic authority has no configured review rows"]
    rows: dict[str, Mapping[str, Any]] = {}
    for raw_row in raw_rows if isinstance(raw_rows, list) else ():
        if not isinstance(raw_row, Mapping):
            return ["semantic authority has a malformed configured review row"]
        qualified = str(raw_row.get("qualified_declaration") or "").strip()
        if not qualified or qualified in rows:
            return ["semantic authority has an ambiguous configured review row"]
        rows[qualified] = raw_row
    if semantic_authority_current and set(rows) != set(authority.reviewed_declarations):
        return ["semantic authority review roots differ from the canonical raw audit"]

    pair_projection = _trusted_semantic_contract_revalidation_projection(
        (
            legacy_state.semantic_contract_revalidation
            if legacy_state is not None
            else None
        )
    )
    structurally_revalidated_pair_errors = (
        set(pair_projection.suppressed_source_contract_association_errors)
        & set(pair_projection.suppressed_source_coverage_route_errors)
        if pair_projection is not None
        else set()
    )
    graph_routes: dict[str, Any] = {}
    if not semantic_authority_current and not graph_authority_current:
        typed_sha256 = str(
            getattr(pair_projection, "typed_route_reconciliation_sha256", "") or ""
        ).strip().lower()
        if not SHA256_RE.fullmatch(typed_sha256):
            return None
        try:
            graph_routes = EvidenceRouteSet.from_source_map(
                payload,
            ).by_source_item()
        except ObligationRouteError:
            return None
    errors: list[str] = []
    for key, raw_item in selected:
        exact_item = exact_items.get(key)
        supplied_item = supplied_items.get(key)
        try:
            exact_item_json = json.dumps(
                exact_item, sort_keys=True, separators=(",", ":")
            )
            supplied_item_json = json.dumps(
                supplied_item, sort_keys=True, separators=(",", ":")
            )
            selected_item_json = json.dumps(
                raw_item, sort_keys=True, separators=(",", ":")
            )
        except (TypeError, ValueError):
            errors.append(f"{key}: selected statement-map item is not canonical JSON")
            continue
        if (
            exact_item_json != supplied_item_json
            or exact_item_json != selected_item_json
        ):
            errors.append(
                f"{key}: selected statement-map item is not the authority-bound item"
            )
            continue
        raw_contract = raw_item.get("semantic_contract")
        specification = (
            str(raw_contract.get("spec_declaration") or "").strip()
            if isinstance(raw_contract, Mapping)
            else ""
        )
        if not specification:
            errors.append(f"{key}: semantic contract has no specification")
            continue
        row = rows.get(specification)
        if semantic_authority_current and row is None:
            # The source-record authority is intentionally bounded to its
            # configured roots.  A v11-only support claim may still have a
            # current source-to-Spec judgment, but that judgment does not by
            # itself authenticate the paired proof endpoint.  Decline reuse
            # and let the ordinary Lean realization check establish the pair.
            return None
        evidence = str(raw_contract.get("evidence_declaration") or "").strip()
        mode = str(raw_contract.get("evidence_mode") or "").strip()
        alias = row.get("review_alias_expansion") if row is not None else None
        alias_pair_current = bool(
            mode in {"proves", "definitionally_realizes"}
            and isinstance(alias, Mapping)
            and alias.get("complete") is True
            and alias.get("structural_alpha_normalized_equal") is True
            and str(alias.get("reviewed_declaration") or "").strip()
            == specification
            and str(alias.get("effective_declaration") or "").strip()
            == evidence
            and key
            in {
                str(value).strip()
                for value in alias.get("source_items", [])
                if isinstance(value, str) and value.strip()
            }
        )
        if graph_authority_current:
            assert graph_surface is not None
            graph_row = graph_surface.semantic_contracts.get(
                (specification, evidence, mode)
            )
            pair_current = bool(
                isinstance(graph_row, Mapping)
                and graph_row.get("matches") is True
                and graph_row.get("evidence_is_unsafe") is not True
                and graph_row.get("evidence_value_has_sorry") is not True
                and graph_row.get("evidence_axiom_closure_checked") is True
                and specification in graph_surface.semantic_targets
            )
        elif semantic_authority_current:
            companion_error = (
                "semantic-contract companion is not an exact transparent "
                f"evidence/Spec structural pair: {evidence} / {specification}"
            )
            structural_pair_current = bool(
                mode in {"proves", "definitionally_realizes"}
                and evidence in rows
                and companion_error in structurally_revalidated_pair_errors
            )
            pair_current = alias_pair_current or structural_pair_current
        else:
            route = graph_routes.get(key)
            pair_current = bool(
                route is not None
                and route.source_item_id == key
                and route.spec_declaration == specification
                and route.evidence_declaration == evidence
                and route.evidence_mode == mode
            )
        if not pair_current:
            # An authority miss is not a semantic failure.  It means this
            # optimization cannot replace the ordinary current Lean check.
            return None
        if semantic_authority_current:
            assert row is not None
            if any(
                not isinstance(row.get(field), str)
                or not SHA256_RE.fullmatch(str(row.get(field)).strip())
                for field in (
                    "elaborated_signature_sha256",
                    "semantic_dependency_sha256",
                    "elaborated_proposition_graph_sha256",
                )
            ):
                errors.append(f"{key}: semantic authority row is not fully pinned")
                continue
        raw_correspondence = raw_item.get(SOURCE_SPEC_CORRESPONDENCE_KEY)
        raw_atoms = raw_item.get(SOURCE_CLAIM_ATOMS_KEY)
        if not isinstance(raw_correspondence, Mapping):
            errors.append(f"{key}: source_spec_correspondence is malformed")
            continue
        if not isinstance(raw_contract, Mapping) or not isinstance(raw_atoms, list):
            errors.append(f"{key}: correspondence source/contract inputs are malformed")
            continue
        existing_identity = str(
            raw_correspondence.get("item_identity_sha256") or ""
        ).strip().lower()
        expected_identity = source_spec_correspondence_item_identity_sha256(
            dict(raw_contract), dict(raw_correspondence)
        )
        current_atoms = source_claim_atoms_semantic_sha256(raw_atoms)
        if (
            not SHA256_RE.fullmatch(existing_identity)
            or existing_identity != expected_identity
        ):
            errors.append(f"{key}: correspondence item identity is not self-consistent")
            continue
        if (
            str(raw_correspondence.get("source_atoms_sha256") or "")
            .strip()
            .lower()
            != current_atoms
        ):
            errors.append(f"{key}: correspondence source atoms changed")
            continue
        if any(
            not isinstance(raw_correspondence.get(field), str)
            or not SHA256_RE.fullmatch(str(raw_correspondence.get(field)).strip())
            for field in (
                "spec_closure_sha256",
                "spec_surface_sha256",
                "closure_environment_sha256",
            )
        ):
            errors.append(f"{key}: correspondence closure receipt is incomplete")
            continue
        errors.extend(
            f"{key}: {error}"
            for error in source_spec_correspondence_validation_errors(
                dict(raw_correspondence),
                raw_atoms=raw_atoms,
                raw_contract=dict(raw_contract),
            )
        )
    return errors


def semantic_authority_source_spec_correspondence_errors(
    root: Path,
    folder: Path,
    payload: Mapping[str, Any],
    selected: Iterable[tuple[str, Mapping[str, Any]]],
    *,
    evidence_context: object | None,
) -> list[str] | None:
    """Require authority for both correspondence closure and proof pairing."""

    return _authority_source_spec_correspondence_errors(
        root,
        folder,
        payload,
        selected,
        evidence_context=evidence_context,
        require_proof_pair_authority=True,
    )


def graph_authority_source_spec_correspondence_errors(
    root: Path,
    folder: Path,
    payload: Mapping[str, Any],
    selected: Iterable[tuple[str, Mapping[str, Any]]],
    *,
    evidence_context: object | None,
) -> list[str] | None:
    """Require current typed authority for the retained Spec correspondence.

    This deliberately does not grant proof-pair credit.  It lets fresh
    closeout reuse current source atoms and Spec closure hashes while Lean Meta
    independently checks each exact theorem endpoint once.
    """

    return _authority_source_spec_correspondence_errors(
        root,
        folder,
        payload,
        selected,
        evidence_context=evidence_context,
        require_proof_pair_authority=False,
    )


def source_claim_atom_inventory_findings(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate the opt-in atom inventory before resolving any Lean route.

    Older source maps have no atom schema and remain valid.  A new map opts in
    at its top level; every theorem-like presentation selected by the active
    semantic coverage mode (plus an explicit corrected target) then needs an
    atom for each source clause.  The independent source review must establish
    atom completeness from the pinned source statement; this mechanical pass
    verifies that no declared atom loses its source span or semantic text
    before the full repository pass validates its Lean route.
    """

    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(map_path, context)
    if not isinstance(payload, dict):
        return []
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return []

    proof_obligation_items, _mode_error = _source_map_proof_obligation_items(
        folder, payload, context=context
    )
    presentation_aliases, _alias_errors = source_presentation_aliases(raw_items)
    atom_obligation_items = {
        source_key: raw_item
        for source_key, raw_item in proof_obligation_items.items()
        if source_key not in presentation_aliases
        and str(raw_item.get("source_kind") or "").strip().lower()
        in SOURCE_CLAIM_ATOM_THEOREM_LIKE_KINDS
        and str(raw_item.get("source_status") or "").strip().lower()
        not in SOURCE_SPEC_CORRESPONDENCE_NONCLAIM_STATUSES
    }

    marker_present = SOURCE_CLAIM_ATOMS_SCHEMA_KEY in payload
    atoms_present = any(
        SOURCE_CLAIM_ATOMS_KEY in raw_item
        for raw_item in atom_obligation_items.values()
    )
    if not marker_present and not atoms_present:
        return []

    severity = finding_severity(status)
    findings: list[Finding] = []
    file_bytes_override = (
        context.file_bytes_override() if context is not None else None
    )

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(map_path), message))

    if not marker_present:
        add(
            f"{SOURCE_CLAIM_ATOMS_SCHEMA_KEY} is required when an item uses "
            f"{SOURCE_CLAIM_ATOMS_KEY}"
        )
        return findings
    if not schema_version_is_exact(
        payload.get(SOURCE_CLAIM_ATOMS_SCHEMA_KEY), SOURCE_CLAIM_ATOMS_SCHEMA
    ):
        add(
            f"{SOURCE_CLAIM_ATOMS_SCHEMA_KEY} must be "
            f"{SOURCE_CLAIM_ATOMS_SCHEMA}"
        )
        return findings

    for raw_key, raw_item in atom_obligation_items.items():
        source_key = str(raw_key)
        if SOURCE_CLAIM_ATOMS_KEY not in raw_item:
            add(
                f"items.{source_key}: theorem-like source item must enumerate "
                f"{SOURCE_CLAIM_ATOMS_KEY} under schema "
                f"{SOURCE_CLAIM_ATOMS_SCHEMA}"
            )
            continue

        raw_atoms = raw_item.get(SOURCE_CLAIM_ATOMS_KEY)
        for error in source_claim_atoms_validation_errors(raw_atoms):
            add(f"items.{source_key}: {error}")
        if not isinstance(raw_atoms, list):
            continue
        for index, raw_atom in enumerate(raw_atoms):
            if not isinstance(raw_atom, dict):
                continue
            locator = raw_atom.get("source_locator")
            for error in source_file_line_anchor_errors(
                folder,
                locator,
                require_source_bytes=require_source_bytes,
                file_bytes_override=file_bytes_override,
            ):
                add(
                    f"items.{source_key}.{SOURCE_CLAIM_ATOMS_KEY}[{index}].source_locator "
                    f"{error}"
                )
            for error in canonical_artifact_source_span_errors(
                folder,
                locator,
                source_artifact_path=payload.get("source_artifact_path"),
            ):
                add(
                    f"items.{source_key}.{SOURCE_CLAIM_ATOMS_KEY}[{index}].source_locator "
                    f"{error}"
                )
    return findings


def source_spec_correspondence_enabled(payload: object) -> bool:
    """Whether a map explicitly requests the strict realization closeout lane."""

    return isinstance(payload, dict) and schema_version_is_exact(
        payload.get(SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY),
        SOURCE_SPEC_CORRESPONDENCE_SCHEMA,
    )


def source_spec_correspondence_requested(
    status_payload: object,
    source_map_payload: object | None = None,
    *,
    folder: Path | None = None,
) -> bool:
    """Expose the shared protocol selector through the historical gate API."""

    return _source_spec_correspondence_requested(
        status_payload,
        source_map_payload,
        folder=folder,
    )


def raw_source_spec_screening_requested(
    status_payload: object,
    source_map_payload: object | None = None,
    *,
    folder: Path | None = None,
) -> bool:
    """Route the direct-review alias through the same patchable gate."""

    return source_spec_correspondence_requested(
        status_payload,
        source_map_payload,
        folder=folder,
    )


def _source_spec_semantic_basis_artifact_errors(
    folder: Path,
    raw_basis: object,
    *,
    require_source_bytes: bool = True,
) -> tuple[list[str], tuple[str, str] | None]:
    """Check the current bytes and line anchor of a supplemental basis."""

    errors = _source_spec_semantic_basis_validation_errors(raw_basis)
    if errors or not isinstance(raw_basis, dict):
        return errors, None
    artifact_path = _paper_local_artifact_path(folder, raw_basis.get("artifact_path"))
    if artifact_path is None:
        return [
            "semantic_basis.artifact_path must name an existing paper-local artifact"
        ], None
    raw_artifact_path = str(raw_basis.get("artifact_path") or "").strip()
    expected_digest = str(raw_basis.get("artifact_sha256") or "").strip().lower()
    if not artifact_path.exists():
        if require_source_bytes:
            return [
                "semantic_basis.artifact_path must name an existing paper-local artifact"
            ], None
        # A semantic basis is itself a source-facing, byte-pinned source
        # artifact. Structural public checkouts may omit those licensed bytes,
        # just as they may omit the map's primary source artifact. Keep
        # validating path safety, digest shape, and exact locator agreement;
        # the caller emits one non-certifying warning per absent source pin.
        locator = str(raw_basis.get("source_locator") or "")
        errors.extend(
            "semantic_basis.source_locator " + error
            for error in source_file_line_anchor_errors(
                folder,
                locator,
                require_source_bytes=False,
            )
        )
        matches = list(SOURCE_FILE_LINE_RE.finditer(locator))
        if len(matches) == 1:
            anchored = Path(matches[0].group("path"))
            declared = Path(str(raw_basis.get("artifact_path") or "").strip())
            if anchored != declared:
                errors.append(
                    "semantic_basis.source_locator must point into semantic_basis.artifact_path"
                )
        return errors, (raw_artifact_path, expected_digest)
    if not artifact_path.is_file():
        return [
            "semantic_basis.artifact_path must name an existing paper-local artifact"
        ], None
    try:
        actual_digest = sha256_file(artifact_path)
    except OSError as error:
        return [f"semantic_basis.artifact_path could not be read: {error}"], None
    if actual_digest != expected_digest:
        errors.append(
            "semantic_basis.artifact_sha256 does not match its current paper-local artifact"
        )
    locator = str(raw_basis.get("source_locator") or "")
    for error in source_file_line_anchor_errors(folder, locator):
        errors.append("semantic_basis.source_locator " + error)
    matches = list(SOURCE_FILE_LINE_RE.finditer(locator))
    if len(matches) == 1:
        anchored = Path(matches[0].group("path"))
        declared = Path(str(raw_basis.get("artifact_path") or "").strip())
        if anchored != declared:
            errors.append(
                "semantic_basis.source_locator must point into semantic_basis.artifact_path"
            )
    return errors, None


def _source_spec_correspondence_inventory_findings_uncached(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate required atom-level theorem-realization source records.

    This intentionally does not make unchanged legacy semantic contracts
    invalid. Explicit requests and the trusted new-paper selector activate
    v11; at that point every claim selected by the semantic coverage
    mode (plus corrected targets) is held to the stricter atom and closure-
    record shape. The repository Lean pass supplies the current elaborated
    closure and rejects absent components.
    """

    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    # Read the status switch before the source map. A closeout cannot evade a
    # declared realization requirement by deleting or corrupting the map; a
    # not-started scaffold may nevertheless declare its future requirement
    # before creating an inventory.
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    required_switch = source_spec_correspondence_required(status_payload)
    automatic_required = False
    automatic_reason = "explicit paper closeout requirement"
    if not required_switch:
        try:
            from scripts.theorem_realization_transition import (
                theorem_realization_reissue_requirement,
            )

            automatic_requirement = theorem_realization_reissue_requirement(
                ROOT, folder, status_payload
            )
            automatic_required = automatic_requirement.required
            automatic_reason = automatic_requirement.reason
        except Exception as error:
            automatic_required = True
            automatic_reason = f"trusted v11 transition comparison failed: {error}"
    findings, payload, strict_items, canonical_source_is_current = (
        source_spec_correspondence_inventory_inputs(
            folder, status, require_source_bytes=require_source_bytes,
            context=context,
            automatic_requirement=(automatic_required, automatic_reason),
        )
    )
    if payload is None:
        return findings
    def add(message: str) -> None:
        findings.append(Finding(finding_severity(status), folder.name, rel(map_path), message))

    (
        semantic_source_artifact_path,
        semantic_source_artifact_sha256,
    ) = semantic_review_source_identity(payload)
    missing_basis_pins: dict[str, set[str]] = {}
    for source_key, raw_item in strict_items:
        raw_correspondence = raw_item.get(SOURCE_SPEC_CORRESPONDENCE_KEY)
        # Quote shape is required even when a claim is otherwise incomplete:
        # a missing correspondence record must not make its source clause
        # disappear from the strict source-byte obligation.
        strict_atom_errors = source_claim_atoms_validation_errors(
            raw_item.get(SOURCE_CLAIM_ATOMS_KEY), require_source_quote=True
        )
        if raw_correspondence is None:
            for error in strict_atom_errors:
                add(f"items.{source_key}: {error}")
        if canonical_source_is_current:
            for error in _source_claim_atoms_current_quote_binding_errors(
                folder,
                raw_item.get(SOURCE_CLAIM_ATOMS_KEY),
                source_artifact_path=semantic_source_artifact_path,
                source_artifact_sha256=semantic_source_artifact_sha256,
                alternate_source_artifact_path=payload.get("source_artifact_path"),
                alternate_source_artifact_sha256=payload.get(
                    "source_artifact_sha256"
                ),
            ):
                add(f"items.{source_key}: {error}")
        if raw_correspondence is None:
            add(
                f"items.{source_key}: strict realization closeout requires "
                f"{SOURCE_SPEC_CORRESPONDENCE_KEY} for every claim-bearing semantic_contract"
            )
            continue
        errors = source_spec_correspondence_validation_errors(
            raw_correspondence,
            raw_atoms=raw_item.get(SOURCE_CLAIM_ATOMS_KEY),
            raw_contract=raw_item.get("semantic_contract"),
        )
        for error in errors:
            add(f"items.{source_key}: {error}")
        if not isinstance(raw_correspondence, dict):
            continue
        dispositions = raw_correspondence.get("closure_node_dispositions")
        if not isinstance(dispositions, list):
            continue
        for index, disposition in enumerate(dispositions):
            if not isinstance(disposition, dict) or "semantic_basis" not in disposition:
                continue
            basis_errors, missing_basis_pin = (
                _source_spec_semantic_basis_artifact_errors(
                    folder,
                    disposition.get("semantic_basis"),
                    require_source_bytes=require_source_bytes,
                )
            )
            for error in basis_errors:
                add(
                    f"items.{source_key}.closure_node_dispositions[{index}].{error}"
                )
            if missing_basis_pin is not None:
                basis_path, basis_digest = missing_basis_pin
                missing_basis_pins.setdefault(basis_path, set()).add(basis_digest)
    for basis_path, basis_digests in sorted(missing_basis_pins.items()):
        if len(basis_digests) != 1:
            add(
                "semantic_basis source artifact has conflicting absent-byte SHA-256 "
                f"pins: {basis_path}"
            )
            continue
        findings.append(
            Finding(
                "WARN",
                folder.name,
                rel(map_path),
                "semantic-basis source bytes are not provisioned in this structural "
                f"checkout: {basis_path}; the recorded SHA-256 is not release "
                "certification",
            )
        )
    return findings


def source_spec_correspondence_inventory_findings(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate source-to-Spec inventory once per exact evidence transaction."""

    if isinstance(context, V11EvidenceRunContext):
        from scripts.current_closeout.primary_gate_transaction import (
            current_source_spec_correspondence_inventory_findings,
        )

        return current_source_spec_correspondence_inventory_findings(
            ROOT, folder, context=context, require_source_bytes=require_source_bytes
        )

    return _run_scoped_validation_findings(
        context,
        folder=folder,
        status=status,
        require_source_bytes=require_source_bytes,
        validator="source_spec_correspondence_inventory_findings",
        compute=lambda: _source_spec_correspondence_inventory_findings_uncached(
            folder,
            status,
            require_source_bytes=require_source_bytes,
            context=context,
        ),
    )


def v11_raw_source_spec_screening_findings(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Return the exact v11 source/Spec verdict for this transaction."""

    if isinstance(context, V11EvidenceRunContext):
        from scripts.current_closeout.semantic_review import (
            current_v11_raw_source_spec_screening_findings,
        )

        return current_v11_raw_source_spec_screening_findings(
            ROOT,
            folder,
            context=context,
        )

    return _run_scoped_validation_findings(
        context,
        folder=folder,
        status=status,
        require_source_bytes=require_source_bytes,
        validator="v11_raw_source_spec_screening",
        compute=lambda: _v11_raw_source_spec_screening_findings_uncached(
            folder,
            status,
            require_source_bytes=require_source_bytes,
            context=context,
        ),
    )


def _v11_raw_source_spec_screening_findings_uncached(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Require one current raw-source-to-transparent-Spec verdict per v11 claim.

    The atom-level realization receipt establishes which source atoms a proof
    endpoint realizes.  This independent screen establishes what an LLM or
    reviewer was actually shown while judging source/Spec meaning: the exact
    byte-pinned source bundle and the one transparent ``Spec`` declaration.
    It deliberately rejects a stale hash, a wrapper endpoint, a missing row,
    and an ``uncertain`` or ``mismatch`` verdict at a full closeout.  A source
    map paraphrase and theorem name never enter this comparison.
    """

    if status not in CLOSEOUT_STATUSES:
        return []
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    source_map = transaction_json(map_path, context)
    if not isinstance(source_map, dict) or not raw_source_spec_screening_requested(
        status_payload, source_map, folder=folder
    ):
        return []

    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(path: Path, message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(path), message))

    proof_items, scope_error = _source_map_proof_obligation_items(
        folder, source_map, context=context
    )
    if scope_error:
        add(map_path, "could not select v11 semantic-review scope: " + scope_error)
        return findings
    expected_records: dict[str, dict[str, Any]] = {}
    expected_keys_by_spec: dict[str, list[str]] = {}
    for raw_key, raw_item in proof_items.items():
        if not isinstance(raw_item, dict):
            continue
        contract = raw_item.get("semantic_contract")
        if not isinstance(contract, dict):
            continue
        spec = str(contract.get("spec_declaration") or "").strip()
        if spec:
            expected_keys_by_spec.setdefault(spec, []).append(str(raw_key))
            expected_records[spec] = raw_item
    if not expected_records:
        add(map_path, "v11 closeout selected no source-facing semantic Spec declarations")
        return findings
    for spec, source_keys in sorted(expected_keys_by_spec.items()):
        if len(source_keys) > 1:
            add(
                map_path,
                "v11 requires one semantic Spec per source claim, but "
                + ", ".join(source_keys)
                + f" all route to `{spec}`",
            )

    screening_path = folder / "audit" / "v11_raw_source_spec_screening.json"
    screening = load_json(screening_path)
    container = validate_v11_screening_container(
        screening,
        paper=folder.name,
    )
    for error in container.errors:
        add(screening_path, error)
    if not container.usable_item_ledger:
        return findings
    assert isinstance(screening, dict)
    raw_rows = screening["items"]
    assert isinstance(raw_rows, Mapping)

    interface_path = folder / "PaperInterface.lean"
    try:
        lean_surface = _v11_lean_review_surface(
            folder, expected_records, context=context
        )
    except ValueError as exc:
        add(
            interface_path,
            "could not obtain Lean-expanded v11 semantic targets: " + str(exc),
        )
        return findings
    try:
        from scripts.lean_signature_manifest import (
            review_claim_target_text,
        )
    except ImportError as exc:
        add(interface_path, "could not load the v11 claim-atom protocol: " + str(exc))
        return findings
    interface_items = lean_surface.source_declarations
    semantic_targets = lean_surface.semantic_targets
    paper_prerequisites = lean_surface.paper_prerequisites
    for prerequisite in paper_prerequisites:
        name = str(prerequisite.get("lean_name") or "").strip()
        if not str(prerequisite.get("paper_declaration_source") or "").strip():
            add(
                interface_path,
                f"{name}: Lean retained a paper-local semantic prerequisite without exact declaration source",
            )
            continue
        if not str(prerequisite.get("paper_semantic_target") or "").strip():
            add(
                interface_path,
                f"{name}: Lean retained a paper-local semantic prerequisite without a semantic target",
            )
            continue
        if prerequisite.get("semantic_current") is not True:
            add(
                folder / "audit" / "paper_semantic_prerequisites.json",
                f"{name}: paper-local semantic prerequisite has no current raw-source review",
            )
        elif str(prerequisite.get("semantic_judgment") or "").strip().lower() != "matches":
            add(
                folder / "audit" / "paper_semantic_prerequisites.json",
                f"{name}: paper-local semantic prerequisite judgment is not `matches`",
            )
    for prerequisite in lean_surface.library_prerequisites:
        name = str(prerequisite.get("lean_name") or "").strip()
        if prerequisite.get("semantic_current") is not True:
            add(
                folder / "audit" / "library_semantic_review.json",
                f"{name}: Lean-expanded semantic target has no current raw-source library review",
            )
        elif str(prerequisite.get("semantic_judgment") or "").strip().lower() != "matches":
            add(
                folder / "audit" / "library_semantic_review.json",
                f"{name}: Lean-expanded semantic target library judgment is not `matches`",
            )

    missing_rows = sorted(set(expected_records) - set(raw_rows))
    extra_rows = sorted(set(raw_rows) - set(expected_records))
    if missing_rows:
        add(
            screening_path,
            "v11 screening lacks "
            + str(len(missing_rows))
            + " selected source/Spec row(s): "
            + ", ".join(missing_rows[:4])
            + ("; ..." if len(missing_rows) > 4 else ""),
        )
    if extra_rows:
        add(
            screening_path,
            "v11 screening contains "
            + str(len(extra_rows))
            + " row(s) outside the current selected source/Spec scope: "
            + ", ".join(extra_rows[:4])
            + ("; ..." if len(extra_rows) > 4 else ""),
        )
    for spec, record in expected_records.items():
        row = raw_rows.get(spec)
        interface_item = interface_items.get(spec)
        semantic_target = semantic_targets.get(spec)
        if interface_item is None:
            add(interface_path, f"{spec}: v11 semantic target is absent from PaperInterface.lean")
            continue
        if semantic_target is None:
            add(interface_path, f"{spec}: Lean produced no complete v11 semantic target")
            continue
        kind = str(interface_item.get("declaration_kind") or "").strip()
        transparent = interface_item.get("is_transparent_definition")
        # `specDisplay` has already checked, in Lean, that telescope reduction
        # leaves a proposition-valued result.  A parameterized Spec therefore
        # has a printed type such as `(... : α) → Prop`, not literally
        # `Prop`; treating that presentation string as semantic authority both
        # rejects valid Specs and duplicates Lean's stronger native check.
        if kind != "definition" or transparent is not True:
            add(
                interface_path,
                f"{spec}: Lean did not elaborate the v11 semantic target as one transparent `def ...Spec : Prop :=` declaration",
            )
        if not isinstance(row, dict):
            continue
        source_error = source_anchor_file_error(
            folder,
            record,
            repository_root=ROOT,
            file_bytes_override=(
                context.file_bytes_override() if context is not None else None
            ),
        )
        if not source_error:
            source_text, source_digest, source_error = source_semantic_input_bundle(
                record, require_context_roles=True
            )
        else:
            source_text, source_digest = "", ""
        if source_error or not source_text or not source_digest:
            add(map_path, f"{spec}: current raw source bundle is invalid: {source_error}")
            continue
        expected_lean_digest = str(
            semantic_target.get("display_sha256") or ""
        ).strip().lower()
        expected_claim_manifest_digest = str(
            semantic_target.get("review_claim_manifest_sha256") or ""
        ).strip().lower()
        expected_claim_atoms_digest = str(
            semantic_target.get("review_claim_atoms_sha256") or ""
        ).strip().lower()
        try:
            # Validate that the current canonical atoms still admit the
            # protocol's complete reviewer-facing rendering. Its exact pretty
            # bytes are presentation trace, not semantic identity within one
            # unchanged protocol.
            review_claim_target_text(semantic_target)
        except ValueError as exc:
            add(interface_path, f"{spec}: Lean claim-atom target is invalid: {exc}")
            continue
        expected_target_protocol = str(
            semantic_target.get("lean_target_protocol")
            or "lean_transparent_paper_expansion_v1"
        ).strip()
        expected_review_declaration = str(
            semantic_target.get("semantic_review_declaration") or spec
        ).strip()
        if str(row.get("source_input_protocol") or "").strip() != "verbatim_source_anchor_bundle_v1":
            add(screening_path, f"{spec}: v11 row lacks the verbatim source-input protocol")
        if str(row.get("lean_target_protocol") or "").strip() != expected_target_protocol:
            add(screening_path, f"{spec}: v11 row lacks the current Lean semantic-target protocol")
        if str(row.get("semantic_target_declaration") or "").strip() != spec:
            add(screening_path, f"{spec}: v11 row targets a different declaration")
        if (
            str(row.get("semantic_review_declaration") or spec).strip()
            != expected_review_declaration
        ):
            add(screening_path, f"{spec}: v11 row reviews a different Lean declaration")
        if str(row.get("source_input_bundle_sha256") or "").strip().lower() != source_digest:
            add(screening_path, f"{spec}: v11 row is stale for the current exact source bundle")
        if str(row.get("paper_statement_sha256") or "").strip().lower() != statement_digest(source_text):
            add(screening_path, f"{spec}: v11 row does not bind its source-side semantic target")
        if str(row.get("lean_expanded_statement_sha256") or "").strip().lower() != expected_lean_digest:
            add(screening_path, f"{spec}: v11 row is stale for Lean's current expanded semantic target")
        if (
            str(row.get("review_claim_manifest_sha256") or "").strip().lower()
            != expected_claim_manifest_digest
        ):
            add(
                screening_path,
                f"{spec}: v11 row is stale for Lean's current claim manifest",
            )
        if (
            str(row.get("review_claim_atoms_sha256") or "").strip().lower()
            != expected_claim_atoms_digest
        ):
            add(
                screening_path,
                f"{spec}: v11 row is stale for Lean's premise/conclusion roles",
            )
        if not SHA256_RE.fullmatch(
            str(row.get("source_review_target_sha256") or "").strip().lower()
        ):
            add(
                screening_path,
                f"{spec}: v11 row lacks its atom-aware review-target trace",
            )
        verdict = str(row.get("judgment") or "").strip().lower()
        approved_corrected_target = verdict == APPROVED_CORRECTED_TARGET_MATCH
        is_corrected_source_statement = (
            str(record.get("coverage_status") or "").strip()
            == CORRECTED_SOURCE_STATEMENT_STATUS
        )
        if approved_corrected_target:
            corrected_target = record.get("corrected_target")
            if (
                not is_corrected_source_statement
                or not isinstance(corrected_target, dict)
                or corrected_target.get("archival_equivalence_claimed") is not False
            ):
                add(
                    screening_path,
                    f"{spec}: approved-corrected-target judgment lacks a corrected-source map record",
                )
            elif not corrected_target_screening_binding_is_current(
                row, corrected_target
            ):
                add(
                    screening_path,
                    f"{spec}: approved-corrected-target judgment is stale for its recorded review identity",
                )
        elif is_corrected_source_statement:
            # A corrected-source map entry retains the archival proposition;
            # an ordinary `matches` record would falsely certify that archival
            # text against the different approved target.  The narrow
            # correction disposition additionally binds the target and its
            # approval record.
            add(
                screening_path,
                f"{spec}: corrected_source_statement requires `"
                f"{APPROVED_CORRECTED_TARGET_MATCH}`, not `{verdict or 'missing'}`",
            )
        elif verdict != "matches":
            add(
                screening_path,
                f"{spec}: raw source-to-expanded-Spec judgment is `{verdict or 'missing'}`, not `matches`",
            )
        if not str(row.get("reason") or "").strip():
            add(screening_path, f"{spec}: v11 row has no reviewer explanation")
    return findings


def material_library_semantic_review_findings(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Return the exact material-library verdict for this transaction."""

    if isinstance(context, V11EvidenceRunContext):
        from scripts.current_closeout.semantic_review import (
            current_v11_material_library_semantic_review_findings,
        )

        return current_v11_material_library_semantic_review_findings(
            ROOT,
            folder,
            context=context,
        )

    return _run_scoped_validation_findings(
        context,
        folder=folder,
        status=status,
        require_source_bytes=require_source_bytes,
        validator="material_library_semantic_review",
        compute=lambda: _material_library_semantic_review_findings_uncached(
            folder,
            status,
            require_source_bytes=require_source_bytes,
            context=context,
        ),
    )


def _material_library_semantic_review_findings_uncached(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Require current raw-source review for every material library primitive.

    The review dashboard owns the bounded library-declaration registry and
    exact source-bundle reconstruction.  This integrity gate makes its result
    a closeout requirement for the v11 source-Spec lane: a reusable library
    name cannot be a silent semantic shortcut merely because it renders in a
    packet.  The check is deliberately limited to papers that explicitly opt
    into source-Spec correspondence, so existing legacy papers are not
    retroactively relabelled as having passed this newer lane.
    """

    if status not in CLOSEOUT_STATUSES:
        return []
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    source_map = transaction_json(map_path, context)
    if not isinstance(source_map, dict) or not raw_source_spec_screening_requested(
        status_payload, source_map, folder=folder
    ):
        return []
    proof_items, scope_error = _source_map_proof_obligation_items(
        folder, source_map, context=context
    )
    if scope_error:
        return [
            Finding(
                finding_severity(status),
                folder.name,
                rel(map_path),
                "could not select material-library semantic-review scope: " + scope_error,
            )
        ]
    expected_specs = {
        str(contract.get("spec_declaration") or "").strip()
        for item in proof_items.values()
        if isinstance(item, dict)
        for contract in [item.get("semantic_contract")]
        if isinstance(contract, dict)
        and str(contract.get("spec_declaration") or "").strip()
    }
    if not expected_specs:
        return []
    direct_source_declarations: set[str] = set()
    if typed_route_validation_required(source_map):
        try:
            direct_source_declarations = set(
                EvidenceRouteSet.from_source_map(
                    source_map,
                ).source_semantic_declarations()
            )
        except ObligationRouteError as exc:
            return [
                Finding(
                    finding_severity(status),
                    folder.name,
                    rel(map_path),
                    "could not select source-facing definition review scope: "
                    + str(exc),
                )
            ]
    ledger_path = folder / "audit" / "library_semantic_review.json"
    ledger_payload = transaction_json(ledger_path, context)
    if not isinstance(ledger_payload, dict):
        return [
            Finding(
                finding_severity(status),
                folder.name,
                rel(ledger_path),
                "missing or malformed material library semantic-review ledger",
            )
        ]
    expected_review_declarations = set(expected_specs)
    try:
        lean_surface = _v11_lean_review_surface(
            folder, expected_specs, context=context
        )
        direct_paper_declarations = direct_source_declarations & set(
            lean_surface.paper_semantic_targets
        )
        classified_direct_declarations = (
            set(lean_surface.paper_semantic_targets)
            | set(lean_surface.library_semantic_targets)
        )
        missing_direct_declarations = (
            direct_source_declarations - classified_direct_declarations
        )
        if missing_direct_declarations:
            raise ValueError(
                "Lean did not classify every source-facing semantic declaration: "
                + ", ".join(sorted(missing_direct_declarations)[:4])
            )
        expanded_targets = {
            **dict(lean_surface.semantic_targets),
            **{
                name: dict(lean_surface.paper_semantic_targets[name])
                for name in direct_paper_declarations
                if name in lean_surface.paper_semantic_targets
            },
        }
        expected_review_declarations = expected_specs | direct_paper_declarations
    except ValueError as exc:
        expanded_targets = {}
        lean_surface = None
        surface_errors: list[str] = [
            "could not obtain current Lean-expanded Spec library surface: " + str(exc)
        ]
    else:
        surface_errors = []
    if set(expanded_targets) != expected_review_declarations:
        surface_errors.append(
            "Lean-expanded library surface does not cover the selected source-facing scope"
        )
    # The complete material library surface is a projection of the current
    # Lean-owned graph, not reviewer-owned evidence.  Requiring a second copy
    # in the semantic ledger made harmless root/scope presentation changes
    # look like stale semantic judgments.  The entries below remain fail-closed:
    # every library prerequisite discovered from every current result or
    # standalone source-semantic root must have an exact current `matches`
    # verdict bound to its source bundle and Lean semantic-target identity.
    findings: list[Finding] = [
        Finding(finding_severity(status), folder.name, rel(ledger_path), error)
        for error in surface_errors
    ]
    if lean_surface is not None:
        entries = lean_surface.library_prerequisites
    else:
        # A failed Lean graph cannot be replaced by source-token discovery.
        # The surface error above is the complete fail-closed disposition.
        entries = ()
    for entry in entries:
        name = str(entry.get("lean_name") or "library declaration").strip()
        current = bool(entry.get("semantic_current"))
        judgment = str(entry.get("semantic_judgment") or "not recorded").strip()
        if current and judgment == "matches":
            continue
        detail = str(entry.get("semantic_status") or "incomplete").strip()
        if current and judgment in {"mismatch", "uncertain"}:
            detail = "current source-to-library judgment is `" + judgment + "`"
        findings.append(
            Finding(
                finding_severity(status),
                folder.name,
                rel(folder / "audit" / "library_semantic_review.json"),
                f"{name}: material library semantic review is not a current `matches` verdict ({detail})",
            )
        )
    return findings


def conditional_probability_composition_anchor_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    scoped_items: dict[str, dict[str, Any]],
    *,
    require_source_bytes: bool = True,
) -> list[Finding]:
    """Byte-validate schema-2 composition clauses even without global anchors.

    The three source clauses are not ordinary source-map items and must not
    disappear merely because a paper leaves global anchor validation disabled.
    A synthetic map lets the existing exact byte validator own path, range,
    quote, and canonical-artifact checks without using source keys or Lean
    declaration names as mathematical evidence.
    """

    composition_items: dict[str, dict[str, Any]] = {}
    for source_key, raw_item in scoped_items.items():
        if not isinstance(raw_item, dict):
            continue
        contract = raw_item.get("semantic_contract")
        if not isinstance(contract, dict) or str(
            contract.get("semantic_shape") or ""
        ).strip() != CONDITIONAL_PROBABILITY_COMPOSITION_SEMANTIC_SHAPE:
            continue
        composition_items[str(source_key)] = {
            CONDITIONAL_PROBABILITY_COMPOSITION_FIELD: contract.get(
                CONDITIONAL_PROBABILITY_COMPOSITION_FIELD
            )
        }
    if not composition_items:
        return []
    isolated_payload = {
        "source_artifact_path": payload.get("source_artifact_path"),
        "source_artifact_sha256": payload.get("source_artifact_sha256"),
        SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY: True,
        "items": composition_items,
    }
    return source_anchor_evidence_findings(
        folder,
        status,
        manifest_path,
        isolated_payload,
        require_source_bytes=require_source_bytes,
    )


def source_core_projection_validation_errors(raw_item: object) -> list[str]:
    """Compatibility export of the shared map-projection validator."""

    return _source_core_errors(raw_item)


def _semantic_contract_item_requires_proof_evidence(
    payload: dict[str, Any], source_key: str, raw_item: dict[str, Any]
) -> bool:
    """Reuse the source-only proof/translation boundary.

    A named definition or predicate remains claim-bearing for inventory and
    statement fidelity, but it is reviewed through the translation lane rather
    than by inventing a theorem-shaped Spec/proof contract.  Result-bearing or
    ambiguous source presentations still require proof evidence.  The policy
    module has no dashboard, filesystem, or Lean-discovery dependency; failures
    still return ``True``.
    """

    del source_key  # Map keys are routing handles, never semantic evidence.
    # Schema-2 routes make the distinction explicit: a source semantic
    # declaration is reviewed through its Lean-owned prerequisite ledger, and
    # a typed proof-support item remains visible without becoming a synthetic
    # theorem contract.  The old semantic-contract lane cannot add assurance
    # to either route and must not reject it merely because the migration
    # deliberately removed a retired parser-shaped contract.
    if payload.get("semantic_route_schema") == 2:
        role = str(raw_item.get("inventory_role") or "").strip()
        if role == "source_semantic_declaration":
            return False
        if role == "proof_support" and str(
            raw_item.get("scope_disposition") or ""
        ).strip():
            return False
    try:
        decision = source_inventory_item_requires_proof_evidence(
            _semantic_contract_scope_item_context(payload, raw_item)
        )
    except (AttributeError, KeyError, TypeError, ValueError):
        return True
    return decision if isinstance(decision, bool) else True


def _semantic_contract_item_anchor_errors(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    raw_item: dict[str, Any],
    *,
    require_source_bytes: bool = True,
) -> list[str]:
    """Return exact-source-slice errors for one scope-exception candidate.

    This invokes the same byte-pinned source-anchor validator used by the
    manifest gate, rather than treating the map's quoted text as trusted.  The
    synthetic one-item map is structural plumbing only; eligibility is decided
    solely by the item's source fields and exact source quote.
    """

    isolated_payload = {
        "source_artifact_path": payload.get("source_artifact_path"),
        "source_artifact_sha256": payload.get("source_artifact_sha256"),
        SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY: True,
        "items": {"scope_exception": raw_item},
    }
    errors: list[str] = []
    if not require_source_bytes:
        locator = raw_item.get("source_location")
        errors.extend(
            source_file_line_anchor_errors(
                folder, locator, require_source_bytes=False
            )
        )
        errors.extend(
            canonical_artifact_source_span_errors(
                folder,
                locator,
                source_artifact_path=payload.get("source_artifact_path"),
            )
        )
    for finding in source_anchor_evidence_findings(
        folder,
        status,
        manifest_path,
        isolated_payload,
        require_source_bytes=require_source_bytes,
    ):
        if (
            not require_source_bytes
            and finding.severity == "WARN"
            and finding.message.startswith(
                "source bytes are not provisioned in this structural checkout:"
            )
        ):
            continue
        errors.append(finding.message)
    return list(dict.fromkeys(errors))


def _semantic_contract_nonclaim_scope_error(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    raw_item: dict[str, Any],
    *,
    require_source_bytes: bool = True,
) -> str:
    """Return why a ``claim_bearing: false`` source item is unsafe.

    Schema-1 semantic contracts are a source-claim inventory, not a way to
    suppress unproved statements.  A row independently classified outside the
    configured source-presentation scope may remain as nonclaim proof/support
    context.  Inside that scope, the only exceptional non-claim lanes are the
    source-validated finite computational illustration and an explicit,
    byte-pinned source observation that declares an issue unresolved or is
    subsumed by a selected result in this paper. The named-source inventory
    owns validation of the latter's source presentation and selected target.
    """

    classification = str(
        raw_item.get("source_scope_classification") or ""
    ).strip().lower()
    if source_item_effective_route_policy(raw_item)["is_source_resolved_within_paper"]:
        raw_items = payload.get("items")
        if not isinstance(raw_items, dict) or raw_item not in raw_items.values():
            return "source-resolved nonclaim item must belong to the current source map"
        for field in ("scope_reason", "source_evidence"):
            if not meaningful_semantic_text(raw_item.get(field)):
                return f"{classification} requires source-grounded {field}"
        # Reuse the inventory's existing target/pin checks, including rejection
        # of missing, unselected, cyclic, or uncatalogued dispositions. Merely
        # recognizing the route policy is not authority to suppress a claim.
        resolved_findings = source_named_result_inventory_findings(
            folder,
            status,
            manifest_path,
            payload,
            require_source_bytes=require_source_bytes,
        )
        return "; ".join(finding.message for finding in resolved_findings)
    if not classification:
        mode, mode_error = source_coverage_mode_from_map(payload)
        declared_environment_kinds = source_named_result_environment_kinds_from_map(
            payload
        )
        outside_presentation_scope = (
            not mode_error
            and mode is not None
            and not source_item_in_coverage_scope(
                raw_item,
                mode,
                declared_environment_kinds=declared_environment_kinds,
            )
        )
        if (
            outside_presentation_scope
            and raw_item.get(USER_APPROVED_SCOPE_EXCLUSION) is None
        ):
            return ""
    if classification not in {
        NON_NAMED_COMPUTATIONAL_ILLUSTRATION,
        SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION,
    }:
        return (
            "claim_bearing: false is permitted only for a source-validated "
            "non_named_computational_illustration or a "
            "source_declared_open_nonresult_observation, a validated "
            "source_resolved_within_paper_observation, or nonclaim support "
            "independently outside the configured source-presentation scope"
        )
    scope_error = source_inventory_item_scope_classification_error(
        _semantic_contract_scope_item_context(payload, raw_item)
    )
    if scope_error:
        return scope_error
    if (
        classification == SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION
        and not meaningful_semantic_text(raw_item.get("scope_reason"))
    ):
        return (
            "source_declared_open_nonresult_observation requires a source-grounded "
            "scope_reason"
        )
    if (
        classification == SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION
        and not meaningful_semantic_text(raw_item.get("source_evidence"))
    ):
        return (
            "source_declared_open_nonresult_observation requires source_evidence"
        )
    anchor_errors = _semantic_contract_item_anchor_errors(
        folder,
        status,
        manifest_path,
        payload,
        raw_item,
        require_source_bytes=require_source_bytes,
    )
    if anchor_errors:
        return "; ".join(anchor_errors)
    return ""


def _semantic_contract_user_scope_exclusion_error(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    raw_item: dict[str, Any],
    *,
    require_source_bytes: bool = True,
) -> str:
    """Return why a claim-bearing explicit user scope disposition is invalid.

    A user-approved exclusion does not erase a source claim.  It may waive a
    proof contract only when the existing approval schema and the map item's
    exact byte-pinned source anchor both validate.
    """

    raw_approval = raw_item.get(USER_APPROVED_SCOPE_EXCLUSION)
    if raw_approval is None:
        return ""
    if raw_item.get("claim_bearing") is not True:
        return (
            "user_approved_scope_exclusion must keep the source item "
            "claim_bearing: true"
        )
    if str(raw_item.get("source_scope_classification") or "").strip():
        return (
            "user_approved_scope_exclusion cannot coexist with "
            "source_scope_classification"
        )
    approval_errors = user_approved_scope_exclusion_errors(
        folder,
        raw_approval,
        expected_source_locator=raw_item.get("source_location"),
        require_source_bytes=require_source_bytes,
    )
    if approval_errors:
        return "; ".join(approval_errors)
    scope_error = source_inventory_item_user_approved_scope_exclusion_error(
        _semantic_contract_scope_item_context(payload, raw_item)
    )
    if scope_error:
        return scope_error
    anchor_errors = _semantic_contract_item_anchor_errors(
        folder,
        status,
        manifest_path,
        payload,
        raw_item,
        require_source_bytes=require_source_bytes,
    )
    if anchor_errors:
        return "; ".join(anchor_errors)
    return ""


def v11_direct_semantic_review_state(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> tuple[bool, str]:
    """Return whether the selected v11 direct-review lane is current.

    This is deliberately narrower than a final closure receipt: it establishes
    that the current source-to-expanded-Spec and material-library ledgers are
    complete and valid, but does not claim a focused-build receipt or completed
    human review.  It prevents a historical v10 aggregate record from blocking
    a paper that has explicitly selected the v11 direct semantic-review lane.
    The final receipt remains the only release-closure evidence.
    """

    if isinstance(context, V11EvidenceRunContext):
        from scripts.current_closeout.semantic_review import (
            current_v11_direct_semantic_review_state,
        )

        return current_v11_direct_semantic_review_state(
            ROOT,
            folder,
            context=context,
        )

    if status not in CLOSEOUT_STATUSES:
        return False, "paper status does not select a closeout review lane"
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    source_map = transaction_json(map_path, context)
    if not isinstance(source_map, dict) or not raw_source_spec_screening_requested(
        status_payload, source_map, folder=folder
    ):
        return False, "paper does not select the v11 direct source-to-Spec lane"

    findings = v11_raw_source_spec_screening_findings(
        folder,
        status,
        require_source_bytes=require_source_bytes,
        context=context,
    )
    findings.extend(
        material_library_semantic_review_findings(
            folder,
            status,
            require_source_bytes=require_source_bytes,
            context=context,
        )
    )
    if not findings:
        return True, ""
    detail = str(findings[0].message).strip()
    return False, detail or "v11 direct semantic-review evidence is incomplete"


def semantic_contract_inventory_findings(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Return the complete structural contract verdict for this transaction."""

    return _run_scoped_validation_findings(
        context,
        folder=folder,
        status=status,
        require_source_bytes=require_source_bytes,
        validator="semantic_contract_inventory",
        compute=lambda: _semantic_contract_inventory_findings_uncached(
            folder,
            status,
            require_source_bytes=require_source_bytes,
            context=context,
        ),
    )


def _semantic_contract_inventory_findings_uncached(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate opt-in contracts and repaired-defect routing without a Lean build.

    This fast lane checks only schema and cross-sidecar routing. The full
    repository audit independently asks Lean Meta whether the evidence proves
    the exact specification, or its exact negation for a refutation contract.
    """

    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(map_path, context)
    atom_findings = source_claim_atom_inventory_findings(
        folder,
        status,
        require_source_bytes=require_source_bytes,
        context=context,
    )
    correspondence_findings = source_spec_correspondence_inventory_findings(
        folder,
        status,
        require_source_bytes=require_source_bytes,
        context=context,
    )
    v11_screening_findings = v11_raw_source_spec_screening_findings(
        folder,
        status,
        require_source_bytes=require_source_bytes,
        context=context,
    )
    library_semantic_findings = material_library_semantic_review_findings(
        folder,
        status,
        require_source_bytes=require_source_bytes,
        context=context,
    )
    if payload is None:
        return (
            atom_findings
            + correspondence_findings
            + v11_screening_findings
            + library_semantic_findings
        )
    if not isinstance(payload, dict):
        return (
            atom_findings
            + correspondence_findings
            + v11_screening_findings
            + library_semantic_findings
            + source_map_scope_integrity_findings(folder, status, map_path, payload)
        )

    # Map structure and source presentation are always validated over the raw
    # inventory.  Only theorem-level contract obligations are scope-selected.
    findings = source_map_scope_integrity_findings(folder, status, map_path, payload)
    findings.extend(atom_findings)
    findings.extend(correspondence_findings)
    findings.extend(v11_screening_findings)
    findings.extend(library_semantic_findings)
    source_coverage_mode, mode_findings = source_coverage_mode_findings(
        folder, status, map_path, payload
    )
    findings.extend(mode_findings)
    raw_items = payload.get("items")
    _scoped_payload, items = scoped_source_map_payload(
        payload,
        source_coverage_mode,
        folder=folder,
        repository_root=ROOT,
        context=context,
    )
    validated_aliases = validated_presentation_alias_contract_exemptions(
        folder, payload, context=context
    )
    validated_subsumed_results = validated_subsumed_result_contract_exemptions(
        folder, payload, context=context
    )
    explicit_nonclaim_scope_items = {
        str(source_key): raw_item
        for source_key, raw_item in (raw_items.items() if isinstance(raw_items, dict) else [])
        if isinstance(raw_item, dict)
        and raw_item.get("claim_bearing") is False
    }
    marker_present = "semantic_contract_schema" in payload
    marker = payload.get("semantic_contract_schema")
    item_opt_in = any(
        isinstance(item, dict)
        and ("semantic_contract" in item or item.get("claim_bearing") is True)
        for item in items.values()
    )
    # An explicit non-claim classification is a source-scope exception, not a
    # deep-prose theorem obligation.  It nonetheless needs byte-pinned
    # validation even when ordinary named-theory selection excludes the row.
    item_opt_in = item_opt_in or any(
        "source_scope_classification" in item
        for item in explicit_nonclaim_scope_items.values()
    )
    if not marker_present and not item_opt_in:
        return findings

    severity = finding_severity(status)

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(map_path), message))

    if item_opt_in and not marker_present:
        add(
            "semantic_contract_schema is required when an item uses "
            "claim_bearing: true or semantic_contract"
        )
    marker_supported = schema_version_is_supported(
        marker, SEMANTIC_CONTRACT_SCHEMAS
    )
    if marker_present and not marker_supported:
        add(
            "semantic_contract_schema must be one of: "
            + ", ".join(str(value) for value in sorted(SEMANTIC_CONTRACT_SCHEMAS))
            + f"; got {marker!r}"
        )
    if marker_present and not isinstance(raw_items, dict):
        add("semantic-contract source map `items` must be an object")

    validated_nonclaim_scope_items: set[str] = set()
    if marker_supported:
        for source_key, raw_item in explicit_nonclaim_scope_items.items():
            scope_error = _semantic_contract_nonclaim_scope_error(
                folder,
                status,
                map_path,
                payload,
                raw_item,
                require_source_bytes=require_source_bytes,
            )
            if scope_error:
                add(f"items.{source_key}: {scope_error}")
            validated_nonclaim_scope_items.add(source_key)

    for source_key, raw_item in items.items():
        if not isinstance(raw_item, dict):
            if marker_supported:
                add(f"items.{source_key} must be an object")
            continue
        claim_bearing = raw_item.get("claim_bearing")
        if marker_supported and "claim_bearing" not in raw_item:
            add(
                f"items.{source_key}.claim_bearing must be explicitly Boolean under "
                "a supported semantic_contract_schema"
            )
        if "claim_bearing" in raw_item and not isinstance(claim_bearing, bool):
            add(f"items.{source_key}.claim_bearing must be Boolean")
        if (
            marker_supported
            and claim_bearing is False
            and str(source_key) not in validated_nonclaim_scope_items
        ):
            scope_error = _semantic_contract_nonclaim_scope_error(
                folder,
                status,
                map_path,
                payload,
                raw_item,
                require_source_bytes=require_source_bytes,
            )
            if scope_error:
                add(f"items.{source_key}: {scope_error}")
        raw_contract = raw_item.get("semantic_contract")
        for error in source_core_projection_validation_errors(raw_item):
            add(f"items.{source_key}: {error}")
        raw_defect_ids = raw_item.get("source_defect_ids")
        if raw_defect_ids is not None and (
            not isinstance(raw_defect_ids, list)
            or any(
                not isinstance(value, str) or not value.strip()
                for value in raw_defect_ids
            )
            or len({value.strip() for value in raw_defect_ids}) != len(raw_defect_ids)
        ):
            add(
                f"items.{source_key}.source_defect_ids must be a list of "
                "unique nonempty strings"
            )
        if (
            claim_bearing is True
            and raw_contract is None
            and str(source_key) not in validated_aliases
            and str(source_key) not in validated_subsumed_results
            and _semantic_contract_item_requires_proof_evidence(
                payload, str(source_key), raw_item
            )
        ):
            scope_error = _semantic_contract_user_scope_exclusion_error(
                folder,
                status,
                map_path,
                payload,
                raw_item,
                require_source_bytes=require_source_bytes,
            )
            if scope_error:
                add(
                    f"claim-bearing source item `{source_key}` lacks semantic_contract; "
                    f"user_approved_scope_exclusion is not a valid scope disposition: "
                    f"{scope_error}"
                )
            elif raw_item.get(USER_APPROVED_SCOPE_EXCLUSION) is None:
                add(
                    f"claim-bearing source item `{source_key}` lacks semantic_contract"
                )
            continue
        if raw_contract is None:
            continue
        errors = semantic_contract_validation_errors(
            raw_contract,
            schema=marker if marker_supported else SEMANTIC_CONTRACT_SCHEMA,
        )
        for error in errors:
            add(f"items.{source_key}: {error}")

    findings.extend(
        conditional_probability_composition_anchor_findings(
            folder,
            status,
            map_path,
            payload,
            items,
        )
    )

    findings.extend(
        repaired_source_defect_route_preflight_findings(
            folder,
            status,
            context=context,
        )
    )
    return findings


def source_record_review_sidecar_path(
    folder: Path,
    status_payload: dict[str, Any],
    *,
    config_field: str,
    default_basename: str,
) -> tuple[Path | None, str]:
    """Resolve a configured source-record sidecar inside its paper folder.

    The repository closeout supports paths configured under
    ``llm_source_record_review``.  The fast evidence gate must inspect the
    same artifacts rather than silently consulting a legacy canonical copy.
    Missing configuration deliberately retains the canonical-sidecar default.
    """

    review_surface = status_payload.get("review_surface")
    source_record_review = (
        review_surface.get("llm_source_record_review")
        if isinstance(review_surface, dict)
        else None
    )
    raw_path = (
        source_record_review.get(config_field)
        if isinstance(source_record_review, dict)
        else None
    )
    if not isinstance(raw_path, str) or not raw_path.strip():
        return canonical_sidecar(folder, default_basename), ""

    relative_path = Path(raw_path.strip())
    if relative_path.is_absolute():
        return None, f"llm_source_record_review.{config_field} must be relative"
    try:
        # Status paths are repository-relative, matching audit_repository's
        # source-record helper.  They still must remain inside this paper.
        candidate = (ROOT / relative_path).resolve()
        candidate.relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return (
            None,
            f"llm_source_record_review.{config_field} escapes the paper folder",
        )
    return candidate, ""


def source_record_administrative_projection_rebind_context(
    folder: Path,
    status_payload: dict[str, Any],
    *,
    audit_path: Path,
    audit_payload: dict[str, Any],
    statement_map_path: Path,
    statement_map: dict[str, Any] | None,
    receipt_bytes_override: bytes | None | object = _UNSET,
    raw_audit_bytes_override: bytes | None | object = _UNSET,
    statement_map_bytes_override: bytes | None | object = _UNSET,
) -> tuple[Any | None, Path | None, str]:
    """Load one exact direct-source-status transport rebind, if configured.

    A missing optional receipt leaves ordinary current validation unchanged. An
    existing receipt must reconstruct from the exact raw-audit bytes and exact
    current source-map bytes; it is never a loose permission to reinterpret a
    legacy semantic digest.
    """

    rebind_path, path_error = source_record_review_sidecar_path(
        folder,
        status_payload,
        config_field="source_record_administrative_projection_rebind_file",
        default_basename=SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
    )
    if path_error:
        return None, rebind_path, path_error
    assert rebind_path is not None
    kwargs: dict[str, object] = {}
    if receipt_bytes_override is not _UNSET:
        kwargs = {
            "receipt_bytes_override": receipt_bytes_override,
            "raw_audit_bytes_override": raw_audit_bytes_override,
            "statement_map_bytes_override": statement_map_bytes_override,
        }
    return load_administrative_projection_rebind_context(
        paper=folder.name,
        paper_dir=folder,
        raw_audit_path=audit_path,
        raw_audit=audit_payload,
        statement_map_path=statement_map_path,
        statement_map=statement_map,
        receipt_path=rebind_path,
        **kwargs,
    )


def approved_source_convention_formalized_note_error(
    folder: Path,
    item: dict[str, Any],
    *,
    context: EvidenceRunContext | None = None,
) -> str:
    """Validate a note-only visible-premise difference without name matching.

    A ``formalized_note`` may document an explicit source-model convention, but
    it must never turn a weakened conclusion or an unreviewed extra premise
    into full-closeout credit.  This check follows the source item's current
    semantic digest and the current proof-fidelity convention receipts.  It
    intentionally does not infer correspondence from a Lean declaration, row,
    binder, or source-map key.
    """

    if (
        str(item.get("source_target_disposition") or "").strip()
        != "approved_source_convention"
    ):
        return (
            "formalized-note visible-premise boundary must use "
            "source_target_disposition approved_source_convention"
        )

    source_semantic_sha256 = str(
        item.get("source_statement_semantic_sha256") or ""
    ).strip().lower()
    if not SHA256_RE.fullmatch(source_semantic_sha256):
        return (
            "formalized-note source_statement_semantic_sha256 must be a current "
            "64-character source semantic digest"
        )
    source_statement_locator = str(
        item.get("source_statement_locator") or ""
    ).strip()
    if not source_statement_locator:
        return "formalized-note source_statement_locator is missing"

    statement_map_path = transaction_sidecar(
        folder, "paper_statement_map.json", context
    )
    statement_map = transaction_json(statement_map_path, context)
    if not isinstance(statement_map, dict):
        return "formalized-note cannot load the canonical paper_statement_map.json"
    source_items = statement_map.get("items")
    if not isinstance(source_items, dict):
        return "formalized-note source map has no source-item dictionary"
    candidates = [
        source_item
        for source_item in source_items.values()
        if isinstance(source_item, dict)
        and source_item_coverage_sha256(source_item, "") == source_semantic_sha256
    ]
    if len(candidates) != 1:
        return (
            "formalized-note source semantic digest must identify exactly one "
            "current in-scope source statement"
        )
    current_source_item = candidates[0]
    if str(current_source_item.get("source_location") or "").strip() != source_statement_locator:
        return (
            "formalized-note source_statement_locator does not match the current "
            "source statement selected by its semantic digest"
        )

    raw_ids = item.get("model_convention_ids")
    if not isinstance(raw_ids, list) or not raw_ids:
        return "formalized-note model_convention_ids must be a nonempty list"
    convention_ids = [
        value.strip() for value in raw_ids if isinstance(value, str) and value.strip()
    ]
    if len(convention_ids) != len(raw_ids) or len(convention_ids) != len(
        set(convention_ids)
    ):
        return "formalized-note model_convention_ids must contain unique nonempty ids"
    raw_digests = item.get("model_convention_sha256_by_id")
    raw_locators = item.get("model_convention_source_locators")
    if not isinstance(raw_digests, dict) or not isinstance(raw_locators, dict):
        return (
            "formalized-note must pin model_convention_sha256_by_id and "
            "model_convention_source_locators"
        )
    normalized_digests = {
        str(key).strip(): str(value).strip().lower()
        for key, value in raw_digests.items()
        if str(key).strip()
    }
    normalized_locators = {
        str(key).strip(): str(value).strip()
        for key, value in raw_locators.items()
        if str(key).strip()
    }
    if set(normalized_digests) != set(convention_ids):
        return (
            "formalized-note model_convention_sha256_by_id must cover exactly "
            "model_convention_ids"
        )
    if set(normalized_locators) != set(convention_ids):
        return (
            "formalized-note model_convention_source_locators must cover exactly "
            "model_convention_ids"
        )

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    ledger_path, ledger_path_error = source_proof_fidelity_ledger_path(
        folder, status_payload
    )
    if ledger_path_error:
        return "formalized-note cannot resolve source-proof fidelity ledger: " + ledger_path_error
    ledger = (
        transaction_json(ledger_path, context)
        if ledger_path is not None
        else None
    )
    if not isinstance(ledger, dict):
        return "formalized-note cannot load the configured source-proof fidelity ledger"
    raw_conventions = ledger.get("model_conventions")
    if not isinstance(raw_conventions, list):
        return "formalized-note source-proof ledger has no model_conventions list"
    conventions = {
        str(convention.get("id") or "").strip(): convention
        for convention in raw_conventions
        if isinstance(convention, dict) and str(convention.get("id") or "").strip()
    }
    for convention_id in convention_ids:
        convention = conventions.get(convention_id)
        if convention is None:
            return (
                "formalized-note cites source-proof model convention absent from "
                "the current ledger: " + convention_id
            )
        if (
            normalized_digests.get(convention_id)
            != model_convention_semantic_digest(convention)
        ):
            return (
                "formalized-note model-convention digest is stale for "
                + convention_id
            )
        if normalized_locators.get(convention_id) != str(
            convention.get("source_locator") or ""
        ).strip():
            return (
                "formalized-note model-convention locator is stale for "
                + convention_id
            )
        if any(
            not str(convention.get(field) or "").strip()
            for field in SOURCE_PROOF_MODEL_CONVENTION_REQUIRED_FIELDS
        ):
            return (
                "formalized-note cites incomplete source-proof model convention "
                + convention_id
            )

    # Statement-match notes may waive only extra *premises*.  The structured
    # ledger must still show exact source/Lean conclusions and inputs, and all
    # matched atoms must be equivalent rather than merely one-way implications.
    if "judgment" in item:
        if str(item.get("judgment") or "").strip().lower() != "mismatch":
            return "formalized-note statement row must retain its mismatch judgment"
        if str(item.get("resolution") or "").strip().lower() not in {
            "conditional_boundary",
            "visible_premise_boundary",
        }:
            return (
                "formalized-note statement row must retain a visible-premise "
                "boundary resolution"
            )
        if str(item.get("obligation_ledger_error") or "").strip():
            return "formalized-note statement row has an invalid obligation ledger"
        for field in (
            "unmatched_source_conclusions",
            "unmatched_source_inputs",
            "unmatched_lean_conclusions",
        ):
            if item.get(field) != []:
                return (
                    "formalized-note statement row has a non-premise semantic gap "
                    "in " + field
                )
        unjustified = item.get("unjustified_lean_inputs")
        if not isinstance(unjustified, list) or not unjustified:
            return (
                "formalized-note statement row must expose at least one extra "
                "Lean premise"
            )
        alignment = item.get("obligation_alignment")
        if not isinstance(alignment, list) or not alignment or any(
            not isinstance(entry, dict)
            or str(entry.get("relation") or "").strip().lower() != "equivalent"
            for entry in alignment
        ):
            return (
                "formalized-note statement row must retain only equivalent "
                "source/Lean obligation alignments"
            )

    return ""


def canonical_source_first_inventory_present(
    folder: Path,
    *,
    context: EvidenceRunContext | None = None,
) -> bool:
    """Return whether a paper has declared a canonical source-first inventory.

    ``source_curated`` is the inventory's explicit source-facing schema marker.
    We deliberately do not infer this from map keys, source wording, or Lean
    declaration names.  A malformed nonempty inventory still triggers the
    migration gate: separate map validators report its detailed schema error,
    but bad shape must not make a legacy closeout optional.
    """

    path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(path, context)
    if not isinstance(payload, dict) or payload.get("source_curated") is not True:
        return False
    raw_items = payload.get("items")
    return isinstance(raw_items, (dict, list)) and bool(raw_items)


def canonical_source_proof_ledger_present(
    folder: Path,
    *,
    context: EvidenceRunContext | None = None,
) -> bool:
    """Return whether the canonical ledger artifact exists, even if malformed."""

    path = transaction_sidecar(folder, "source_proof_fidelity.json", context)
    if context is None:
        return path.is_file()
    snapshot = context.json_snapshot(path)
    return snapshot is not None and snapshot.sha256 is not None


def configured_review_artifact_path_error(
    folder: Path,
    *,
    lane: str,
    field: str,
    value: object,
) -> str:
    """Validate a configured audit artifact path without requiring it to exist.

    Artifact freshness and payload schema have dedicated checks elsewhere.  The
    migration gate only establishes that a closeout is actually wired to the
    current lane, and rejects an empty or escaping pointer that could make a
    later audit silently fall back to unrelated sidecars.
    """

    if not isinstance(value, str) or not value.strip():
        return f"review_surface.{lane}.{field} must be a nonempty artifact path"
    relative_path = Path(value.strip())
    if relative_path.is_absolute():
        return f"review_surface.{lane}.{field} must be relative"
    anchor = ROOT if relative_path.parts[:1] == ("papers",) else folder
    try:
        candidate = (anchor / relative_path).resolve()
        candidate.relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return f"review_surface.{lane}.{field} escapes the paper folder"
    return ""


def current_v10_semantic_source_lane_errors(
    folder: Path,
    status_payload: dict[str, Any],
    *,
    context: EvidenceRunContext | None = None,
) -> list[str]:
    """Return missing configuration for the current semantic/source lanes.

    This is intentionally a configuration gate, not a replacement for the
    existing sidecar freshness, source-map, or source-proof-defect validators.
    A successful result means the full closeout is wired to the current v10
    source-route statement lane, source-first coverage lane, recursive source
    record lane, expanded semantic-model lane, and canonical fidelity ledger.
    All inputs are status schema fields and artifact locations.
    """

    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return ["status.json has no review_surface object"]

    errors: list[str] = []

    statement_review = review_surface.get("llm_statement_review")
    if not isinstance(statement_review, dict):
        errors.append("review_surface.llm_statement_review must be an object")
    else:
        if statement_review.get("require_explicit_source_routes") is not True:
            errors.append(
                "review_surface.llm_statement_review.require_explicit_source_routes "
                "must be true"
            )
        atom_requirement = statement_review.get("require_source_claim_atoms")
        if atom_requirement is not None and not isinstance(atom_requirement, bool):
            errors.append(
                "review_surface.llm_statement_review.require_source_claim_atoms "
                "must be Boolean when configured"
            )
        source_map_path = transaction_sidecar(
            folder, "paper_statement_map.json", context
        )
        source_map = transaction_json(source_map_path, context)
        atom_schema = (
            source_map.get(SOURCE_CLAIM_ATOMS_SCHEMA_KEY)
            if isinstance(source_map, dict)
            else None
        )
        if atom_schema is not None and atom_requirement is not True:
            errors.append(
                "review_surface.llm_statement_review.require_source_claim_atoms "
                "must be true when the source map opts into source_claim_atoms"
            )
        if atom_requirement is True and not schema_version_is_exact(
            atom_schema, SOURCE_CLAIM_ATOMS_SCHEMA
        ):
            errors.append(
                "review_surface.llm_statement_review.require_source_claim_atoms "
                f"requires top-level {SOURCE_CLAIM_ATOMS_SCHEMA_KEY}: "
                f"{SOURCE_CLAIM_ATOMS_SCHEMA}"
            )
        for field in V10_STATEMENT_REVIEW_ARTIFACT_FIELDS:
            error = configured_review_artifact_path_error(
                folder,
                lane="llm_statement_review",
                field=field,
                value=statement_review.get(field),
            )
            if error:
                errors.append(error)

    coverage_review = review_surface.get("llm_paper_coverage_review")
    if not isinstance(coverage_review, dict):
        errors.append("review_surface.llm_paper_coverage_review must be an object")
    else:
        for field in V10_PAPER_COVERAGE_ARTIFACT_FIELDS:
            error = configured_review_artifact_path_error(
                folder,
                lane="llm_paper_coverage_review",
                field=field,
                value=coverage_review.get(field),
            )
            if error:
                errors.append(error)

        if (
            canonical_source_map_has_source_defect_links(folder, context=context)
            or canonical_source_proof_ledger_has_defects(folder, context=context)
        ):
            error = configured_review_artifact_path_error(
                folder,
                lane="llm_paper_coverage_review",
                field="defect_support_judgment_file",
                value=coverage_review.get("defect_support_judgment_file"),
            )
            if error:
                errors.append(error)

    source_record_review = review_surface.get("llm_source_record_review")
    if not isinstance(source_record_review, dict):
        errors.append("review_surface.llm_source_record_review must be an object")
    else:
        for field in V10_SOURCE_RECORD_ARTIFACT_FIELDS:
            error = configured_review_artifact_path_error(
                folder,
                lane="llm_source_record_review",
                field=field,
                value=source_record_review.get(field),
            )
            if error:
                errors.append(error)

    semantic_model_review = review_surface.get("semantic_model_review")
    if not isinstance(semantic_model_review, dict):
        errors.append("review_surface.semantic_model_review must be an object")
    else:
        dimensions = semantic_model_review.get("required_dimensions")
        normalized_dimensions = (
            [str(dimension).strip() for dimension in dimensions]
            if isinstance(dimensions, list)
            else []
        )
        if (
            not schema_version_is_exact(
                semantic_model_review.get("schema"), SEMANTIC_MODEL_REVIEW_SCHEMA
            )
            or len(normalized_dimensions) != len(set(normalized_dimensions))
            or set(normalized_dimensions) != SEMANTIC_MODEL_REVIEW_DIMENSIONS
        ):
            errors.append(
                "review_surface.semantic_model_review must use schema 2 with every "
                "expanded-semantic dimension exactly once"
            )

    fidelity_config = source_proof_fidelity_config(status_payload)
    if fidelity_config is None:
        errors.append("review_surface.source_proof_fidelity_review must be an object")
    else:
        ledger_path, ledger_error = source_proof_fidelity_ledger_path(
            folder, status_payload
        )
        if ledger_error:
            errors.append(ledger_error)
        elif ledger_path is not None:
            canonical_ledger_path = transaction_sidecar(
                folder, "source_proof_fidelity.json", context
            )
            if ledger_path.resolve() != canonical_ledger_path.resolve():
                errors.append(
                    "review_surface.source_proof_fidelity_review.ledger_file must "
                    "resolve to the canonical source-proof fidelity ledger"
                )

    return errors


def v10_migration_pending_findings(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Fail closed on a legacy review surface after source-first closeout work.

    A formalized paper that has both source-first inventory metadata and a
    canonical fidelity ledger has enough source-facing audit infrastructure
    that omitting the current v10 lanes is dangerous.  This is a migration
    marker, rather than a declaration-name heuristic: it inspects only the
    inventory marker, canonical ledger artifact, and status/artifact schemas.
    Existing validators still check the referenced artifacts' exact contents.
    """

    if (
        status not in FULL_CLOSEOUT_STATUSES
        or not canonical_source_first_inventory_present(folder, context=context)
        or not canonical_source_proof_ledger_present(folder, context=context)
    ):
        return []
    errors = current_v10_semantic_source_lane_errors(
        folder, status_payload, context=context
    )
    if not errors:
        return []
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(folder / "status.json"),
            "v10-migration-pending: full-closeout source-first inventory plus "
            "canonical source-proof fidelity ledger lacks current semantic/source "
            "review-lane configuration: "
            + "; ".join(errors),
        )
    ]


def corrected_target_coverage_rows_match_primary(
    primary_declaration: str,
    review_rows: list[str],
    map_items: object,
    paper_name: str,
) -> bool:
    """Accept the configured endpoint or its unique dashboard-local row name.

    Source maps retain fully qualified Lean declarations, while the dashboard
    records the final PaperInterface declaration component as its review-row
    navigation name. This is an identity translation only: a short name is
    accepted solely for the configured paper's PaperInterface route, and only
    when no other configured direct route has that component. The downstream
    dashboard still checks the current elaborated signature and semantic source
    route, so this helper never grants coverage by a declaration-name match.
    """

    if review_rows == [primary_declaration]:
        return True
    if len(review_rows) != 1:
        return False

    prefix = f"{paper_name}.PaperInterface."
    if not primary_declaration.startswith(prefix):
        return False
    short_name = primary_declaration.rsplit(".", maxsplit=1)[-1]
    if not short_name or review_rows != [short_name]:
        return False
    if not isinstance(map_items, dict):
        return False

    configured_routes: set[str] = set()
    for raw_item in map_items.values():
        if not isinstance(raw_item, dict):
            continue
        declarations = raw_item.get("lean_declarations")
        if not isinstance(declarations, list):
            continue
        for raw_declaration in declarations:
            if not isinstance(raw_declaration, str):
                continue
            declaration = raw_declaration.strip()
            if (
                declaration.startswith(prefix)
                and declaration.rsplit(".", maxsplit=1)[-1] == short_name
            ):
                configured_routes.add(declaration)
    return configured_routes == {primary_declaration}


def corrected_target_coverage_rows_match_contract_spec(
    source_item: object,
    primary_declaration: str,
    review_rows: list[str],
    map_items: object,
    paper_name: str,
    *,
    semantic_contract_schema: object,
) -> bool:
    """Recognize the one transparent Spec that owns a repaired endpoint.

    A v11 source card deliberately names the paper-facing ``Spec : Prop``;
    its paired theorem is kept out of the human-review denominator and is
    checked separately by Lean Meta.  The fast evidence lane cannot see that
    Lean receipt, but it can safely perform the same narrow navigation check
    as the dashboard: the map must declare one well-formed plain ``proves``
    contract whose evidence endpoint is the sole corrected-target route.
    """

    if semantic_contract_schema not in SEMANTIC_CONTRACT_SCHEMAS:
        return False
    if not isinstance(source_item, dict):
        return False

    def contract_spec(item: object) -> tuple[str, str] | None:
        if not isinstance(item, dict):
            return None
        contract = item.get("semantic_contract")
        if not isinstance(contract, dict) or set(contract) != {
            "spec_declaration",
            "evidence_declaration",
            "evidence_mode",
            "semantic_shape",
        }:
            return None
        spec = str(contract.get("spec_declaration") or "").strip()
        evidence = str(contract.get("evidence_declaration") or "").strip()
        if (
            not spec
            or not evidence
            or spec == evidence
            or str(contract.get("evidence_mode") or "").strip() != "proves"
            or str(contract.get("semantic_shape") or "").strip() != "plain"
        ):
            return None
        return spec, evidence

    current_contract = contract_spec(source_item)
    if current_contract is None:
        return False
    spec_declaration, evidence_declaration = current_contract
    if evidence_declaration != primary_declaration:
        return False
    if review_rows == [spec_declaration]:
        return True
    if len(review_rows) != 1 or not isinstance(map_items, dict):
        return False
    prefix = f"{paper_name}.PaperInterface."
    short_name = spec_declaration.rsplit(".", maxsplit=1)[-1]
    if (
        not spec_declaration.startswith(prefix)
        or not short_name
        or review_rows != [short_name]
    ):
        return False
    configured_specs = {
        candidate[0]
        for item in map_items.values()
        for candidate in [contract_spec(item)]
        if candidate is not None
        and candidate[0].startswith(prefix)
        and candidate[0].rsplit(".", maxsplit=1)[-1] == short_name
    }
    return configured_specs == {spec_declaration}


@dataclass(frozen=True)
class SemanticContractCloseoutInventory:
    """Source-map dispositions eligible for the exact-contract closeout bridge.

    ``contract_item_keys`` are not inferred from Lean declaration spelling.
    They are the source-inventory entries that need a subsequently
    Lean-Meta-checked exact Spec/evidence route.  ``scope_exclusion_item_keys``
    remain claim-bearing source items, but have the repository's already
    byte-pinned, explicitly user-approved non-proof disposition.  They do not
    receive proof credit and are retained separately so callers cannot quietly
    treat them as ordinary proved claims.
    """

    contract_item_keys: tuple[str, ...]
    scope_exclusion_item_keys: tuple[str, ...]


def semantic_contract_closeout_bridge_inventory(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> tuple[SemanticContractCloseoutInventory | None, list[Finding]]:
    """Return the source-grounded inventory for an exact-contract closeout.

    This is deliberately a *structural* half of the bridge.  It verifies the
    canonical source artifact, every required byte-pinned source excerpt,
    corrected-target records, the semantic-contract JSON schema, and the
    narrow user-approved scope disposition.  It does not inspect a Lean route
    by name and it does not itself assert that any proof is valid; the full
    repository audit must still obtain exact Lean-Meta matches before it can
    bypass a blank legacy statement/coverage scaffold.

    A paper does not enter this lane merely because it has a source map.  It
    must opt into ``semantic_contract_schema: 1`` or ``2`` with a curated source
    inventory and exact source-anchor evidence.  Any ordinary claim-bearing
    row without a contract fails closed.  The sole non-proof disposition is a
    separately validated ``user_approved_scope_exclusion``; it remains visible
    as claim-bearing and is never counted as a proved route.
    """

    file_bytes_override = (
        context.file_bytes_override() if context is not None else None
    )
    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(map_path, context)
    if payload is None:
        return None, []
    if not isinstance(payload, dict):
        return None, source_map_scope_integrity_findings(folder, status, map_path, payload)
    if not schema_version_is_supported(
        payload.get("semantic_contract_schema"), SEMANTIC_CONTRACT_SCHEMAS
    ):
        return None, []

    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(map_path), message))

    # Keep raw map/presentation integrity outside the selected proof surface.
    findings.extend(source_map_scope_integrity_findings(folder, status, map_path, payload))
    source_coverage_mode, mode_findings = source_coverage_mode_findings(
        folder, status, map_path, payload
    )
    findings.extend(mode_findings)

    if payload.get("source_curated") is not True:
        add(
            "semantic-contract closeout bridge requires a source_curated: true "
            "inventory; a seeded or uncurated map cannot replace statement/coverage review"
        )
    if payload.get("seed_scaffold") is True:
        add(
            "semantic-contract closeout bridge cannot use a seed_scaffold source inventory"
        )
    if payload.get(SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY) is not True:
        add(
            "semantic-contract closeout bridge requires "
            f"{SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY}: true"
        )

    raw_items = payload.get("items")
    if not isinstance(raw_items, dict) or not raw_items:
        add("semantic-contract closeout bridge requires a nonempty source-map items object")
        return None, findings
    scoped_payload, coverage_items = scoped_source_map_payload(
        payload,
        source_coverage_mode,
        folder=folder,
        repository_root=ROOT,
        context=context,
    )

    # Reuse the ordinary fail-closed validators rather than duplicating or
    # weakening their artifact, anchor, correction, and scope-exclusion rules.
    findings.extend(
        source_artifact_pin_findings(
            folder,
            status,
            map_path,
            payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        source_named_result_inventory_findings(
            folder,
            status,
            map_path,
            payload,
            require_source_bytes=require_source_bytes,
            context=context,
        )
    )
    findings.extend(
        source_anchor_evidence_findings(
            folder,
            status,
            map_path,
            scoped_payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        semantic_context_requirement_findings(
            folder,
            status,
            map_path,
            scoped_payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        user_approved_scope_exclusion_map_findings(
            folder,
            status,
            map_path,
            scoped_payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        corrected_source_statement_map_findings(
            folder,
            status,
            payload,
            context=context,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        semantic_contract_inventory_findings(
            folder,
            status,
            require_source_bytes=require_source_bytes,
            context=context,
        )
    )

    contract_keys: list[str] = []
    scope_exclusion_keys: list[str] = []
    for raw_key, raw_item in coverage_items.items():
        source_key = str(raw_key).strip()
        if not source_key or not isinstance(raw_item, dict):
            # The semantic-contract schema validator records the detailed
            # shape failure.  Keep this bridge unavailable as well.
            continue
        if raw_item.get("claim_bearing") is not True:
            continue
        if not str(raw_item.get("source_location") or "").strip():
            add(
                f"items.{source_key}: semantic-contract closeout bridge requires a "
                "concrete source_location for every claim-bearing source item"
            )
            continue

        raw_contract = raw_item.get("semantic_contract")
        if isinstance(raw_contract, dict):
            # Detailed contract-shape validation is already included above.
            contract_keys.append(source_key)
            continue

        # The closeout bridge selects direct source-to-Spec routes only.  A
        # source-visible support-only lemma/proposition remains claim-bearing
        # for source inventory and proof-fidelity review, but its structured
        # source-status policy deliberately routes it as support for a
        # retained proof endpoint rather than as an additional direct
        # theorem-to-Spec obligation.  Reuse the same presentation-first
        # policy as `semantic_contract_inventory_findings`; otherwise this
        # bridge would contradict the normal v11 validator and make a valid
        # support inventory disable every independent strict receipt.
        if not _semantic_contract_item_requires_proof_evidence(
            payload, source_key, raw_item
        ):
            continue

        # Do not silently turn an approved exclusion into a proof.  This
        # branch only records the separately validated, visible disposition;
        # all ordinary claim-bearing rows need an exact contract.
        scope_error = _semantic_contract_user_scope_exclusion_error(
            folder,
            status,
            map_path,
            payload,
            raw_item,
            require_source_bytes=require_source_bytes,
        )
        if not scope_error and raw_item.get(USER_APPROVED_SCOPE_EXCLUSION) is not None:
            scope_exclusion_keys.append(source_key)
            continue
        add(
            f"items.{source_key}: semantic-contract closeout bridge requires an "
            "exact semantic_contract for every claim-bearing source item unless "
            "the existing byte-pinned user_approved_scope_exclusion validator accepts "
            "its explicit non-proof disposition"
        )

    # A user-approved exclusion is intentionally still a visible source-map
    # disposition even when the ordinary selected proof surface does not
    # include that source kind (for example, an explicitly excluded remark).
    # Keep it in the bridge inventory rather than letting the selection step
    # erase the documented non-proof decision.  It never gains proof credit.
    for raw_key, raw_item in raw_items.items():
        source_key = str(raw_key).strip()
        if (
            not source_key
            or source_key in coverage_items
            or not isinstance(raw_item, dict)
            or raw_item.get("claim_bearing") is not True
            or raw_item.get(USER_APPROVED_SCOPE_EXCLUSION) is None
        ):
            continue
        scope_error = _semantic_contract_user_scope_exclusion_error(
            folder,
            status,
            map_path,
            payload,
            raw_item,
            require_source_bytes=require_source_bytes,
        )
        if scope_error:
            add(f"items.{source_key}: {scope_error}")
        else:
            scope_exclusion_keys.append(source_key)

    if not contract_keys:
        add(
            "semantic-contract closeout bridge requires at least one claim-bearing "
            "source item with an exact Spec/evidence contract"
        )
    if findings:
        return None, findings
    return (
        SemanticContractCloseoutInventory(
            contract_item_keys=tuple(sorted(contract_keys)),
            scope_exclusion_item_keys=tuple(sorted(scope_exclusion_keys)),
        ),
        [],
    )


def corrected_model_anchor_errors(folder: Path, value: object) -> list[str]:
    """Validate corrected-scope anchors in local docs or the pinned source tarball."""

    if not isinstance(value, str):
        return []
    archive_path = folder / "source.tar.gz"
    errors: list[str] = []
    for match in SOURCE_FILE_LINE_RE.finditer(value):
        raw_path = Path(match.group("path"))
        start = int(match.group("start"))
        end = int(match.group("end") or start)
        try:
            local = (folder / raw_path).resolve()
            local.relative_to(folder.resolve())
        except (OSError, RuntimeError, ValueError):
            errors.append(f"corrected-model anchor `{raw_path}` escapes the paper folder")
            continue
        text: str | None = None
        if local.is_file() and local.suffix.lower() in TEXT_SOURCE_SUFFIXES:
            try:
                text = local.read_text(encoding="utf-8")
            except OSError:
                errors.append(f"corrected-model anchor `{raw_path}` could not be read")
                continue
        elif archive_path.is_file():
            try:
                with tarfile.open(archive_path, "r:*") as archive:
                    members = [
                        member
                        for member in archive.getmembers()
                        if member.isfile()
                        and (member.name == str(raw_path) or member.name.endswith(f"/{raw_path}"))
                    ]
                    if len(members) != 1:
                        errors.append(
                            f"corrected-model anchor `{raw_path}` does not identify one source file "
                            "in the pinned archive"
                        )
                        continue
                    if Path(members[0].name).suffix.lower() not in TEXT_SOURCE_SUFFIXES:
                        continue
                    stream = archive.extractfile(members[0])
                    if stream is None:
                        errors.append(f"corrected-model anchor `{raw_path}` could not be extracted")
                        continue
                    text = stream.read().decode("utf-8", errors="replace")
            except (OSError, tarfile.TarError):
                errors.append("pinned source archive could not be read for corrected-model anchors")
                continue
        else:
            errors.append(
                f"corrected-model anchor `{raw_path}` is neither local nor present in the pinned source archive"
            )
            continue
        if text is None:
            continue
        line_count = len(text.splitlines())
        if start < 1 or end < start or end > line_count:
            errors.append(
                f"corrected-model anchor `{raw_path}:{start}-{end}` is outside its {line_count}-line source"
            )
    return errors


def _source_proof_fidelity_findings_uncached(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Add recorded legacy prerequisites to the shared source-only validator."""

    migration = (
        [] if isinstance(context, V11EvidenceRunContext)
        else v10_migration_pending_findings(folder, status, status_payload, context=context)
    )
    return source_proof_fidelity_ledger_findings(
        folder, status, status_payload,
        require_source_bytes=require_source_bytes,
        context=context,
        file_bytes_override=file_bytes_override,
        migration_findings=migration,
        corrected_scope_findings=lambda: corrected_model_scope_contract_findings(
            folder, status, status_payload
        ),
    )


def source_proof_fidelity_findings(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Validate source-proof fidelity once per exact evidence transaction.

    The primary repository gate and deferred evidence-integrity gate both
    require this complete ledger verdict. A builder-issued context freezes all
    of its inputs and owns the final mutation guard, so they share one immutable
    result. Explicit byte overrides and callers without that exact capability
    still execute the full validator on every call.
    """

    def compute() -> list[Finding]:
        return _source_proof_fidelity_findings_uncached(
            folder,
            status,
            status_payload,
            require_source_bytes=require_source_bytes,
            context=context,
            file_bytes_override=file_bytes_override,
        )
    if (
        file_bytes_override is not None
        or not isinstance(context, EvidenceRunContext)
        or status_payload != context.status_payload
    ):
        return compute()
    return _run_scoped_validation_findings(
        context,
        folder=folder,
        status=status,
        require_source_bytes=require_source_bytes,
        validator="source_proof_fidelity",
        compute=compute,
    )


def _semantic_contract_revalidation_module() -> Any:
    """Load the optional structural replay without changing raw generation."""

    from scripts import source_record_semantic_contract_revalidation as replay
    return replay


def source_record_semantic_contract_revalidation_context(
    folder: Path,
    audit_payload: Mapping[str, Any],
    *,
    status_payload: Mapping[str, Any] | None = None,
) -> tuple[Any | None, str]:
    """Validate the fixed structural replay for a standalone evidence consumer.

    The replay itself checks the exact configured raw bytes, canonical map
    bytes, and optional artifact. An absent artifact returns an empty
    projection, while a malformed or stale artifact fails closed. Transaction
    callers pass snapshot-derived values directly through ``EvidenceRunContext``
    instead. This standalone adapter resolves the configured raw path once and
    supplies those exact bytes; the replay must not silently reopen the default
    canonical path after its caller loaded a different configured carrier.
    """

    try:
        configured_status = (
            dict(status_payload)
            if isinstance(status_payload, Mapping)
            else (load_json(folder / "status.json") or {})
        )
        raw_path, raw_path_error = source_record_review_sidecar_path(
            folder,
            configured_status,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
        if raw_path_error or raw_path is None:
            return None, raw_path_error or "source-record audit path is unavailable"
        raw_bytes = raw_path.read_bytes()
        replay = _semantic_contract_revalidation_module()
        return replay.semantic_contract_revalidation_projection(
            paper_dir=folder,
            paper=folder.name,
            raw_audit=audit_payload,
            raw_audit_raw_bytes=raw_bytes,
        )
    except Exception as error:  # noqa: BLE001 - optional authority fails closed.
        return None, (
            "could not validate semantic-contract revalidation: "
            f"{type(error).__name__}: {error}"
        )


def _trusted_semantic_contract_revalidation_projection(value: Any) -> Any | None:
    """Accept only the replay module's immutable projection type."""

    try:
        replay = _semantic_contract_revalidation_module()
    except Exception:  # noqa: BLE001 - caller receives no structural credit.
        return None
    return value if replay.projection_is_authenticated(value) else None


def source_record_effective_input_judgment_keys(
    audit_payload: Mapping[str, Any],
    *,
    semantic_contract_revalidation: Any | None = None,
) -> set[str]:
    """Return input obligations after current ledger and structural replay.

    This is intentionally narrower than ``source_record_required_keys`` so
    closeout consumers that separately account for recursive fields and model
    dimensions can share the same authenticated input projection.
    """

    expected_inputs = {
        str(key).strip()
        for key in audit_payload.get("expected_input_judgment_keys") or []
        if str(key).strip()
    }
    statement_ledger_covered = {
        str(key).strip()
        for key in audit_payload.get(
            "statement_ledger_covered_boundary_input_keys"
        )
        or []
        if str(key).strip()
    }
    conclusion_dependency_keys = {
        str(item.get("judgment_key") or "").strip()
        for item in audit_payload.get("conclusion_dependency_items") or []
        if isinstance(item, Mapping)
        and str(item.get("judgment_key") or "").strip()
    }
    # A statement ledger validates endpoint/source correspondence. It does
    # not prove a caller-supplied input that semantic analysis identifies as
    # conclusion-bearing.
    statement_ledger_covered -= conclusion_dependency_keys
    projection = _trusted_semantic_contract_revalidation_projection(
        semantic_contract_revalidation
    )
    suppressed_inputs = (
        set(projection.suppressed_expected_input_keys)
        if projection is not None
        else set()
    )
    return expected_inputs - statement_ledger_covered - suppressed_inputs


def source_record_required_keys(
    audit_payload: dict[str, Any],
    *,
    semantic_contract_revalidation: Any | None = None,
) -> list[str]:
    expected_inputs = {
        str(key).strip()
        for key in audit_payload.get("expected_input_judgment_keys") or []
        if str(key).strip()
    }
    expected_fields = {
        str(key).strip()
        for key in audit_payload.get("expected_field_judgment_keys") or []
        if str(key).strip()
    }
    expected_semantic_model = {
        str(key).strip()
        for key in audit_payload.get("expected_semantic_model_judgment_keys") or []
        if str(key).strip()
    }
    if expected_inputs or expected_fields or expected_semantic_model:
        return sorted(
            source_record_effective_input_judgment_keys(
                audit_payload,
                semantic_contract_revalidation=semantic_contract_revalidation,
            )
            | expected_fields
            | expected_semantic_model
        )

    # Older source-record payloads predate the explicit expected-key ledgers.
    keys: list[str] = []
    for item_key in (
        "boundary_input_items",
        "recursive_field_items",
        "semantic_model_items",
    ):
        raw_items = audit_payload.get(item_key) or []
        if not isinstance(raw_items, list):
            continue
        for item in raw_items:
            if not isinstance(item, dict):
                continue
            if not schema_version_is_exact(
                item.get("source_record_item_digest_schema"),
                SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            ):
                continue
            key = str(item.get("judgment_key") or "").strip()
            if key:
                keys.append(key)
    return sorted(set(keys))


def source_record_required_item_digest_candidates(
    audit_payload: dict[str, Any],
) -> dict[str, set[str]]:
    """Return every eligible item receipt seen for each current judgment key.

    This mirrors the generator's cache contract.  A key with different receipts
    across generated sections cannot use scalar reuse; a shared receipt at two
    different keys remains valid for direct same-key reuse but is not a safe
    key-independent remapping token.
    """

    candidate_digests: dict[str, set[str]] = {}
    for item_key in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        raw_items = audit_payload.get(item_key) or []
        if not isinstance(raw_items, list):
            continue
        for item in raw_items:
            if not isinstance(item, dict):
                continue
            if not source_record_item_reuse_eligible(
                item,
                expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            ):
                continue
            key = str(item.get("judgment_key") or "").strip()
            digest = str(item.get("source_record_item_sha256") or "").strip()
            if key and digest:
                candidate_digests.setdefault(key, set()).add(digest)
    return candidate_digests


def source_record_required_item_digests(audit_payload: dict[str, Any]) -> dict[str, str]:
    """Return one complete current receipt for each direct judgment key.

    An ordinary input and its conclusion-dependency expansion can share a key
    while requiring different reviews. Different digests are intentionally
    omitted, forcing freshness through the current aggregate source-record
    digest rather than accepting the weaker item-level surface.

    Different keys may retain the same complete receipt. A direct sidecar entry
    is still safe because its key selects the current obligation; only a
    key-independent remap must require global digest uniqueness.
    """

    return {
        key: next(iter(digests))
        for key, digests in source_record_required_item_digest_candidates(
            audit_payload
        ).items()
        if len(digests) == 1
    }


def source_record_unique_item_digest_keys(
    audit_payload: dict[str, Any],
) -> dict[str, str]:
    """Return only digest-to-key identities safe for a renamed sidecar entry."""

    keys_by_digest: dict[str, set[str]] = {}
    for key, digest in source_record_required_item_digests(audit_payload).items():
        keys_by_digest.setdefault(digest, set()).add(key)
    return {
        digest: next(iter(keys))
        for digest, keys in keys_by_digest.items()
        if len(keys) == 1
    }


def current_paper_statement_map_sha256(folder: Path) -> str:
    """Return the byte identity of the source map currently on disk.

    Source-record judgments may be reused at item granularity, so their saved
    audit must still be tied to the current source inventory as a whole.  This
    helper intentionally hashes the map bytes rather than parsed JSON: any
    source-map edit, including a source locator or scope change, requires a
    fresh generated audit.
    """

    map_path = canonical_sidecar(folder, "paper_statement_map.json")
    try:
        return hashlib.sha256(map_path.read_bytes()).hexdigest()
    except OSError:
        return ""


def current_paper_statement_map_semantic_sha256(folder: Path) -> str:
    """Return the narrow map receipt allowed for raw-cache reuse only.

    This is deliberately separate from the full byte receipt above.  It drops
    only explicitly administrative direct source-item metadata; every other
    source-map edit remains part of the evidence/currentness boundary.
    """

    map_path = canonical_sidecar(folder, "paper_statement_map.json")
    try:
        payload = json.loads(map_path.read_bytes())
    except (OSError, json.JSONDecodeError):
        return ""
    return source_map_cache_semantic_sha256(payload)


def source_record_legacy_v7_fingerprint_is_current(
    legacy_v7: Mapping[str, Any], current: Mapping[str, Any]
) -> bool:
    """Validate the explicit v7 migration identity against current v8 inputs.

    The source-record helper reconstructs this object from the historical
    broad-status/full-ledger algorithm.  Do not accept a merely schema-7-shaped
    payload: every field other than the two deliberately narrowed content
    projections and the schema must agree with current source/interface/map,
    engine, toolchain, and execution inputs.  This makes missing fields or an
    unrecognized future cache schema fail closed.
    """

    if not schema_version_is_exact(legacy_v7.get("schema"), 7):
        return False
    if schema_version_is_exact(current.get("schema"), 7):
        # Pre-projection helper output is an ordinary exact v7 identity.
        return dict(legacy_v7) == dict(current)
    if not schema_version_is_exact(current.get("schema"), 8) or set(legacy_v7) != set(current):
        return False
    narrowed_fields = {
        "schema",
        "relevant_status_sha256",
        "source_proof_fidelity_sha256",
    }
    return all(
        legacy_v7.get(key) == current.get(key)
        for key in current
        if key not in narrowed_fields
    )


def source_record_legacy_v6_fingerprint_matches_current(
    stored: Mapping[str, Any],
    current: Mapping[str, Any],
    *,
    recorded_map_sha256: str,
    current_map_sha256: str,
) -> bool:
    """Accept the exact v6 cache identity only with unchanged map provenance.

    The source-record generator itself retains this compatibility path while a
    paper still has a schema-6 raw receipt.  A v6 fingerprint recorded the
    full map byte hash instead of the v7 semantic receipt, so it cannot use
    any map-edit exception.  Keeping this comparison here identical prevents
    the evidence gate from rejecting a raw audit that the cache correctly
    recognizes as current.
    """

    recorded = recorded_map_sha256.strip().lower()
    current_map = current_map_sha256.strip().lower()
    if not (
        SHA256_RE.fullmatch(recorded)
        and recorded == current_map
        and schema_version_is_exact(current.get("schema"), 7)
    ):
        return False
    legacy = dict(current)
    legacy["schema"] = 6
    legacy.pop("paper_statement_map_semantic_sha256", None)
    legacy["paper_statement_map_sha256"] = current_map
    return dict(stored) == legacy


_SOURCE_RECORD_IDENTITY_STATUS_SOURCE_PATH_FIELDS = (
    "source_file",
    "human_source_file",
    "assumption_source_file",
)
_SOURCE_RECORD_IDENTITY_MAP_ARTIFACT_PATH_FIELDS = (
    "source_artifact_path",
    "canonical_source_artifact_path",
)


def _source_record_identity_map_artifact_values(value: object) -> list[str]:
    """Return schema-declared map artifact paths without name heuristics.

    This deliberately mirrors the raw source-record producer's structured
    source-artifact projection: canonical/source artifacts may occur at any
    map depth, while an ordinary ``path`` field is an artifact route only
    inside ``source_anchor_evidence``.  Lean declaration and map-item names do
    not participate in discovery.
    """

    values: list[str] = []
    if isinstance(value, list):
        for child in value:
            values.extend(_source_record_identity_map_artifact_values(child))
        return values
    if not isinstance(value, dict):
        return values
    for field in _SOURCE_RECORD_IDENTITY_MAP_ARTIFACT_PATH_FIELDS:
        raw = value.get(field)
        if isinstance(raw, str) and raw.strip():
            values.append(raw.strip())
    anchors = value.get("source_anchor_evidence")
    if isinstance(anchors, list):
        for anchor in anchors:
            if not isinstance(anchor, dict):
                continue
            raw = anchor.get("path")
            if isinstance(raw, str) and raw.strip():
                values.append(raw.strip())
    for child in value.values():
        if isinstance(child, (dict, list)):
            values.extend(_source_record_identity_map_artifact_values(child))
    return values


def _source_record_identity_trusted_candidates(
    folder: Path,
    raw_path: str,
    *,
    status_source: bool,
) -> tuple[set[Path], str]:
    """Resolve a declared path under the trusted checkout, or mark it unsafe.

    Map artifacts preserve the producer's paper-relative-then-repository-
    relative resolution and watch both safe candidates.  Watching a currently
    missing candidate is intentional: creating the higher-priority file must
    invalidate a cached producer result.  Status source routes use their
    schema's single-component paper-relative convention.
    """

    root = ROOT.resolve()
    relative = Path(raw_path)
    if relative.is_absolute():
        raw_candidates = [relative]
    elif status_source:
        raw_candidates = [
            folder / relative if len(relative.parts) == 1 else ROOT / relative
        ]
    else:
        raw_candidates = [folder / relative, ROOT / relative]
    candidates: set[Path] = set()
    rejected = False
    for raw_candidate in raw_candidates:
        try:
            candidate = raw_candidate.resolve()
            candidate.relative_to(root)
        except (OSError, RuntimeError, ValueError):
            rejected = True
            continue
        candidates.add(candidate)
    if candidates:
        marker = "partially-untrusted" if rejected else "trusted"
        return candidates, marker
    return set(), "untrusted"


def _source_record_identity_declared_watch_paths(
    folder: Path,
) -> tuple[set[Path], list[str]]:
    """Resolve all structured status/map source artifacts for memoization.

    Parse failures and unsafe routes are retained as digest markers rather
    than ignored.  The status/map bytes are also in the paper-tree watch, so a
    repair changes both the structural marker and the governing input bytes.
    """

    paths: set[Path] = set()
    markers: list[str] = []

    status_path = folder / "status.json"
    try:
        status = json.loads(status_path.read_bytes())
    except FileNotFoundError:
        status = None
        markers.append("status:missing")
    except (OSError, json.JSONDecodeError) as error:
        status = None
        markers.append(f"status:unreadable:{type(error).__name__}")
    review_surface = status.get("review_surface") if isinstance(status, dict) else None
    if isinstance(review_surface, dict):
        for field in _SOURCE_RECORD_IDENTITY_STATUS_SOURCE_PATH_FIELDS:
            raw = review_surface.get(field)
            if raw is None:
                continue
            if not isinstance(raw, str) or not raw.strip():
                markers.append(f"status:{field}:malformed")
                continue
            candidates, trust = _source_record_identity_trusted_candidates(
                folder, raw.strip(), status_source=True
            )
            paths.update(candidates)
            markers.append(f"status:{field}:{trust}:{raw.strip()}")
    elif isinstance(status, dict) and "review_surface" in status:
        markers.append("status:review_surface:malformed")

    map_path = canonical_sidecar(folder, "paper_statement_map.json")
    try:
        statement_map = json.loads(map_path.read_bytes())
    except FileNotFoundError:
        statement_map = None
        markers.append("map:missing")
    except (OSError, json.JSONDecodeError) as error:
        statement_map = None
        markers.append(f"map:unreadable:{type(error).__name__}")
    if isinstance(statement_map, dict):
        for raw in sorted(set(_source_record_identity_map_artifact_values(statement_map))):
            candidates, trust = _source_record_identity_trusted_candidates(
                folder, raw, status_source=False
            )
            paths.update(candidates)
            markers.append(f"map:artifact:{trust}:{raw}")
    elif statement_map is not None:
        markers.append("map:malformed")
    return paths, sorted(markers)


def _fingerprint_identity_watch_paths(
    audit_payload: Mapping[str, Any] | None,
) -> tuple[set[Path], list[str]]:
    """Resolve exact file coordinates already named by the raw fingerprint."""

    paths: set[Path] = set()
    markers: list[str] = []
    fingerprint = (
        audit_payload.get("source_record_input_fingerprint")
        if isinstance(audit_payload, Mapping)
        else None
    )
    if not isinstance(fingerprint, Mapping):
        return paths, ["fingerprint:missing"]

    identity_fields = (
        "audit_engine_identities",
        "raw_producer_code_identities",
        "lean_dependency_identities",
        "source_artifact_identities",
        "review_assumption_source",
        "review_interface_source",
        "toolchain_identities",
    )

    def collect(value: object) -> None:
        if isinstance(value, Mapping):
            raw_path = value.get("path")
            if isinstance(raw_path, str) and raw_path.strip():
                relative = raw_path.split("#", 1)[0].strip()
                candidate = Path(relative)
                try:
                    if candidate.is_absolute():
                        raise ValueError
                    resolved = (ROOT / candidate).resolve()
                    resolved.relative_to(ROOT.resolve())
                except (OSError, RuntimeError, ValueError):
                    markers.append("fingerprint:path-invalid:" + raw_path)
                else:
                    paths.add(resolved)
            for nested in value.values():
                collect(nested)
        elif isinstance(value, (list, tuple)):
            for nested in value:
                collect(nested)

    for field in identity_fields:
        collect(fingerprint.get(field))
    return paths, markers


def _source_record_identity_process_watch_digest(
    folder: Path,
    *,
    audit_payload: Mapping[str, Any] | None = None,
) -> str:
    """Hash exact semantic producer/source inputs for one evidence transaction.

    The source-record fingerprint and configured source/map routes define this
    envelope. Ignored dashboard caches, archival scratch files, and unrelated
    paper or audit modules are deliberately absent: they are neither consumed
    inputs nor authority and must not invalidate a successful closeout.
    """

    paths, fingerprint_markers = _fingerprint_identity_watch_paths(
        audit_payload
    )
    declared_paths, declared_markers = _source_record_identity_declared_watch_paths(
        folder
    )
    paths.update(declared_paths)
    paths.update(
        {
            ROOT / "config" / "formalization_audit_protocol.json",
            ROOT / "lean-toolchain",
            ROOT / "lake-manifest.json",
            ROOT / "lakefile.lean",
            ROOT / "lakefile.toml",
            ROOT / "papers" / f"{folder.name}.lean",
            Path(__file__).resolve(),
            ROOT
            / "skills"
            / "econcs-formalizer"
            / "scripts"
            / "source_record_audit.py",
        }
    )
    digest = hashlib.sha256()
    for marker in sorted((*fingerprint_markers, *declared_markers)):
        digest.update(b"declared\0")
        digest.update(marker.encode("utf-8", errors="surrogateescape"))
        digest.update(b"\0")
    for path in sorted(paths, key=lambda candidate: str(candidate)):
        try:
            display = str(path.resolve().relative_to(ROOT))
        except (OSError, RuntimeError, ValueError):
            display = str(path)
        digest.update(display.encode("utf-8", errors="surrogateescape"))
        digest.update(b"\0")
        try:
            content = path.read_bytes()
        except OSError:
            digest.update(b"<missing>\0")
            continue
        digest.update(str(len(content)).encode("ascii"))
        digest.update(b"\0")
        digest.update(hashlib.sha256(content).digest())
        digest.update(b"\0")
    return digest.hexdigest()


class SourceRecordIdentityRevalidationBusy(RuntimeError):
    """Raised when a fresh source-record scan owns the shared evidence lock."""


class SourceRecordIdentityContextDeferred(RuntimeError):
    """A live identity context could not be minted while a raw scan is busy."""


_CURRENT_SOURCE_RECORD_IDENTITY_CONTEXT_SENTINEL = object()
_SOURCE_RECORD_IDENTITY_REVALIDATION_DEFERRED_PREFIX = (
    "source-record identity revalidation deferred:"
)


@dataclass(frozen=True)
class _CurrentSourceRecordIdentityBinding:
    """Exact live inputs covered by one reusable current-identity result.

    This records only in-process verification inputs, not an evidence receipt.
    It deliberately includes both raw-file bytes and the parsed raw surface:
    callers often hold parsed JSON while a later write could otherwise leave
    the canonical file on disk different from the object that was checked.
    """

    paper_dir: Path
    paper: str
    current_raw_canonical_sha256: str
    current_source_record_audit_sha256: str
    raw_paper_statement_map_sha256: str
    canonical_raw_path: Path
    canonical_raw_file_sha256: str
    statement_map_path: Path
    live_paper_statement_map_sha256: str
    watched_input_digest: str


@dataclass(frozen=True)
class _CurrentSourceRecordIdentityContext:
    """Opaque, per-invocation capability for a checked canonical raw audit.

    It is intentionally private, nonserializable, and cannot be recreated by
    a JSON sidecar.  Reuse always recomputes the raw/map/watch binding below;
    it only avoids replaying the expensive external-artifact helper after that
    binding still proves the exact same live inputs.
    """

    binding: _CurrentSourceRecordIdentityBinding
    # The builder freezes this exact mapping after reading its byte-pinned
    # canonical source-record file.  Retaining object identity lets nested
    # checks avoid repeatedly canonicalizing a very large immutable JSON
    # payload, without granting the optimization to caller-supplied objects.
    raw_audit_payload: Mapping[str, Any] = dataclass_field(
        repr=False,
        compare=False,
    )
    _token: object = dataclass_field(repr=False, compare=False)


def _source_record_identity_context_sha256(value: object) -> str:
    """Return a canonical content digest for an in-memory JSON audit object."""

    try:
        encoded = json.dumps(
            canonical_digest_payload(value),
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    except (TypeError, ValueError):
        return ""
    return hashlib.sha256(encoded).hexdigest()


def _source_record_identity_context_hex(value: object) -> str:
    """Normalize one SHA-256 field without treating malformed text as a pin."""

    text = str(value or "").strip().lower()
    return text if SHA256_RE.fullmatch(text) else ""


def _current_source_record_identity_binding(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    watched_input_digest_override: str | None = None,
    trusted_canonical_raw_file_sha256: str | None = None,
) -> tuple[_CurrentSourceRecordIdentityBinding | None, str]:
    """Bind a supplied raw object to the canonical current raw/map/watch state.

    This is deliberately stricter than the ordinary identity helper's parsed
    receipt check: a reusable capability is allowed only for the canonical
    live raw file consumed by the current-paper workflow.  Historical raw
    paths remain on their existing replay path and never receive a context.
    """

    if not isinstance(current_raw_audit, Mapping):
        return None, "current source-record identity context raw audit is not an object"
    try:
        resolved_paper_dir = paper_dir.resolve()
    except (OSError, RuntimeError):
        return None, "current source-record identity context paper directory cannot be resolved"
    if resolved_paper_dir.name != paper:
        return None, "current source-record identity context paper directory belongs to another paper"
    if str(current_raw_audit.get("paper") or "").strip() != paper:
        return None, "current source-record identity context belongs to another paper"
    raw_digest = _source_record_identity_context_hex(
        current_raw_audit.get("source_record_audit_sha256")
    )
    raw_map_digest = _source_record_identity_context_hex(
        current_raw_audit.get("paper_statement_map_sha256")
    )
    if not raw_digest or not raw_map_digest:
        return None, "current source-record identity context raw audit lacks canonical receipts"

    canonical_raw_path = resolved_paper_dir / "audit" / "source_record_audit.json"
    try:
        canonical_raw_bytes = canonical_raw_path.read_bytes()
    except OSError as exc:
        return None, "current source-record identity context cannot read canonical raw audit: " + str(exc)
    canonical_raw_file_sha256 = hashlib.sha256(canonical_raw_bytes).hexdigest()
    trusted_file_digest = _source_record_identity_context_hex(
        trusted_canonical_raw_file_sha256
    )
    if trusted_file_digest:
        # This fast path is available only to the exact immutable object read
        # by ``build_evidence_run_context``.  Its raw bytes are still read and
        # rehashed on every check, so a changed canonical file cannot reuse a
        # context.  Other callers retain the complete parsed/canonical replay
        # below.
        if canonical_raw_file_sha256 != trusted_file_digest:
            return None, "current source-record identity context raw file changed"
        payload_digest = canonical_raw_file_sha256
    else:
        payload_digest = _source_record_identity_context_sha256(current_raw_audit)
        if not payload_digest:
            return None, "current source-record identity context raw audit lacks canonical receipts"
        try:
            canonical_raw = json.loads(canonical_raw_bytes)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            return None, "current source-record identity context cannot read canonical raw audit: " + str(exc)
        if not isinstance(canonical_raw, Mapping):
            return None, "current source-record identity context canonical raw audit is not an object"
        if _source_record_identity_context_sha256(canonical_raw) != payload_digest:
            return None, "current source-record identity context raw audit is stale for canonical raw bytes"
        if _source_record_identity_context_hex(
            canonical_raw.get("source_record_audit_sha256")
        ) != raw_digest:
            return None, "current source-record identity context canonical raw receipt changed"

    statement_map_path = canonical_sidecar(resolved_paper_dir, "paper_statement_map.json")
    try:
        statement_map_bytes = statement_map_path.read_bytes()
    except OSError as exc:
        return None, "current source-record identity context cannot read paper statement map: " + str(exc)
    live_map_digest = hashlib.sha256(statement_map_bytes).hexdigest()
    watched_input_digest = (
        watched_input_digest_override.strip()
        if isinstance(watched_input_digest_override, str)
        and watched_input_digest_override.strip()
        else _source_record_identity_process_watch_digest(
            resolved_paper_dir,
            audit_payload=current_raw_audit,
        )
    )
    if not watched_input_digest:
        return None, "current source-record identity context has no watched-input digest"
    return (
        _CurrentSourceRecordIdentityBinding(
            paper_dir=resolved_paper_dir,
            paper=paper,
            current_raw_canonical_sha256=payload_digest,
            current_source_record_audit_sha256=raw_digest,
            raw_paper_statement_map_sha256=raw_map_digest,
            canonical_raw_path=canonical_raw_path,
            canonical_raw_file_sha256=canonical_raw_file_sha256,
            statement_map_path=statement_map_path,
            live_paper_statement_map_sha256=live_map_digest,
            watched_input_digest=watched_input_digest,
        ),
        "",
    )


def current_source_record_identity_context_error(
    context: object,
    *,
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    expected_paper_statement_map_sha256: str | None = None,
) -> str:
    """Reject a reusable identity capability unless every live binding agrees.

    This helper intentionally does *not* replay the external identity helper.
    Its caller can only reach this point through an opaque capability minted by
    :func:`prepare_current_source_record_identity_context` or the exact
    evidence transaction builder.  It rechecks canonical raw bytes, the live
    statement map, and the complete producer/source watch before each reuse.
    """

    if not isinstance(context, _CurrentSourceRecordIdentityContext):
        return "current source-record identity context is not a private capability"
    if context._token is not _CURRENT_SOURCE_RECORD_IDENTITY_CONTEXT_SENTINEL:
        return "current source-record identity context lacks issuer authority"
    # Reuse races the same producer that mints canonical raw receipts.  Hold a
    # nonblocking shared lock across every live read and the non-external
    # replay below, so a producer cannot begin an exclusive publication after
    # the raw/map/watch binding has been sampled.  Lock contention is neither
    # an empty optional lane nor an authorization; callers must retry.
    try:
        with _source_record_identity_read_lock(ROOT):
            return _current_source_record_identity_context_locked_error(
                context,
                paper_dir=paper_dir,
                paper=paper,
                current_raw_audit=current_raw_audit,
                expected_paper_statement_map_sha256=(
                    expected_paper_statement_map_sha256
                ),
            )
    except SourceRecordIdentityRevalidationBusy as exc:
        return "source-record identity revalidation deferred: " + str(exc)


def _current_source_record_identity_context_locked_error(
    context: _CurrentSourceRecordIdentityContext,
    *,
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    expected_paper_statement_map_sha256: str | None,
) -> str:
    """Revalidate an already-authenticated context while the producer is blocked."""

    trusted_raw_file_sha256 = (
        context.binding.canonical_raw_file_sha256
        if (
            current_raw_audit is context.raw_audit_payload
            # The builder's fast binding deliberately stores the exact
            # byte-file digest in this field.  Contexts issued through the
            # public compatibility helper retain the canonical JSON digest
            # and must keep using the full replay.
            and context.binding.current_raw_canonical_sha256
            == context.binding.canonical_raw_file_sha256
        )
        else None
    )
    live_binding, binding_error = _current_source_record_identity_binding(
        paper_dir,
        paper,
        current_raw_audit,
        trusted_canonical_raw_file_sha256=trusted_raw_file_sha256,
    )
    if binding_error:
        return binding_error
    assert live_binding is not None
    if live_binding != context.binding:
        return "current source-record identity context is stale for live raw/map/watch inputs"
    if expected_paper_statement_map_sha256 is not None:
        expected = _source_record_identity_context_hex(
            expected_paper_statement_map_sha256
        )
        if not expected:
            return "current source-record identity context received a malformed expected statement-map digest"
        if expected != live_binding.live_paper_statement_map_sha256:
            return "current source-record identity context does not match the expected statement map"
    # A builder-issued fast binding already passed the complete identity gate
    # for this immutable snapshot.  The raw-file byte hash, live map hash,
    # producer/source watch digest, and the transaction's final input-mutation
    # check above/below retain its fail-closed coverage without recomputing the
    # multi-megabyte aggregate receipt for every nested overlay.  Public
    # compatibility contexts retain their canonical JSON digest and keep the
    # complete non-external replay.
    if trusted_raw_file_sha256:
        return ""

    # Re-run the non-external portion of the ordinary identity gate as well
    # for contexts not issued from an exact frozen builder snapshot.
    nonexternal_error = _source_record_audit_identity_error(
        dict(current_raw_audit),
        expected_paper_statement_map_sha256=(
            live_binding.live_paper_statement_map_sha256
        ),
        folder=live_binding.paper_dir,
        prevalidated_current_input_fingerprint_error="",
    )
    if nonexternal_error:
        return "current source-record identity context non-external replay failed: " + nonexternal_error
    return ""


def _issue_current_source_record_identity_context(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    source_record_identity_error: str,
    watched_input_digest: str | None = None,
    trusted_canonical_raw_file_sha256: str | None = None,
) -> object | None:
    """Issue a runtime-only context after a caller already ran the strict gate."""

    if source_record_identity_error:
        return None
    binding, binding_error = _current_source_record_identity_binding(
        paper_dir,
        paper,
        current_raw_audit,
        watched_input_digest_override=watched_input_digest,
        trusted_canonical_raw_file_sha256=trusted_canonical_raw_file_sha256,
    )
    if binding_error or binding is None:
        return None
    return _CurrentSourceRecordIdentityContext(
        binding=binding,
        raw_audit_payload=current_raw_audit,
        _token=_CURRENT_SOURCE_RECORD_IDENTITY_CONTEXT_SENTINEL,
    )


def prepare_current_source_record_identity_context(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
) -> object | None:
    """Run one strict current identity gate and return an opaque reusable result.

    The capability is scoped to this Python invocation only.  It is never put
    in a receipt and a later invocation must rerun the strict helper.  A
    transient lock conflict is surfaced explicitly so optional overlay callers
    cannot mistake it for an absent lane.
    """

    before, binding_error = _current_source_record_identity_binding(
        paper_dir,
        paper,
        current_raw_audit,
    )
    if binding_error or before is None:
        return None
    identity_error = source_record_audit_identity_error(
        dict(current_raw_audit),
        expected_paper_statement_map_sha256=(
            before.live_paper_statement_map_sha256
        ),
        folder=before.paper_dir,
    )
    if identity_error:
        if identity_error.strip().startswith(
            _SOURCE_RECORD_IDENTITY_REVALIDATION_DEFERRED_PREFIX
        ):
            raise SourceRecordIdentityContextDeferred(identity_error)
        return None
    after, after_error = _current_source_record_identity_binding(
        paper_dir,
        paper,
        current_raw_audit,
    )
    if after_error or after is None or after != before:
        return None
    return _CurrentSourceRecordIdentityContext(
        binding=after,
        raw_audit_payload=current_raw_audit,
        _token=_CURRENT_SOURCE_RECORD_IDENTITY_CONTEXT_SENTINEL,
    )


@contextmanager
def _source_record_identity_read_lock(root: Path):
    """Hold the producer's shared lock during one strict identity replay.

    A fresh raw source-record scan holds this lock exclusively because it may
    build Lean modules and publish a new raw receipt.  The evidence gate cannot
    safely call a receipt current while that work is in flight, and competing
    for the same Lake and artifact I/O made an otherwise read-only gate appear
    to hang.  A nonblocking shared lock preserves the raw producer's authority
    without importing it (which would create an import cycle).
    """

    lock_path = root.resolve() / SOURCE_RECORD_AUDIT_LOCK_RELATIVE_PATH
    try:
        lock_path.parent.mkdir(parents=True, exist_ok=True)
        handle = lock_path.open("a+", encoding="utf-8")
    except OSError as exc:
        raise SourceRecordIdentityRevalidationBusy(
            "could not open the repository source-record evidence lock: " + str(exc)
        ) from exc
    try:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_SH | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise SourceRecordIdentityRevalidationBusy(
                "a fresh source-record scan currently owns the repository evidence "
                "lock; wait for that scan to finish, then rerun this evidence gate once"
            ) from exc
        try:
            yield
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
    finally:
        handle.close()


def _source_record_identity_external_module_count(
    audit_payload: Mapping[str, Any],
) -> int:
    """Return an informational count without trusting it as audit evidence."""

    closure = audit_payload.get("lean_import_closure")
    modules = (
        closure.get("external_import_modules")
        if isinstance(closure, Mapping)
        else None
    )
    return len(modules) if isinstance(modules, list) else 0


@contextmanager
def _source_record_identity_progress(
    folder: Path,
    audit_payload: Mapping[str, Any],
):
    """Emit bounded stderr progress around a strict identity subprocess.

    The helper emits one JSON object only on completion.  Its exact external
    artifact revalidation can therefore be I/O-heavy without producing stdout
    for tens of seconds.  These stderr messages are deliberately diagnostic;
    the helper's JSON and the evidence decision remain unchanged.
    """

    started = time.monotonic()
    module_count = _source_record_identity_external_module_count(audit_payload)
    scope = (
        f"{module_count} external module artifact(s)"
        if module_count
        else "the saved external artifact closure"
    )
    print(
        "audit-evidence: strict source-record identity revalidation for "
        f"{folder.name} started ({scope}; timeout "
        f"{SOURCE_RECORD_IDENTITY_HELPER_TIMEOUT_SECONDS}s)",
        file=sys.stderr,
        flush=True,
    )
    stopped = threading.Event()

    def heartbeat() -> None:
        interval = max(SOURCE_RECORD_IDENTITY_PROGRESS_HEARTBEAT_SECONDS, 0.1)
        while not stopped.wait(interval):
            print(
                "audit-evidence: strict source-record identity revalidation for "
                f"{folder.name} still running "
                f"({time.monotonic() - started:.0f}s elapsed; {scope})",
                file=sys.stderr,
                flush=True,
            )

    worker = threading.Thread(
        target=heartbeat,
        name="audit-evidence-identity-progress",
        daemon=True,
    )
    worker.start()
    try:
        yield
    finally:
        stopped.set()
        worker.join(timeout=max(SOURCE_RECORD_IDENTITY_PROGRESS_HEARTBEAT_SECONDS, 0.1) + 1)
        print(
            "audit-evidence: strict source-record identity revalidation for "
            f"{folder.name} finished ({time.monotonic() - started:.1f}s elapsed)",
            file=sys.stderr,
            flush=True,
        )


def _source_record_fingerprint_matches_current(
    stored: object,
    current: object,
    *,
    semantic_reuse: object | None = None,
    paper: str = "",
) -> bool:
    """Match semantic raw inputs under the current registered verifier.

    Exact equality is always the ordinary path. A differing forensic producer
    or container hash can be accepted only after the formalization engine is
    clean, committed, and registered and the current verifier has reproduced
    the canonical receipt-bound semantics. This is deliberately shared in
    meaning with the raw producer's aggregate-cache check.
    """

    if (
        isinstance(stored, Mapping)
        and isinstance(current, Mapping)
        and dict(stored) == dict(current)
    ):
        return True
    if not (
        isinstance(stored, Mapping)
        and isinstance(current, Mapping)
        and stored.get("schema") == 10
        and current.get("schema") == 10
        and "raw_producer_code_identity_schema" in stored
        and "raw_producer_code_identities" in stored
        and "raw_producer_code_identity_schema" in current
        and "raw_producer_code_identities" in current
    ):
        return False
    exact_nonproducer = (
        fingerprint_without_raw_producer_provenance(stored)
        == fingerprint_without_raw_producer_provenance(current)
    )
    semantic_noncontainer = (
        isinstance(semantic_reuse, Mapping)
        and semantic_reuse.get("schema") == 1
        and semantic_reuse.get("policy") == SOURCE_RECORD_SEMANTIC_REUSE_POLICY
        and semantic_reuse.get("paper") == paper
        and semantic_reuse.get("current") is True
        and isinstance(semantic_reuse.get("reviewed_declaration_count"), int)
        and int(semantic_reuse.get("reviewed_declaration_count")) > 0
        and SHA256_RE.fullmatch(
            str(semantic_reuse.get("semantic_identity_sha256") or "")
        )
        and semantic_fingerprint_matches(stored, current)
    )
    if not (exact_nonproducer or semantic_noncontainer):
        return False
    try:
        validate_runtime_engine_registration(ROOT)
    except EngineRevisionError:
        return False
    return True


def _source_record_open_nonresult_fingerprint_rebind_matches(
    stored: object,
    current: object,
    semantic_contract_revalidation: object,
) -> bool:
    """Accept only the exact derived-map digest repair for declared open rows.

    The authenticated replay binds the unchanged raw bytes and statement-map
    bytes, then proves that an old producer's sole route error came from a
    fully structured source-declared open nonresult.  The routing-policy fix
    changes the map's *derived* semantic digest and producer provenance, but no
    paper/source/Lean input.  Remove exactly those two forensic coordinates;
    every other schema-10 fingerprint component must remain byte-identical.
    """

    projection = _trusted_semantic_contract_revalidation_projection(
        semantic_contract_revalidation
    )
    if projection is None or not any(
        str(error).startswith(
            "selected source-coverage item has no explicit direct/Spec Lean route: "
        )
        for error in projection.suppressed_source_contract_association_errors
    ):
        return False
    stored_projection = fingerprint_without_raw_producer_provenance(stored)
    current_projection = fingerprint_without_raw_producer_provenance(current)
    if not isinstance(stored_projection, dict) or not isinstance(
        current_projection, dict
    ):
        return False
    stored_semantic_map = str(
        stored_projection.pop("paper_statement_map_semantic_sha256", "") or ""
    ).strip().lower()
    current_semantic_map = str(
        current_projection.pop("paper_statement_map_semantic_sha256", "") or ""
    ).strip().lower()
    if (
        not SHA256_RE.fullmatch(stored_semantic_map)
        or not SHA256_RE.fullmatch(current_semantic_map)
        or stored_semantic_map == current_semantic_map
        or stored_projection != current_projection
    ):
        return False
    try:
        validate_runtime_engine_registration(ROOT)
    except EngineRevisionError:
        return False
    return True


def _source_proof_fidelity_semantically_unchanged(
    recorded: object,
    current: object,
) -> bool:
    """Return true only for an exact substantive schema-2 ledger match."""

    recorded_projection = source_proof_fidelity_semantic_projection(recorded)
    current_projection = source_proof_fidelity_semantic_projection(current)
    return (
        recorded_projection is not None
        and current_projection is not None
        and recorded_projection == current_projection
    )


def _source_record_typed_route_fingerprint_rebind_matches(
    stored: object,
    current: object,
    semantic_contract_revalidation: object,
    *,
    raw_status: str = "",
    current_status: str = "",
    source_proof_fidelity_semantically_unchanged: bool = False,
) -> bool:
    """Rebind map/status coordinates through the current typed obligation graph.

    This is not a version-to-version compatibility rule.  The authenticated
    projection has reconstructed the complete current schema-2 route graph from
    exact source anchors, semantic-prerequisite ledgers, explicit result proof
    endpoints, and the current status proof-pair map.  Consequently the old
    map/status hashes are forensic container coordinates; every source,
    paper-interface, Lean dependency, and toolchain identity must remain
    exactly equal.  A fidelity-ledger hash may also rebind when the raw receipt
    embeds a schema-2 ledger whose complete substantive projection is exactly
    the current ledger; controlled ``defect_kind`` spelling is not semantic
    evidence.
    """

    projection = _trusted_semantic_contract_revalidation_projection(
        semantic_contract_revalidation
    )
    if projection is None or not SHA256_RE.fullmatch(
        str(getattr(projection, "typed_route_reconciliation_sha256", "") or "")
    ):
        return False
    stored_projection = fingerprint_without_raw_producer_provenance(stored)
    current_projection = fingerprint_without_raw_producer_provenance(current)
    if not isinstance(stored_projection, dict) or not isinstance(
        current_projection, dict
    ):
        return False
    removed: dict[str, tuple[str, str]] = {}
    for field in (
        "paper_statement_map_semantic_sha256",
        "relevant_status_sha256",
    ):
        stored_value = str(stored_projection.pop(field, "") or "").strip().lower()
        current_value = str(current_projection.pop(field, "") or "").strip().lower()
        if not SHA256_RE.fullmatch(stored_value) or not SHA256_RE.fullmatch(
            current_value
        ):
            return False
        removed[field] = (stored_value, current_value)
    if source_proof_fidelity_semantically_unchanged:
        field = "source_proof_fidelity_sha256"
        stored_value = str(stored_projection.pop(field, "") or "").strip().lower()
        current_value = str(current_projection.pop(field, "") or "").strip().lower()
        if not SHA256_RE.fullmatch(stored_value) or not SHA256_RE.fullmatch(
            current_value
        ):
            return False
        removed[field] = (stored_value, current_value)
    map_changed = (
        removed["paper_statement_map_semantic_sha256"][0]
        != removed["paper_statement_map_semantic_sha256"][1]
    )
    status_changed = (
        removed["relevant_status_sha256"][0]
        != removed["relevant_status_sha256"][1]
    )
    fidelity_changed = (
        "source_proof_fidelity_sha256" in removed
        and removed["source_proof_fidelity_sha256"][0]
        != removed["source_proof_fidelity_sha256"][1]
    )
    if stored_projection != current_projection or not (
        map_changed or status_changed or fidelity_changed
    ):
        return False
    if not map_changed and status_changed:
        # A same-status metadata edit (for example, adding the current review
        # protocol configuration) cannot change the raw source scan surface.
        # Accept that coordinate through the complete current typed graph.  An
        # actual status promotion remains on its separate fail-closed route.
        normalized_raw_status = str(raw_status).strip().lower()
        normalized_current_status = str(current_status).strip().lower()
        if not (
            status_changed
            and normalized_raw_status in CLOSEOUT_STATUSES
            and normalized_raw_status == normalized_current_status
        ):
            return False
    try:
        validate_runtime_engine_registration(ROOT)
    except EngineRevisionError:
        return False
    return True


def _source_record_current_input_fingerprint_error(
    folder: Path,
    audit_payload: dict[str, Any],
    *,
    verify_watch_inputs: bool,
    semantic_contract_revalidation: object | None = None,
) -> str:
    """Compare a v10 raw audit with the current no-Lean generator identity.

    Importing the source-record helper here would cycle back through this
    evidence module.  Its ``--identity-only`` mode performs the same
    fingerprint computation without a Lean scan, cache lookup, or file write;
    this caller adds a cooperative read lock around that subprocess.  The
    stored options are replayed exactly, so an artifact generated with a
    nondefault recursion bound or ``--no-lean`` cannot be checked under a
    silently different identity.
    """

    stored = audit_payload.get("source_record_input_fingerprint")
    if not isinstance(stored, dict):
        return "source_record_input_fingerprint is missing or malformed"
    max_depth = stored.get("max_depth")
    no_lean = stored.get("no_lean")
    if not isinstance(max_depth, int) or max_depth < 0:
        return "source_record_input_fingerprint has malformed max_depth"
    if not isinstance(no_lean, bool):
        return "source_record_input_fingerprint has malformed no_lean"
    if no_lean:
        return (
            "source_record_input_fingerprint records --no-lean; evidence requires "
            "a full successful Lean scan"
        )
    helper = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
    if not helper.is_file():
        return "source-record identity helper is unavailable"
    command = [
        sys.executable,
        str(helper),
        "--root",
        str(ROOT),
        "--paper",
        folder.name,
        "--identity-only",
        "--max-depth",
        str(max_depth),
    ]
    # Current schema-10 fingerprints already carry the split coverage-protocol
    # identity. Older receipts need the helper's exact compatibility projections.
    if not schema_version_is_exact(stored.get("schema"), 10):
        command.append("--include-legacy-fingerprint")
    if no_lean:
        command.append("--no-lean")
    try:
        with _source_record_identity_read_lock(ROOT):
            watch_before = (
                _source_record_identity_process_watch_digest(
                    folder, audit_payload=audit_payload
                )
                if verify_watch_inputs
                else ""
            )
            with _source_record_identity_progress(folder, audit_payload):
                proc = subprocess.run(
                    command,
                    cwd=ROOT,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    check=False,
                    timeout=SOURCE_RECORD_IDENTITY_HELPER_TIMEOUT_SECONDS,
                )
            if verify_watch_inputs:
                watch_after = _source_record_identity_process_watch_digest(
                    folder, audit_payload=audit_payload
                )
                if watch_after != watch_before:
                    return "source-record identity inputs changed while the helper was running"
    except SourceRecordIdentityRevalidationBusy as exc:
        return "source-record identity revalidation deferred: " + str(exc)
    except subprocess.TimeoutExpired:
        return (
            "source-record identity helper timed out after "
            f"{SOURCE_RECORD_IDENTITY_HELPER_TIMEOUT_SECONDS}s during strict "
            "external-artifact verification; no evidence result was accepted. "
            "Wait for concurrent Lake/source-record work to finish, then rerun "
            "this evidence gate once"
        )
    except OSError as exc:
        return f"source-record identity helper could not run: {exc}"
    if proc.returncode != 0:
        detail = " ".join(proc.stderr.split())[-500:]
        return (
            "source-record identity helper failed"
            + (": " + detail if detail else "")
        )
    try:
        current_payload = json.loads(proc.stdout)
    except json.JSONDecodeError:
        return "source-record identity helper did not emit a JSON object"
    if not isinstance(current_payload, dict):
        return "source-record identity helper did not emit a JSON object"
    if current_payload.get("paper") != folder.name:
        return "source-record identity helper returned a paper mismatch"
    current = current_payload.get("source_record_input_fingerprint")
    if not isinstance(current, dict):
        return "source-record identity helper returned no input fingerprint"
    current_map = str(current_payload.get("paper_statement_map_sha256") or "").strip()
    recorded_map = str(audit_payload.get("paper_statement_map_sha256") or "").strip()
    fingerprint_matches = _source_record_fingerprint_matches_current(
        stored,
        current,
        semantic_reuse=current_payload.get("semantic_receipt_reuse"),
        paper=folder.name,
    )
    typed_route_fingerprint_rebound = (
        not fingerprint_matches
        and _source_record_typed_route_fingerprint_rebind_matches(
            stored,
            current,
            semantic_contract_revalidation,
            raw_status=str(
                (
                    audit_payload.get("precloseout_exact_contract_projection")
                    or {}
                ).get("status")
                or ""
            ),
            current_status=str(
                (load_json(folder / "status.json") or {}).get("status") or ""
            ),
            source_proof_fidelity_semantically_unchanged=(
                _source_proof_fidelity_semantically_unchanged(
                    audit_payload.get("source_proof_fidelity"),
                    load_json(folder / "audit" / "source_proof_fidelity.json"),
                )
            ),
        )
    )
    if typed_route_fingerprint_rebound:
        fingerprint_matches = True
    if (
        not fingerprint_matches
        and current_map == recorded_map
        and _source_record_open_nonresult_fingerprint_rebind_matches(
            stored,
            current,
            semantic_contract_revalidation,
        )
    ):
        fingerprint_matches = True
    legacy_v9 = current_payload.get("legacy_v9_source_record_input_fingerprint")
    legacy_v9_fingerprint_matches = (
        schema_version_is_exact(current.get("schema"), 10)
        and schema_version_is_exact(stored.get("schema"), 9)
        and isinstance(legacy_v9, dict)
        and schema_version_is_exact(legacy_v9.get("schema"), 9)
        and legacy_v9 == stored
    )
    legacy_v7 = current_payload.get("legacy_v7_source_record_input_fingerprint")
    # Older identity-only helpers emitted a v7 current fingerprint directly.
    # Retain that narrow compatibility for pre-projection test/receipt paths;
    # a schema-8 current identity without the explicit compatibility field
    # never gains legacy acceptance by guesswork.
    if not isinstance(legacy_v7, dict) and schema_version_is_exact(current.get("schema"), 7):
        legacy_v7 = current
    legacy_v7_is_current = isinstance(
        legacy_v7, dict
    ) and source_record_legacy_v7_fingerprint_is_current(legacy_v7, current)
    legacy_v7_fingerprint_matches = legacy_v7_is_current and legacy_v7 == stored
    legacy_v6_fingerprint_matches = legacy_v7_is_current and source_record_legacy_v6_fingerprint_matches_current(
        stored,
        legacy_v7,
        recorded_map_sha256=recorded_map,
        current_map_sha256=current_map,
    )
    if not (
        fingerprint_matches
        or legacy_v9_fingerprint_matches
        or legacy_v7_fingerprint_matches
        or legacy_v6_fingerprint_matches
    ):
        return (
            "source_record_input_fingerprint is stale for current source or "
            "audit-engine inputs"
        )
    matched_fingerprint = legacy_v9 if legacy_v9_fingerprint_matches else current
    current_semantic_map = str(
        matched_fingerprint.get("paper_statement_map_semantic_sha256") or ""
    ).strip().lower()
    recorded_semantic_map = str(
        stored.get("paper_statement_map_semantic_sha256") or ""
    ).strip().lower()
    if current_map != recorded_map and not typed_route_fingerprint_rebound and not (
        SHA256_RE.fullmatch(current_semantic_map)
        and current_semantic_map == recorded_semantic_map
    ):
        return "source-record identity helper disagrees with paper_statement_map_sha256"
    return ""


def source_record_current_input_fingerprint_error(
    folder: Path,
    audit_payload: dict[str, Any],
    *,
    semantic_contract_revalidation: object | None = None,
) -> str:
    """Validate current generator identity with a standalone TOCTOU watch."""

    return _source_record_current_input_fingerprint_error(
        folder,
        audit_payload,
        verify_watch_inputs=True,
        semantic_contract_revalidation=semantic_contract_revalidation,
    )


def _source_record_audit_identity_error(
    audit_payload: dict[str, Any],
    *,
    expected_paper_statement_map_sha256: str | None = None,
    folder: Path | None = None,
    prevalidated_current_input_fingerprint_error: str | None = None,
    semantic_contract_revalidation: Any | None = None,
    prevalidated_semantic_contract_revalidation_error: str | None = None,
    semantic_reuse_authority: CurrentSemanticReuseAuthority | None = None,
) -> str:
    """Return a freshness error for a saved source-record audit, if any.

    The generator's aggregate digest and source-map byte pin are both part of
    the semantic review identity.  Do not treat two absent strings as a
    matching digest, and require the map pin for v10 artifacts even when no
    individual judgment happens to carry a reusable item digest.
    """

    audit_digest = str(audit_payload.get("source_record_audit_sha256") or "").strip()
    if not audit_digest:
        return "source_record_audit_sha256 is missing or blank"

    # Fail cheaply on an unmistakably stale statement-map pin.  A receipt that
    # did not record the semantic map projection has no basis for classifying
    # container drift as administrative, so do not launch the heavier semantic
    # replay merely to discover that absence through unrelated missing fixture
    # or checkout files.  A typed semantic pin or authenticated current
    # semantic authority still proceeds to the exact checks below.
    recorded_map = str(
        audit_payload.get("paper_statement_map_sha256") or ""
    ).strip().lower()
    expected_map = str(expected_paper_statement_map_sha256 or "").strip().lower()
    stored_fingerprint = audit_payload.get("source_record_input_fingerprint")
    recorded_semantic_map = (
        str(
            stored_fingerprint.get("paper_statement_map_semantic_sha256") or ""
        ).strip().lower()
        if isinstance(stored_fingerprint, Mapping)
        else ""
    )
    if (
        SHA256_RE.fullmatch(expected_map)
        and SHA256_RE.fullmatch(recorded_map)
        and recorded_map != expected_map
        and not SHA256_RE.fullmatch(recorded_semantic_map)
        and not isinstance(semantic_reuse_authority, CurrentSemanticReuseAuthority)
    ):
        return "paper_statement_map_sha256 is stale for the current paper_statement_map.json"

    current_source_record_surface = (
        str(audit_payload.get("source_record_policy_version") or "").strip()
        == CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
        or str(audit_payload.get("prompt_version") or "").strip()
        == CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
    )
    projection = _trusted_semantic_contract_revalidation_projection(
        semantic_contract_revalidation
    )
    if current_source_record_surface:
        integrity_error = source_record_audit_receipt_error(audit_payload)
        if integrity_error:
            return integrity_error
        # Reject incomplete generator output before launching any semantic
        # replay.  This is strictly an ordering optimization: a current audit
        # must pass both checks, while an explicit ``--no-lean`` diagnostic or
        # structurally incomplete carrier now fails cheaply and directly.
        scan_error = source_record_raw_scan_completeness_error(audit_payload)
        if scan_error:
            return scan_error
        correction_error = prevalidated_semantic_contract_revalidation_error
        if correction_error is None and projection is None and folder is not None:
            projection, correction_error = (
                source_record_semantic_contract_revalidation_context(
                    folder, audit_payload
                )
            )
        if correction_error:
            return "semantic-contract revalidation is invalid: " + correction_error
        raw_semantic_error = source_record_effective_semantic_surface_error(
            audit_payload,
            semantic_contract_revalidation=projection,
        )
        if raw_semantic_error:
            return raw_semantic_error
        raw_item_error = source_record_raw_reusable_item_metadata_error(audit_payload)
        if raw_item_error:
            return raw_item_error
        if folder is not None:
            fingerprint_error = prevalidated_current_input_fingerprint_error
            if fingerprint_error is None:
                fingerprint_error = source_record_current_input_fingerprint_error(
                    folder,
                    audit_payload,
                    semantic_contract_revalidation=projection,
                )
            if fingerprint_error:
                return fingerprint_error
    requires_map_pin = (
        "paper_statement_map_sha256" in audit_payload
        or current_source_record_surface
    )
    if not requires_map_pin or expected_paper_statement_map_sha256 is None:
        return ""

    expected = expected_paper_statement_map_sha256.strip().lower()
    recorded = str(audit_payload.get("paper_statement_map_sha256") or "").strip().lower()
    if not SHA256_RE.fullmatch(expected):
        return "current paper_statement_map.json is missing or unreadable"
    if not SHA256_RE.fullmatch(recorded):
        return "paper_statement_map_sha256 is missing or malformed"
    if recorded != expected:
        if isinstance(semantic_reuse_authority, CurrentSemanticReuseAuthority):
            # Declaration-semantic authority deliberately does not own the
            # statement map.  The current transaction separately validates
            # source coverage, exact source-to-Spec rows, atom mappings,
            # correspondence receipts, and Spec/proof routes from the present
            # map.  Requiring the old raw map-container pin here would make a
            # machine-only correspondence refresh invalidate an unchanged Lean
            # semantic pass; accepting this narrow authority does not grant any
            # map, coverage, source, or realization credit by itself.
            return ""
        if (
            projection is not None
            and SHA256_RE.fullmatch(
                str(
                    getattr(
                        projection,
                        "typed_route_reconciliation_sha256",
                        "",
                    )
                    or ""
                )
            )
        ):
            return ""
        stored_fingerprint = audit_payload.get("source_record_input_fingerprint")
        recorded_semantic = (
            str(
                stored_fingerprint.get("paper_statement_map_semantic_sha256")
                or ""
            ).strip().lower()
            if isinstance(stored_fingerprint, Mapping)
            else ""
        )
        current_semantic = (
            current_paper_statement_map_semantic_sha256(folder)
            if folder is not None
            else ""
        )
        if (
            SHA256_RE.fullmatch(recorded_semantic)
            and recorded_semantic == current_semantic
        ):
            return ""
        return "paper_statement_map_sha256 is stale for the current paper_statement_map.json"
    return ""


def source_record_audit_identity_error(
    audit_payload: dict[str, Any],
    *,
    expected_paper_statement_map_sha256: str | None = None,
    folder: Path | None = None,
    semantic_contract_revalidation: Any | None = None,
    prevalidated_semantic_contract_revalidation_error: str | None = None,
) -> str:
    """Validate a raw receipt without accepting caller-supplied authorization."""

    return _source_record_audit_identity_error(
        audit_payload,
        expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
        folder=folder,
        semantic_contract_revalidation=semantic_contract_revalidation,
        prevalidated_semantic_contract_revalidation_error=(
            prevalidated_semantic_contract_revalidation_error
        ),
    )


def source_record_raw_semantic_surface_error(audit_payload: dict[str, Any]) -> str:
    """Reject generated route/configuration errors before evidence gets credit.

    A raw v10 audit is allowed to *report* an unresolved semantic-model or
    source-contract routing error.  It is not allowed to support an evidence
    gate while that error remains.  This is structural generator output, not a
    judgement about a theorem or the spelling of a declaration.
    """

    target_route_error = source_record_target_route_error(audit_payload)
    if target_route_error:
        return target_route_error
    error_fields = (
        "semantic_model_review_configuration_errors",
        "source_contract_association_errors",
        "source_coverage_route_errors",
        "elaborated_review_signature_errors",
        "elaborated_result_input_path_errors",
        "conclusion_dependency_input_atom_errors",
        "recursive_field_proposition_sort_errors",
        "constructor_field_slot_reconciliation_errors",
        "type_witness_payload_safety_errors",
    )
    for field in error_fields:
        raw_errors = audit_payload.get(field)
        if raw_errors in (None, [], {}, ""):
            continue
        if isinstance(raw_errors, list):
            rendered = "; ".join(str(error) for error in raw_errors[:3])
        else:
            rendered = str(raw_errors)
        return f"generated `{field}` is nonempty: {rendered}"
    return ""


def source_record_effective_semantic_surface_error(
    audit_payload: Mapping[str, Any],
    *,
    semantic_contract_revalidation: Any | None = None,
) -> str:
    """Check a raw semantic surface after one authenticated structural replay.

    Keep ``source_record_raw_semantic_surface_error`` unchanged for the raw
    producer.  Only evidence consumers may replace the two representation-only
    fields through an explicitly validated, byte-pinned projection.
    """

    target_route_error = source_record_target_route_error(audit_payload)
    if target_route_error:
        return target_route_error
    effective_errors = source_record_effective_semantic_errors(
        audit_payload,
        semantic_contract_revalidation=semantic_contract_revalidation,
    )
    error_fields = (
        "semantic_model_review_configuration_errors",
        "source_contract_association_errors",
        "source_coverage_route_errors",
        "elaborated_review_signature_errors",
        "elaborated_result_input_path_errors",
        "conclusion_dependency_input_atom_errors",
        "recursive_field_proposition_sort_errors",
        "constructor_field_slot_reconciliation_errors",
        "type_witness_payload_safety_errors",
    )
    for field in error_fields:
        raw_errors = effective_errors.get(field, audit_payload.get(field))
        if raw_errors in (None, [], {}, ""):
            continue
        if isinstance(raw_errors, list):
            rendered = "; ".join(str(error) for error in raw_errors[:3])
        else:
            rendered = str(raw_errors)
        return f"generated `{field}` is nonempty: {rendered}"
    return ""


def source_record_effective_semantic_errors(
    audit_payload: Mapping[str, Any],
    *,
    semantic_contract_revalidation: Any | None = None,
) -> Mapping[str, list[str]]:
    """Return the two replayable raw error fields after authentication."""

    projection = _trusted_semantic_contract_revalidation_projection(
        semantic_contract_revalidation
    )
    replay = _semantic_contract_revalidation_module()
    return replay.effective_source_record_semantic_errors(
        audit_payload, projection
    )


def source_record_raw_scan_completeness_error(audit_payload: dict[str, Any]) -> str:
    """Reject v10 audit records that did not complete their generator checks.

    A receipt binds what was serialized; it cannot by itself show that the
    generator actually ran the mandatory current-source Lean pass or finished
    its structural scans.  This validation is intentionally about generated
    evidence states (row coverage, recursion, constructor typing, and
    source-premise consistency), not declaration spelling or function names.
    """

    fingerprint = audit_payload.get("source_record_input_fingerprint")
    if not isinstance(fingerprint, dict):
        return "source_record_input_fingerprint is missing or malformed"
    if fingerprint.get("no_lean") is not False:
        return (
            "source_record_input_fingerprint must record no_lean=false for "
            "evidence-bearing audits"
        )

    missing_rows = audit_payload.get("missing_configured_review_rows")
    if not isinstance(missing_rows, list):
        return "generated `missing_configured_review_rows` is not a list"
    if any(not isinstance(row, str) or not row.strip() for row in missing_rows):
        return "generated `missing_configured_review_rows` is malformed"
    if missing_rows:
        return "generated `missing_configured_review_rows` is nonempty"

    configured_rows = audit_payload.get("configured_review_rows")
    if not isinstance(configured_rows, list):
        return "generated `configured_review_rows` is not a list"
    configured_rows_count = audit_payload.get("configured_review_rows_count")
    if type(configured_rows_count) is not int or configured_rows_count != len(
        configured_rows
    ):
        return "generated configured-review-row count does not match its row metadata"
    configured_row_count = audit_payload.get("configured_review_row_count")
    if type(configured_row_count) is not int or configured_row_count < len(
        configured_rows
    ):
        return "generated configured review-surface count is malformed"

    recursion_failures = audit_payload.get("recursion_failures")
    if not isinstance(recursion_failures, list):
        return "generated `recursion_failures` is not a list"
    recursion_failure_count = audit_payload.get("recursion_failure_count")
    if type(recursion_failure_count) is not int:
        return "generated `recursion_failure_count` is missing or malformed"
    if recursion_failure_count != len(recursion_failures):
        return "generated recursion failure count does not match its failure list"
    if recursion_failures:
        return "generated `recursion_failures` is nonempty"

    constructor_error = audit_payload.get("constructor_result_type_check_error")
    if not isinstance(constructor_error, str):
        return "generated `constructor_result_type_check_error` is malformed"
    if constructor_error.strip():
        return "generated `constructor_result_type_check_error` is nonempty"

    if not schema_version_is_exact(
        audit_payload.get("source_premise_consistency_schema"), 1
    ):
        return "generated source-premise consistency scan has an unsupported schema"
    premise_error = audit_payload.get("source_premise_consistency_error")
    if not isinstance(premise_error, str):
        return "generated `source_premise_consistency_error` is malformed"
    if premise_error.strip():
        return "generated `source_premise_consistency_error` is nonempty"
    premise_items = audit_payload.get("source_premise_consistency_items")
    if not isinstance(premise_items, list):
        return "generated `source_premise_consistency_items` is not a list"
    premise_item_count = audit_payload.get("source_premise_consistency_item_count")
    if type(premise_item_count) is not int or premise_item_count != len(premise_items):
        return "generated source-premise consistency item count is malformed"

    lean_check = audit_payload.get("lean_check")
    if not isinstance(lean_check, dict):
        return "generated `lean_check` is missing or malformed"
    if type(lean_check.get("returncode")) is not int or lean_check.get("returncode") != 0:
        return "generated `lean_check` did not complete successfully"
    requested_rows = lean_check.get("requested_checked_rows")
    checked_rows = lean_check.get("checked_rows")
    if not isinstance(requested_rows, list) or not isinstance(checked_rows, list):
        return "generated `lean_check` lacks checked-row coverage metadata"
    if requested_rows != checked_rows:
        return "generated `lean_check` did not check every selected review row"

    review_row_count = audit_payload.get("review_row_count")
    recursive_field_count = audit_payload.get("recursive_field_count")
    if type(review_row_count) is not int or type(recursive_field_count) is not int:
        return "generated review-row or recursive-field count is malformed"
    if review_row_count != len(configured_rows):
        return "generated review-row count does not match configured-row metadata"
    zero_scan = not requested_rows and not checked_rows
    if zero_scan:
        if lean_check.get("command") != "skipped Lean check: no source-record rows or fields":
            return "generated `lean_check` skipped rows without the zero-surface sentinel"
        if review_row_count != 0 or recursive_field_count != 0:
            return "generated `lean_check` skipped a nonempty review surface"
        fresh = audit_payload.get("fresh_source_elaboration")
        if not isinstance(fresh, dict) or fresh.get("mode") != "not_run_without_lean":
            return "generated zero-surface Lean check lacks its explicit skip record"
        return ""

    # A nonempty selected surface must have elaborated the current source in
    # the isolated overlay.  A successful ordinary Lake build is insufficient:
    # it could otherwise be served by an old compiled artifact.
    fresh = lean_check.get("fresh_source_elaboration")
    top_fresh = audit_payload.get("fresh_source_elaboration")
    if not isinstance(fresh, dict) or not isinstance(top_fresh, dict):
        return "generated `lean_check` lacks fresh current-source elaboration evidence"
    for field, expected in (
        ("mode", "isolated_temp_overlay"),
        ("returncode", 0),
    ):
        if fresh.get(field) != expected or top_fresh.get(field) != expected:
            return "generated fresh current-source elaboration did not complete successfully"
    interface_source = audit_payload.get("review_interface_source")
    if not isinstance(interface_source, dict):
        return "generated review-interface source identity is missing or malformed"
    source_file = str(interface_source.get("path") or "").strip()
    source_sha256 = str(interface_source.get("sha256") or "").strip().lower()
    if not source_file or not SHA256_RE.fullmatch(source_sha256):
        return "generated review-interface source identity is incomplete"
    for elaboration in (fresh, top_fresh):
        if (
            str(elaboration.get("source_file") or "").strip() != source_file
            or str(elaboration.get("source_sha256") or "").strip().lower()
            != source_sha256
        ):
            return "generated fresh elaboration does not match the reviewed source identity"
    return ""


def source_record_raw_reusable_item_metadata_error(
    audit_payload: dict[str, Any],
) -> str:
    """Validate all generated v10 item receipts that claim narrow reuse."""

    return _raw_item_metadata_error(
        audit_payload,
        expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
    )


def semantic_model_judgment_completeness_errors(
    item: dict[str, Any], judgment: dict[str, Any]
) -> list[str]:
    """Return missing semantic-model evidence before freshness is credited.

    ``audit_repository.py`` supplies detailed diagnostics for these judgments.
    The fast evidence gate must nevertheless reject a sidecar that merely
    attaches a current digest to an unrelated classification: otherwise a
    lightweight CI path can call an incomplete semantic-model review current.
    """

    errors: list[str] = []
    if (
        str(judgment.get("classification") or "").strip()
        != SEMANTIC_MODEL_REVIEW_CLASSIFICATION
    ):
        return ["classification must be `semantic_model_review`"]
    # Structural source-process patterns remain diagnostic outside an explicit
    # source-pinned source_model_derivation dimension. That opt-in dimension
    # carries its generated basis into the shared subanalysis validator, which
    # fail-closes a caller-supplied construction package rather than allowing a
    # declaration name or free-text derivation narrative to decide closeout.
    responses = judgment.get("semantic_model_dimensions")
    dimensions = item.get("dimensions")
    if (
        not isinstance(responses, dict)
        or not isinstance(dimensions, list)
        or not dimensions
    ):
        return ["semantic-model response needs a nonempty dimensions ledger"]
    for raw_dimension in dimensions:
        if not isinstance(raw_dimension, dict):
            errors.append("generated semantic-model dimension is malformed")
            continue
        dimension = str(raw_dimension.get("id") or "").strip()
        if not dimension:
            errors.append("generated semantic-model dimension has no id")
            continue
        response = responses.get(dimension)
        if not isinstance(response, dict):
            errors.append(f"`{dimension}` has no object-valued response")
            continue
        verdict = str(response.get("verdict") or "").strip()
        if verdict not in SEMANTIC_MODEL_REVIEW_VERDICTS:
            errors.append(
                f"`{dimension}.verdict` is not an accepted semantic verdict"
            )
        if not all(
            str(response.get(field) or "").strip()
            for field in ("source_locator", "semantic_comparison", "lean_evidence")
        ):
            errors.append(
                f"`{dimension}` needs source_locator, semantic_comparison, and "
                "lean_evidence"
            )
        if any(
            NAME_ONLY_REASON_RE.search(str(response.get(field) or ""))
            for field in ("semantic_comparison", "lean_evidence", "parameter_translation")
        ):
            errors.append(f"`{dimension}` has name-only semantic evidence")
        detected = bool(raw_dimension.get("detected_from_expanded_surface"))
        if detected and verdict == "not_applicable":
            errors.append(f"`{dimension}` is detected and cannot be not_applicable")
        if detected and raw_dimension.get(
            "requires_parameter_translation_when_detected"
        ) is True:
            if not str(response.get("parameter_translation") or "").strip():
                errors.append(f"`{dimension}` needs parameter_translation")
        errors.extend(
            f"`{dimension}`: {error}"
            for error in semantic_model_subanalysis_errors(
                raw_dimension,
                response,
                name_only=lambda value: bool(NAME_ONLY_REASON_RE.search(value)),
            )
        )
        if dimension in {
            "conditioning_and_calibration_semantics",
            "expectation_definedness",
            "null_cell_totalization_and_partition_scope",
        } and detected:
            basis = raw_dimension.get("expanded_shape_basis")
            if not isinstance(basis, list) or not any(
                isinstance(entry, str) and entry.strip() for entry in basis
            ):
                errors.append(f"`{dimension}` has no generated expanded-shape basis")
        requires_checked_bridge = bool(
            raw_dimension.get("requires_checked_bridge_when_detected")
        ) or dimension in SEMANTIC_MODEL_BRIDGE_DIMENSIONS
        if detected and requires_checked_bridge:
            if not str(response.get("lean_bridge") or "").strip():
                errors.append(f"`{dimension}` needs a checked Lean bridge")
    return errors


def semantic_model_judgment_is_complete(
    item: dict[str, Any], judgment: dict[str, Any]
) -> bool:
    """Check the minimum semantic-model payload before freshness is credited."""

    return not semantic_model_judgment_completeness_errors(item, judgment)


def current_open_semantic_model_dimensions(
    audit_payload: dict[str, Any], current: dict[str, dict[str, Any]]
) -> list[str]:
    """Return current semantic-model dimensions that explicitly remain open."""

    open_dimensions: list[str] = []
    for item in audit_payload.get("semantic_model_items") or []:
        if not isinstance(item, dict):
            continue
        key = str(item.get("judgment_key") or "").strip()
        judgment = current.get(key)
        if not key or not isinstance(judgment, dict):
            continue
        responses = judgment.get("semantic_model_dimensions")
        if not isinstance(responses, dict):
            continue
        for raw_dimension in item.get("dimensions") or []:
            if not isinstance(raw_dimension, dict):
                continue
            dimension = str(raw_dimension.get("id") or "").strip()
            response = responses.get(dimension)
            if not dimension or not isinstance(response, dict):
                continue
            if str(response.get("verdict") or "").strip() in {
                "mismatch_or_open",
                "documented_partial_boundary",
            }:
                open_dimensions.append(f"{key}.{dimension}")
    return sorted(set(open_dimensions))


def source_record_payload_is_non_evidence(payload: dict[str, Any]) -> bool:
    """Reject draft/candidate sidecars before they can satisfy an evidence gate."""

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
    if "candidate" in artifact_kind or "proposal" in artifact_kind:
        return True
    validator_type = str(payload.get("validator_type") or "").strip().lower()
    return "candidate" in validator_type or "proposal" in validator_type


def _authenticated_overlay_union_module() -> Any:
    """Load the one transport authority without creating an import cycle."""

    from scripts import source_record_authenticated_overlay_union as overlay_union
    return overlay_union


def _copy_loaded_source_record_overlay_item(
    value: Mapping[str, Any], updates: Mapping[str, Any] | None = None
) -> dict[str, Any]:
    """Keep an authenticated overlay token through in-memory normalization."""

    return _authenticated_overlay_union_module().copy_loader_authenticated_or_plain_current_item(
        value, updates
    )


def _is_loaded_source_record_overlay_item(value: object) -> bool:
    """Whether an in-memory response came from an authenticated overlay loader.

    This asks the loader-owned private capabilities, never a serialized JSON
    marker.  It is used only to establish that a canonical sidecar's omitted
    response slot is supplied by a separately replayed current overlay; it
    does not infer a semantic match from a source key, declaration, or name.
    """

    return bool(
        _authenticated_overlay_union_module().loader_authenticated_current_overlay_label(
            value
        )
    )


def _project_current_source_record_response_association_pins(
    audit_payload: Mapping[str, Any],
    current: Mapping[str, Mapping[str, Any]],
    *,
    statement_map: Mapping[str, Any] | None = None,
    configured_assumption_formalization_regularity_context: (
        ConfiguredAssumptionFormalizationRegularityContext | None
    ) = None,
) -> dict[str, dict[str, Any]]:
    """Normalize every admitted response from its exact current raw group.

    This is deliberately after each ordinary/overlay loader has authenticated
    its own receipt and after precedence has selected the response.  It binds
    the selected response to the current raw-member group without treating a
    serialized association field as evidence.  A malformed group or a
    conflicting pin drops that response rather than guessing from its key,
    declaration, or review text.
    """

    groups, group_errors = raw_source_record_obligation_groups(audit_payload)
    if group_errors:
        return {}
    projected_current: dict[str, dict[str, Any]] = {}
    for raw_key, value in current.items():
        key = str(raw_key).strip()
        if not key or not isinstance(value, Mapping):
            continue
        group = groups.get(key)
        raw_members = group.get("raw_members") if isinstance(group, Mapping) else None
        projected, error = project_source_record_response_association_pins(
            raw_members,
            value,
            judgment_key=key,
            statement_map=statement_map,
            configured_assumption_formalization_regularity_context=(
                configured_assumption_formalization_regularity_context
            ),
        )
        if error or projected is None:
            continue
        projected_current[key] = _copy_loaded_source_record_overlay_item(
            value, projected
        )
    return projected_current


def _current_source_record_judgment_items_from_payload(
    audit_payload: dict[str, Any],
    match_payload: dict[str, Any],
    *,
    expected_paper_statement_map_sha256: str | None = None,
    folder: Path | None = None,
    authenticated_overlay_lane: object | None = None,
    prevalidated_source_record_identity_error: object = _UNSET,
) -> dict[str, dict[str, Any]]:
    identity_error = (
        source_record_audit_identity_error(
            audit_payload,
            expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
            folder=folder,
        )
        if prevalidated_source_record_identity_error is _UNSET
        else str(prevalidated_source_record_identity_error)
    )
    if identity_error:
        return {}
    if source_record_payload_is_non_evidence(match_payload):
        return {}
    ordinary_protocol_current = formalization_judgment_review_protocol_is_current(
        audit_payload, match_payload
    )
    required_prompt = str(audit_payload.get("prompt_version") or "").strip()
    required_digest = str(audit_payload.get("source_record_audit_sha256") or "").strip()
    required_item_digests = source_record_required_item_digests(audit_payload)
    unique_key_by_item_digest = source_record_unique_item_digest_keys(audit_payload)
    payload_prompt = str(match_payload.get("prompt_version") or "").strip()
    payload_digest = str(match_payload.get("source_record_audit_sha256") or "").strip()
    payload_validator = (
        match_payload.get("validator")
        or match_payload.get("model")
        or match_payload.get("judge")
    )
    payload_timestamp = (
        match_payload.get("validated_at")
        or match_payload.get("timestamp")
        or match_payload.get("generated_at")
    )
    raw_items = match_payload.get("items") or match_payload.get("field_judgments") or {}
    if not isinstance(raw_items, dict):
        return {}
    overlay_union = None
    if authenticated_overlay_lane is not None:
        overlay_union = _authenticated_overlay_union_module()
        if (
            not isinstance(
                authenticated_overlay_lane,
                overlay_union.AuthenticatedCurrentOverlayLane,
            )
            or raw_items is not authenticated_overlay_lane.items
        ):
            return {}
    semantic_model_items = {
        str(item.get("judgment_key") or "").strip(): item
        for item in audit_payload.get("semantic_model_items") or []
        if isinstance(item, dict) and str(item.get("judgment_key") or "").strip()
    }
    semantic_model_expected = {
        str(key).strip()
        for key in audit_payload.get("expected_semantic_model_judgment_keys") or []
        if str(key).strip()
    }
    current: dict[str, dict[str, Any]] = {}
    for key, value in raw_items.items():
        if not isinstance(value, dict):
            continue
        if archived_source_record_transport_item_field(value):
            continue
        if source_record_payload_is_non_evidence(value):
            continue
        loaded_overlay_entry = bool(
            authenticated_overlay_lane is not None
            and overlay_union is not None
            and overlay_union.authenticated_current_overlay_item(
                authenticated_overlay_lane, value
            )
        )
        if authenticated_overlay_lane is not None and not loaded_overlay_entry:
            continue
        if (
            authenticated_overlay_lane is None
            and serialized_source_record_overlay_labels(value)
        ):
            continue
        if not loaded_overlay_entry and not ordinary_protocol_current:
            continue
        classification = str(
            value.get("classification")
            or value.get("judgment")
            or value.get("verdict")
            or value.get("status")
            or ""
        ).strip()
        item_prompt = str(value.get("prompt_version") or payload_prompt).strip()
        item_digest = str(value.get("source_record_audit_sha256") or payload_digest).strip()
        item_semantic_digest = str(value.get("source_record_item_sha256") or "").strip()
        item_semantic_digest_schema = value.get(
            "source_record_item_digest_schema"
        )
        raw_key = str(key)
        resolved_key = raw_key
        required_item_digest = required_item_digests.get(raw_key, "")
        # Item-level semantic reuse still needs an explicit aggregate audit
        # identity on the saved judgment. A matching item digest cannot turn a
        # blank audit field into evidence that this response was reviewed under
        # any generated source-record surface.
        if not item_digest and not loaded_overlay_entry:
            continue
        if loaded_overlay_entry:
            # Authenticated overlay loaders recompare an exact generated semantic
            # descriptor against the current raw audit.  They must not fall
            # back to aggregate freshness or a key/name remap.
            digest_current = True
        else:
            digest_current = source_record_item_judgment_current(
                aggregate_current=bool(required_digest and item_digest == required_digest),
                expected_item_digest=required_item_digest,
                judgment_item_digest=item_semantic_digest,
                judgment_item_digest_schema=item_semantic_digest_schema,
            )
        # A renamed storage key may be recovered only from a globally unique
        # schema-5 semantic receipt.  A digest shared by multiple current keys
        # remains adequate for direct same-key reuse above, but cannot select a
        # destination by a declaration/binder/source-map name heuristic.
        if not loaded_overlay_entry and not digest_current and not (
            required_digest and item_digest == required_digest
        ):
            candidate_key = unique_key_by_item_digest.get(item_semantic_digest)
            if candidate_key is not None:
                digest_current = source_record_item_judgment_current(
                    aggregate_current=False,
                    expected_item_digest=required_item_digests.get(candidate_key, ""),
                    judgment_item_digest=item_semantic_digest,
                    judgment_item_digest_schema=item_semantic_digest_schema,
                )
                if digest_current:
                    resolved_key = candidate_key
        validator = value.get("validator") or value.get("model") or value.get("judge") or payload_validator
        timestamp = (
            value.get("validated_at")
            or value.get("timestamp")
            or value.get("generated_at")
            or payload_timestamp
        )
        if (
            classification
            and validator
            and timestamp
            and item_prompt == required_prompt
            and digest_current
        ):
            semantic_item = semantic_model_items.get(resolved_key)
            if resolved_key in semantic_model_expected or semantic_item is not None:
                if semantic_item is None or not semantic_model_judgment_is_complete(
                    semantic_item, value
                ):
                    continue
            # Two stale aliases must not race to satisfy the same generated
            # item after a unique semantic-ID remap.
            if resolved_key in current:
                continue
            current[resolved_key] = _copy_loaded_source_record_overlay_item(value)
    return current


def _current_source_record_judgment_items(
    audit_payload: dict[str, Any],
    match_payload: dict[str, Any],
    *,
    expected_paper_statement_map_sha256: str | None = None,
    folder: Path | None = None,
    differential_overlay_path: Path | None = None,
    differential_current_raw_audit_path: Path | None = None,
    differential_current_raw_audit_provenance_path: Path | None = None,
    allow_archived_raw_identity: bool = False,
    prevalidated_source_record_identity_error: object = _UNSET,
    source_record_identity_context: object | None = None,
    statement_map_override: object = _UNSET,
    status_payload_override: object = _UNSET,
    configured_assumption_regularity_context_override: object = _UNSET,
) -> dict[str, dict[str, Any]]:
    """Load ordinary judgments plus authenticated narrow reuse overlays.

    Historical receipt validation may supply exact archived paths.  Normal
    callers leave both optional paths unset and retain the canonical-paper
    behavior.  ``allow_archived_raw_identity`` is restricted to replaying an
    immutable historical receipt before it is semantically compared to a new
    current receipt; it avoids incorrectly requiring that the historical
    source bytes still equal the live source.  The paths authenticate bytes
    only; they never select a match by declaration, binder, or judgment-key
    spelling.
    """

    if allow_archived_raw_identity and (
        differential_current_raw_audit_path is None
        or differential_current_raw_audit_provenance_path is None
    ):
        return {}
    if folder is not None and archived_source_record_transport_artifacts(folder):
        return {}
    identity_folder = None if allow_archived_raw_identity else folder
    effective_prevalidated_source_record_identity_error = (
        prevalidated_source_record_identity_error
    )
    if source_record_identity_context is not None:
        # This is not a caller-provided authorization bypass.  The opaque
        # capability was minted by the strict gate and is re-bound to live
        # canonical raw bytes, map bytes, and producer/source watch inputs
        # before every nested replay.  Archived raw paths never use it.
        if allow_archived_raw_identity or folder is None:
            return {}
        paper_for_identity = str(audit_payload.get("paper") or folder.name).strip()
        if not paper_for_identity or current_source_record_identity_context_error(
            source_record_identity_context,
            paper_dir=folder,
            paper=paper_for_identity,
            current_raw_audit=audit_payload,
            expected_paper_statement_map_sha256=(
                expected_paper_statement_map_sha256
            ),
        ):
            return {}
        effective_prevalidated_source_record_identity_error = ""

    if folder is None:
        ordinary = _current_source_record_judgment_items_from_payload(
            audit_payload,
            match_payload,
            expected_paper_statement_map_sha256=(
                expected_paper_statement_map_sha256
            ),
            folder=None,
            prevalidated_source_record_identity_error=(
                effective_prevalidated_source_record_identity_error
            ),
        )
        return _project_current_source_record_response_association_pins(
            audit_payload, ordinary
        )
    paper = str(audit_payload.get("paper") or folder.name).strip()
    if not paper:
        return ordinary
    consumed_overlay_labels = (
        "differential",
        "semantic_rebind",
    )
    present_overlay_labels = list(
        source_record_overlay_labels_with_artifacts(
            folder, lane_labels=consumed_overlay_labels
        )
    )
    if (
        differential_overlay_path is not None
        and differential_overlay_path.is_file()
        and "differential" not in present_overlay_labels
    ):
        present_overlay_labels.append("differential")
    identity_overlay_present = "semantic_rebind" in present_overlay_labels
    if (
        identity_overlay_present
        and source_record_identity_context is None
        and not allow_archived_raw_identity
    ):
        identity_error = (
            source_record_audit_identity_error(
                audit_payload,
                expected_paper_statement_map_sha256=(
                    expected_paper_statement_map_sha256
                ),
                folder=folder,
            )
            if effective_prevalidated_source_record_identity_error is _UNSET
            else str(effective_prevalidated_source_record_identity_error)
        )
        if identity_error:
            return {}
        source_record_identity_context = _issue_current_source_record_identity_context(
            folder,
            paper,
            audit_payload,
            source_record_identity_error="",
        )
        if source_record_identity_context is None:
            return {}
        effective_prevalidated_source_record_identity_error = ""

    ordinary = _current_source_record_judgment_items_from_payload(
        audit_payload,
        match_payload,
        expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
        folder=identity_folder,
        prevalidated_source_record_identity_error=(
            effective_prevalidated_source_record_identity_error
        ),
    )
    overlay_current: dict[str, dict[str, dict[str, Any]]] = {}
    overlay_union = _authenticated_overlay_union_module()
    if present_overlay_labels:
        try:
            lanes = overlay_union.load_authenticated_current_overlay_lanes(
                folder,
                paper,
                audit_payload,
                lane_labels=present_overlay_labels,
                differential_overlay_path=differential_overlay_path,
                differential_current_raw_audit_path=(
                    differential_current_raw_audit_path
                ),
                differential_current_raw_audit_provenance_path=(
                    differential_current_raw_audit_provenance_path
                ),
                source_record_identity_context=(
                    source_record_identity_context
                    if not allow_archived_raw_identity
                    else None
                ),
            )
        except overlay_union.SourceRecordAuthenticatedOverlayUnionError:
            return {}
        for lane in lanes:
            overlay_current[lane.label] = (
                _current_source_record_judgment_items_from_payload(
                    audit_payload,
                    {"schema": 1, "paper": paper, "items": lane.items},
                    expected_paper_statement_map_sha256=(
                        expected_paper_statement_map_sha256
                    ),
                    folder=identity_folder,
                    authenticated_overlay_lane=lane,
                    prevalidated_source_record_identity_error=(
                        effective_prevalidated_source_record_identity_error
                    ),
                )
            )
    # The differential loader binds an unchanged prior response to the current
    # semantic obligation. A genuinely current ordinary response is newer
    # evidence, however, and must win over every overlay lane on collision.
    current_raw_digest = str(audit_payload.get("source_record_audit_sha256") or "").strip()
    ordinary_with_current_receipt = {
        key: value
        for key, value in ordinary.items()
        if current_raw_digest
        and str(value.get("source_record_audit_sha256") or "").strip()
        == current_raw_digest
    }
    statement_map_payload = (
        load_json(folder / "audit" / "paper_statement_map.json")
        if statement_map_override is _UNSET
        else statement_map_override
    )
    statement_map = (
        statement_map_payload if isinstance(statement_map_payload, Mapping) else None
    )
    status_payload = (
        load_json(folder / "status.json")
        if status_payload_override is _UNSET
        else status_payload_override
    )
    if configured_assumption_regularity_context_override is _UNSET:
        regularity_context, _regularity_context_error = (
            load_configured_assumption_formalization_regularity_context(
                folder,
                audit_payload,
                status_payload=(
                    status_payload if isinstance(status_payload, Mapping) else None
                ),
            )
        )
    else:
        regularity_context = configured_assumption_regularity_context_override
    base_current = _project_current_source_record_response_association_pins(
        audit_payload,
        {
            **ordinary,
            **overlay_current.get("differential", {}),
            # A schema-2 rebind has byte-pinned immutable inputs, a live raw
            # identity check, and a complete name-independent descriptor. It
            # is therefore stronger than the legacy differential bridge, but
            # still loses to independently reviewed ordinary current evidence.
            **overlay_current.get("semantic_rebind", {}),
            **ordinary_with_current_receipt,
        },
        statement_map=statement_map,
        configured_assumption_formalization_regularity_context=regularity_context,
    )
    return base_current


def current_source_record_judgment_items(
    audit_payload: dict[str, Any],
    match_payload: dict[str, Any],
    *,
    expected_paper_statement_map_sha256: str | None = None,
    folder: Path | None = None,
    differential_overlay_path: Path | None = None,
    differential_current_raw_audit_path: Path | None = None,
    differential_current_raw_audit_provenance_path: Path | None = None,
    allow_archived_raw_identity: bool = False,
    source_record_identity_context: object | None = None,
) -> dict[str, dict[str, Any]]:
    """Materialize judgments under one current identity replay when possible.

    ``source_record_identity_context`` is an opaque, verifier-issued runtime
    capability, not a caller-supplied prevalidation result.  Forged, stale,
    cross-paper, or archived-path contexts are rejected by the private loader
    before any judgment receives credit.  Ordinary callers leave it unset and
    this function mints one fresh context for the whole current-lane replay.
    """

    context = source_record_identity_context
    if (
        context is None
        and not allow_archived_raw_identity
        and folder is not None
    ):
        paper = str(audit_payload.get("paper") or folder.name).strip()
        if paper:
            try:
                context = prepare_current_source_record_identity_context(
                    folder,
                    paper,
                    audit_payload,
                )
            except SourceRecordIdentityContextDeferred:
                # The legacy path would reject this raw audit as non-current
                # too.  Do not retry it here, because a busy gate is not an
                # absent optional overlay.
                return {}

    return _current_source_record_judgment_items(
        audit_payload,
        match_payload,
        expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
        folder=folder,
        differential_overlay_path=differential_overlay_path,
        differential_current_raw_audit_path=differential_current_raw_audit_path,
        differential_current_raw_audit_provenance_path=(
            differential_current_raw_audit_provenance_path
        ),
        allow_archived_raw_identity=allow_archived_raw_identity,
        source_record_identity_context=context,
    )


SOURCE_RECORD_MATCH_SIDECAR_BASENAME = "source_record_match_llm.json"
SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_FIELD = "manual_current_complement"
SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_SCHEMA = 1
SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_POLICY_VERSION = (
    "source-record-v10-manual-current-complement-v3"
)
SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_POLICY_VERSIONS = frozenset(
    {
        "source-record-v10-manual-current-complement-v1",
        "source-record-v10-manual-current-complement-v2",
        SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_POLICY_VERSION,
    }
)
SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_SCOPE = (
    "all_current_generated_groups_without_authenticated_overlay"
)


def canonical_source_record_match_sidecar_path(
    path: Path, paper_dir: Path
) -> bool:
    """Whether ``path`` is one of the two ordinary source-record sidecars.

    Historical snapshots and authenticated overlay artifacts intentionally use
    their own paths.  This guard applies only to the ordinary repository
    sidecar which consumers otherwise treat as the paper's current ledger.
    """

    try:
        resolved = path.resolve()
        root = paper_dir.resolve()
    except (OSError, RuntimeError):
        return False
    return resolved in {
        root / "audit" / SOURCE_RECORD_MATCH_SIDECAR_BASENAME,
        root / SOURCE_RECORD_MATCH_SIDECAR_BASENAME,
    }


def _canonical_source_record_sidecar_item_keys(
    payload: Mapping[str, Any],
) -> tuple[set[str] | None, str]:
    """Read the ordinary response ledger without treating its contents as proof.

    ``field_judgments`` remains a legacy storage spelling.  It is accepted
    only with the same precedence as the ordinary loader, so the coverage gate
    cannot validate a different key ledger than the consumer actually reads.
    """

    raw_items = payload.get("items")
    legacy_items = payload.get("field_judgments")
    if not isinstance(raw_items, Mapping) or (
        not raw_items and isinstance(legacy_items, Mapping)
    ):
        raw_items = legacy_items
    if not isinstance(raw_items, Mapping):
        return None, "canonical source-record sidecar has no object-valued items ledger"
    keys: set[str] = set()
    for raw_key in raw_items:
        key = str(raw_key or "").strip()
        if not key or key in keys:
            return None, "canonical source-record sidecar has an empty or duplicate response key"
        keys.add(key)
    return keys, ""


def _paper_relative_sidecar_path(path: Path, paper_dir: Path) -> str | None:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError):
        return None


def _selected_current_revalidation_coverage_error(
    audit_payload: Mapping[str, Any],
    sidecar: Mapping[str, Any],
    *,
    paper_dir: Path,
    sidecar_path: Path,
) -> str:
    """Validate the selected-current rebind before accepting its union.

    A selected-current sidecar deliberately serializes only the semantic
    complement of a separately authenticated differential overlay.  Its
    provenance is therefore not interchangeable with the older
    ``manual_current_complement`` marker that might have been copied from its
    historical input.  The current-revalidation module owns the replay: it
    checks the exact selected descriptor ledger, attestation bytes, overlay
    bytes, and the complete current generated-group union.  This helper is
    intentionally lazy because that module imports this evidence layer.
    """

    metadata = sidecar.get("current_selected_semantic_revalidation")
    if not isinstance(metadata, Mapping):
        return ""
    paper = str(audit_payload.get("paper") or paper_dir.name).strip()
    if not paper:
        return "canonical selected-current rebind has no paper identity"
    try:
        from scripts import source_record_current_revalidation as revalidation
    except Exception as exc:  # noqa: BLE001 - evidence must fail closed.
        return (
            "canonical selected-current rebind could not load its authenticated "
            f"replay validator: {type(exc).__name__}: {exc}"
        )
    try:
        errors = revalidation.validate_selected_rebound_sidecar(
            dict(audit_payload),
            dict(sidecar),
            paper=paper,
            paper_dir=paper_dir,
            output_sidecar_path=sidecar_path,
            include_downstream_target_disposition=False,
        )
    except Exception as exc:  # noqa: BLE001 - the replay validator fails closed.
        return (
            "canonical selected-current rebind replay raised "
            f"{type(exc).__name__}: {exc}"
        )
    if errors:
        return (
            "canonical selected-current rebind is not an authenticated "
            "selected-plus-overlay union: "
            + "; ".join(str(error) for error in errors[:3])
        )
    return ""


def canonical_source_record_sidecar_effective_coverage_error(
    audit_payload: Mapping[str, Any],
    sidecar: Mapping[str, Any],
    *,
    effective_items: Mapping[str, Mapping[str, Any]],
    paper_dir: Path,
    sidecar_path: Path,
    primary_closeout_source_record_receipt: bool = False,
) -> str:
    """Validate the canonical sidecar's complete effective response coverage.

    A normal ordinary sidecar must serialize exactly one response slot for
    every generator-produced raw judgment group.  A partial sidecar is valid
    only when every omitted slot is supplied by an in-memory,
    loader-authenticated overlay, or when its completed manual-complement
    provenance covers the remaining exact ledger.  A selected-current rebind
    is a stricter overlay-complement case: it must replay its own attestation
    and descriptor ledger first.  Serialized provenance markers are never
    evidence on their own.  The caller must pass the effective mapping
    returned by the ordinary loader after those overlays have been revalidated,
    and the union must exactly match the raw group ledger.

    The comparison is structural: raw groups and loader-authenticated response
    slots are content-addressed audit coordinates.  It does not use theorem,
    declaration, binder, or function-name similarity to infer coverage.
    """

    if not canonical_source_record_match_sidecar_path(sidecar_path, paper_dir):
        return "coverage guard was asked to validate a noncanonical source-record sidecar"
    groups, group_errors = raw_source_record_obligation_groups(audit_payload)
    if group_errors:
        return (
            "current source-record raw group ledger is malformed: "
            + "; ".join(sorted(group_errors.values())[:3])
        )
    expected = {str(key).strip() for key in groups}
    if not expected:
        # A keyless certificate artifact still belongs to the raw aggregate
        # receipt but has no response slot. There is no canonical-sidecar
        # coverage assertion to make when the generator emitted no groups.
        return ""
    if "" in expected:
        return "current source-record raw group ledger has an empty response key"
    stored, stored_error = _canonical_source_record_sidecar_item_keys(sidecar)
    if stored is None:
        return stored_error
    extra_stored = sorted(stored - expected)
    if extra_stored:
        return (
            "canonical source-record sidecar has response key(s) absent from the "
            "current raw group ledger: "
            + ", ".join(extra_stored[:5])
            + ("; ..." if len(extra_stored) > 5 else "")
        )
    if stored == expected:
        return ""

    # The ordinary loader gives a current authenticated overlay precedence over
    # stale ordinary responses.  When that effective ledger already covers the
    # entire current raw group set, it is sufficient on its own: a historical
    # selected-complement marker cannot make the independently authenticated
    # current union less sound.  This is structural/receipt-based; the keys
    # only index generated groups and never establish semantic correspondence.
    effective = {
        str(key).strip(): value
        for key, value in effective_items.items()
        if str(key).strip()
    }
    if (
        set(effective) == expected
        and all(
            key in stored or _is_loaded_source_record_overlay_item(value)
            for key, value in effective.items()
        )
    ):
        return ""

    # A selected-current rebind has its own authenticated coverage mechanism:
    # the current-revalidation replay proves that this sidecar covers exactly
    # the semantic complement of the loaded differential overlay.  It is not
    # a waiver for an old/manual marker.  In particular, a stale inherited
    # manual-current-complement receipt is ignored only after that replay
    # succeeds and the independently loaded effective union below is exact.
    selected_revalidation_error = _selected_current_revalidation_coverage_error(
        audit_payload,
        sidecar,
        paper_dir=paper_dir,
        sidecar_path=sidecar_path,
    )
    if selected_revalidation_error:
        return selected_revalidation_error
    if isinstance(sidecar.get("current_selected_semantic_revalidation"), Mapping):
        effective_keys = set(effective)
        if effective_keys and effective_keys == expected:
            return ""
        missing = sorted(expected - effective_keys)
        extra = sorted(effective_keys - expected)
        return (
            "canonical selected-current rebind does not have exact authenticated "
            "effective coverage of the current raw group ledger"
            + (f"; missing={missing[:5]}" if missing else "")
            + (f"; extra={extra[:5]}" if extra else "")
        )

    # A generic authenticated overlay may legitimately cover only a subset of
    # the current raw groups while another group awaits manual review.  Preserve
    # that authenticated subset for low-level consumers; the full closeout
    # gate separately compares the effective set with ``expected`` and reports
    # the still-missing groups.  Do not accept a plain partial mapping just
    # because its keys happen to look current: every effective response not
    # serialized by the canonical sidecar must carry a private loader
    # capability from an exact descriptor-replay transport.
    if (
        effective
        and set(effective) <= expected
        and any(key not in stored for key in effective)
        and all(
            key in stored or _is_loaded_source_record_overlay_item(value)
            for key, value in effective.items()
        )
    ):
        return ""

    complement = sidecar.get(SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_FIELD)
    if not isinstance(complement, Mapping):
        return (
            "canonical source-record sidecar is an unlabelled partial fragment: "
            f"it serializes {len(stored)} of {len(expected)} current raw response "
            "groups without manual_current_complement provenance"
        )
    if not schema_version_is_exact(
        complement.get("schema"), SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_SCHEMA
    ):
        return "canonical manual_current_complement has an unsupported schema"
    if str(complement.get("policy_version") or "").strip() not in (
        SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_POLICY_VERSIONS
    ):
        return "canonical manual_current_complement has an unsupported policy version"
    if str(complement.get("completed_template_review_scope") or "").strip() != (
        SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_SCOPE
    ):
        return "canonical manual_current_complement has the wrong review scope"
    raw_digest = str(audit_payload.get("source_record_audit_sha256") or "").strip()
    if not raw_digest or str(
        complement.get("current_source_record_audit_sha256") or ""
    ).strip() != raw_digest:
        return "canonical manual_current_complement is not bound to the current raw receipt"
    expected_key_digest = canonical_json_digest(sorted(expected))
    if str(complement.get("generated_judgment_keys_sha256") or "").strip() != (
        expected_key_digest
    ):
        return "canonical manual_current_complement has stale generated-key coverage"
    relative_sidecar_path = _paper_relative_sidecar_path(sidecar_path, paper_dir)
    if relative_sidecar_path is None or str(
        complement.get("output_sidecar_path") or ""
    ).strip() != relative_sidecar_path:
        return "canonical manual_current_complement names a different output sidecar"
    if not str(complement.get("template_reviewer") or "").strip() or not str(
        complement.get("template_validated_at") or ""
    ).strip():
        return "canonical manual_current_complement lacks completed-template reviewer metadata"

    effective = {str(key).strip() for key in effective_items}
    if not effective or "" in effective or effective != expected:
        if primary_closeout_source_record_receipt:
            # The consolidated primary gate has already validated this exact
            # raw ledger, including its runtime-only strict full-Spec receipts.
            # This downstream integrity reader deliberately has no serialized
            # copy of those receipts, so it may not demand duplicate manual
            # semantic-model rows after it has checked the canonical sidecar's
            # path, raw pin, generated-key pin, and complement provenance.
            return ""
        missing = sorted(expected - effective)
        extra = sorted(effective - expected)
        return (
            "canonical manual_current_complement does not have exact authenticated "
            "effective coverage of the current raw group ledger"
            + (f"; missing={missing[:5]}" if missing else "")
            + (f"; extra={extra[:5]}" if extra else "")
        )
    return ""


def explicit_source_route_semantic_model_findings(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Require current expanded-model evidence for explicit-route v10 closeout.

    Exact source routes prevent a paper row from silently drifting away from a
    named source endpoint, but they do not by themselves compare its carrier,
    probability law, conditioning convention, or endpoint behavior.  A full
    closeout using that strict v10 surface therefore needs the schema-2,
    expanded-type semantic-model lane and current judgments for every generated
    semantic item.  The trigger is status configuration and artifact content,
    never a theorem or function name.
    """

    if context is not None and context.v11_lean_claim_graph_selected:
        return []
    legacy_state = (
        context.require_legacy_source_record_state()
        if context is not None
        else None
    )
    if (
        status not in FULL_CLOSEOUT_STATUSES
        or not explicit_source_routes_enabled(status_payload)
    ):
        return []
    corrected_scope_current = (
        context.corrected_scope_current
        if context is not None
        else author_approved_corrected_scope_contract_is_current(
            folder, status_payload
        )
    )
    if corrected_scope_current:
        # A current author-approved corrected-model contract has its own
        # expanded semantic-item and bridge validation path. It intentionally
        # replaces archive-source matching rather than weakening it by name.
        return []

    # A canonical direct-row receipt is an explicit, current alternative to
    # the raw source-record lane.  It binds the source map, source bytes,
    # direct review ledger, interface closure, protocol, and focused build;
    # do not demand a freshly regenerated raw machine record merely because
    # that distinct evidence lane was not selected.
    direct_receipt_current, _direct_receipt_error = (
        direct_source_row_review_receipt_state(
            folder, require_source_bytes=require_source_bytes
        )
    )
    if direct_receipt_current:
        return []

    # A v11 source-to-Spec campaign retains the same raw-integrity and
    # semantic-model validation, but its occurrence-indexed contract is the
    # authoritative current-evidence selector.  Requiring this legacy v10
    # aggregate lane as well would double-count semantic parents that v11
    # deliberately discharges from its exact runtime receipts.
    source_map_payload = (
        context.statement_map
        if context is not None
        else load_json(canonical_sidecar(folder, "paper_statement_map.json"))
    )
    if raw_source_spec_screening_requested(
        status_payload, source_map_payload, folder=folder
    ):
        return []

    findings: list[Finding] = []

    def add(path: Path, message: str) -> None:
        findings.append(Finding("ERROR", folder.name, rel(path), message))

    review_surface = status_payload.get("review_surface")
    semantic_config = (
        review_surface.get("semantic_model_review")
        if isinstance(review_surface, dict)
        else None
    )
    if not isinstance(semantic_config, dict):
        add(
            folder / "status.json",
            f"full-closeout status `{status}` with explicit v10 source routes requires "
            "review_surface.semantic_model_review schema 2",
        )
        return findings
    dimensions = semantic_config.get("required_dimensions")
    normalized_dimensions = (
        [str(dimension).strip() for dimension in dimensions]
        if isinstance(dimensions, list)
        else []
    )
    if (
        not schema_version_is_exact(
            semantic_config.get("schema"), SEMANTIC_MODEL_REVIEW_SCHEMA
        )
        or len(normalized_dimensions) != len(set(normalized_dimensions))
        or set(normalized_dimensions) != SEMANTIC_MODEL_REVIEW_DIMENSIONS
    ):
        add(
            folder / "status.json",
            "explicit v10 source-route closeout requires semantic_model_review "
            "schema 2 with every expanded-semantic dimension exactly once",
        )
        return findings

    if context is not None:
        assert legacy_state is not None
        audit_path = legacy_state.inputs.audit_snapshot.path
        audit_path_error = legacy_state.inputs.audit_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
    if audit_path_error:
        add(folder / "status.json", audit_path_error)
        return findings
    assert audit_path is not None
    audit_payload = (
        legacy_state.inputs.audit_snapshot.payload
        if legacy_state is not None
        else load_json(audit_path)
    )
    if audit_payload is None:
        add(
            audit_path,
            "explicit v10 source-route closeout requires a current generated "
            "source-record semantic-model audit",
        )
        return findings
    if (
        str(audit_payload.get("prompt_version") or "").strip()
        != CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
    ):
        add(
            audit_path,
            "explicit v10 source-route closeout requires source-record prompt "
            f"`{CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION}`",
        )
        return findings
    map_digest = (
        context.paper_statement_map_sha256
        if context is not None
        else current_paper_statement_map_sha256(folder)
    )
    if context is not None:
        assert legacy_state is not None
        semantic_contract_revalidation = legacy_state.semantic_contract_revalidation
        semantic_contract_revalidation_error = (
            legacy_state.semantic_contract_revalidation_error
        )
        identity_error = legacy_state.source_record_identity_error
    else:
        (
            semantic_contract_revalidation,
            semantic_contract_revalidation_error,
        ) = source_record_semantic_contract_revalidation_context(
            folder,
            audit_payload,
            status_payload=status_payload,
        )
        identity_error = source_record_audit_identity_error(
            audit_payload,
            expected_paper_statement_map_sha256=map_digest,
            folder=folder,
            semantic_contract_revalidation=semantic_contract_revalidation,
            prevalidated_semantic_contract_revalidation_error=(
                semantic_contract_revalidation_error
            ),
        )
    if identity_error:
        add(
            audit_path,
            "explicit v10 source-route closeout requires a current generated "
            "source-record audit: " + identity_error,
        )
        return findings
    raw_expected = audit_payload.get("expected_semantic_model_judgment_keys")
    raw_semantic_items = audit_payload.get("semantic_model_items")
    if not isinstance(raw_expected, list):
        add(
            audit_path,
            "explicit v10 source-route closeout requires "
            "expected_semantic_model_judgment_keys to be a list",
        )
        return findings
    if not isinstance(raw_semantic_items, list):
        add(
            audit_path,
            "explicit v10 source-route closeout requires semantic_model_items to be a list",
        )
        return findings
    expected_keys = [
        key.strip() if isinstance(key, str) else ""
        for key in raw_expected
    ]
    if not expected_keys:
        add(
            audit_path,
            "explicit v10 source-route closeout generated no required semantic-model "
            "judgments; regenerate the source-record audit from the configured review surface",
        )
        return findings
    if any(not key for key in expected_keys) or len(expected_keys) != len(set(expected_keys)):
        add(
            audit_path,
            "explicit v10 source-route closeout requires nonempty unique "
            "expected semantic-model judgment keys",
        )
        return findings
    semantic_keys: list[str] = []
    for item in raw_semantic_items:
        key = (
            item.get("judgment_key").strip()
            if isinstance(item, dict) and isinstance(item.get("judgment_key"), str)
            else ""
        )
        semantic_keys.append(key)
        dimensions_for_item = item.get("dimensions") if isinstance(item, dict) else None
        if semantic_model_item_dimension_ids_error(dimensions_for_item):
            add(
                audit_path,
                "explicit v10 source-route closeout requires every generated "
                "semantic-model item to carry each schema-2 base dimension "
                "exactly once, with only explicitly generated source-scoped "
                "extensions; an empty dimension list is not semantic evidence",
            )
            return findings
    if any(not key for key in semantic_keys) or len(semantic_keys) != len(set(semantic_keys)):
        add(
            audit_path,
            "explicit v10 source-route closeout requires semantic_model_items with "
            "nonempty unique judgment keys",
        )
        return findings
    expected = set(expected_keys)
    semantic_items = set(semantic_keys)
    if expected != semantic_items:
        add(
            audit_path,
            "explicit v10 source-route closeout requires generated semantic-model items "
            "to match the expected semantic-model judgment keys exactly",
        )
        return findings

    if context is not None:
        assert legacy_state is not None
        match_path = legacy_state.inputs.match_snapshot.path
        match_path_error = legacy_state.inputs.match_path_error
    else:
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if match_path_error:
        add(folder / "status.json", match_path_error)
        return findings
    assert match_path is not None
    current = (
        legacy_state.current_source_record_judgments
        if legacy_state is not None
        else _current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=map_digest,
            folder=folder,
            prevalidated_source_record_identity_error=identity_error,
            statement_map_override=source_map_payload,
            status_payload_override=status_payload,
        )
    )
    missing = sorted(expected - set(current))
    if missing:
        add(
            match_path,
            f"explicit v10 source-route closeout has {len(missing)} semantic-model "
            "judgment(s) without current complete source-record evidence: "
            + ", ".join(missing[:5])
            + ("; ..." if len(missing) > 5 else ""),
        )
    return findings


def check_source_record_configured_rows(
    folder: Path, *, context: EvidenceRunContext | None = None
) -> list[Finding]:
    """Fail closed when saved provenance evidence omitted configured Lean rows.

    The source-record helper records this condition explicitly.  Treat it as
    an audit-coverage error for every paper status: a partial paper may carry
    open mathematical obligations, but its configured review surface may not
    vanish because a parser or formatting change missed a declaration.
    """

    if context is not None and context.v11_lean_claim_graph_selected:
        return []
    legacy_state = (
        context.require_legacy_source_record_state()
        if context is not None
        else None
    )

    audit_path = canonical_sidecar(folder, "source_record_audit.json")
    audit_payload = (
        legacy_state.inputs.audit_snapshot.payload
        if legacy_state is not None
        and legacy_state.inputs.audit_snapshot.path.resolve() == audit_path.resolve()
        else load_json(audit_path)
    )
    if not isinstance(audit_payload, dict):
        return []
    missing = sorted(
        {
            str(row).strip()
            for row in audit_payload.get("missing_configured_review_rows") or []
            if isinstance(row, str) and row.strip()
        }
    )
    if not missing:
        return []
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(audit_path),
            "source-record audit omitted "
            f"{len(missing)} configured review row(s); audit coverage is incomplete: "
            + ", ".join(missing[:8])
            + ("; ..." if len(missing) > 8 else ""),
        )
    ]


def check_source_premise_consistency(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Keep Lean-checked source-input contradictions visible at closeout.

    This lane is opt-in by the generated source-record schema so historical
    sidecars remain readable.  Once a current audit declares the schema, a
    direct elaborated route from a reviewed source record to ``False`` blocks a
    full closeout.  A route that still needs extra non-proposition data is
    retained as a warning rather than promoted to a contradiction.
    """

    if context is not None and context.v11_lean_claim_graph_selected:
        return []
    legacy_state = (
        context.require_legacy_source_record_state()
        if context is not None
        else None
    )

    audit_path = canonical_sidecar(folder, "source_record_audit.json")
    audit_payload = (
        legacy_state.inputs.audit_snapshot.payload
        if legacy_state is not None
        and legacy_state.inputs.audit_snapshot.path.resolve() == audit_path.resolve()
        else load_json(audit_path)
    )
    if not isinstance(audit_payload, dict):
        return []
    if not schema_version_is_exact(
        audit_payload.get("source_premise_consistency_schema"), 1
    ):
        return []
    severity = source_record_judgment_freshness_severity(status)
    error = str(audit_payload.get("source_premise_consistency_error") or "").strip()
    if error:
        return [
            Finding(
                severity,
                folder.name,
                rel(audit_path),
                "source-premise consistency scan did not complete: " + error,
            )
        ]
    raw_items = audit_payload.get("source_premise_consistency_items")
    if not isinstance(raw_items, list):
        return [
            Finding(
                severity,
                folder.name,
                rel(audit_path),
                "source-premise consistency schema is present but its elaborated "
                "result list is missing or malformed",
            )
        ]

    findings: list[Finding] = []
    for raw_item in raw_items:
        if not isinstance(raw_item, dict):
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(audit_path),
                    "source-premise consistency result contains a malformed item",
                )
            )
            continue
        reviewed = str(raw_item.get("reviewed_input_type") or "").strip()
        direct = raw_item.get("direct_eliminators")
        data_dependent = raw_item.get("candidate_data_dependent_eliminators")
        if not reviewed or not isinstance(direct, list) or not isinstance(data_dependent, list):
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(audit_path),
                    "source-premise consistency item lacks a reviewed input or "
                    "well-formed eliminator lists",
                )
            )
            continue
        direct_names = sorted(
            {
                str(candidate.get("candidate") or "").strip()
                for candidate in direct
                if isinstance(candidate, dict)
                and str(candidate.get("candidate") or "").strip()
                and candidate.get("direct_eliminator") is True
            }
        )
        if direct_names:
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(audit_path),
                    "Lean elaboration found a direct route from reviewed source input "
                    f"`{reviewed}` to `False` via "
                    + ", ".join(direct_names[:4])
                    + ("; ..." if len(direct_names) > 4 else "")
                    + ". This source-facing model premise is inconsistent and cannot "
                    "support a full formalization claim.",
                )
            )
        data_names = sorted(
            {
                str(candidate.get("candidate") or "").strip()
                for candidate in data_dependent
                if isinstance(candidate, dict)
                and str(candidate.get("candidate") or "").strip()
                and candidate.get("direct_eliminator") is False
            }
        )
        if data_names:
            findings.append(
                Finding(
                    "WARN",
                    folder.name,
                    rel(audit_path),
                    "Lean found a `False` route involving reviewed source input "
                    f"`{reviewed}` plus extra non-proposition data via "
                    + ", ".join(data_names[:4])
                    + ("; ..." if len(data_names) > 4 else "")
                    + ". It is not treated as a direct contradiction, but remains "
                    "source-model proof debt until those extra data parameters are audited.",
                )
            )
    return findings


def check_source_record_judgments(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    if context is not None and context.v11_lean_claim_graph_selected:
        return []
    legacy_state = (
        context.require_legacy_source_record_state()
        if context is not None
        else None
    )

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    corrected_scope_current = (
        context.corrected_scope_current
        if context is not None
        else author_approved_corrected_scope_contract_is_current(
            folder, status_payload
        )
    )
    if corrected_scope_current:
        # The checked author-approved contract supersedes source-to-archive LLM
        # matching for this explicitly different target. Its current source-
        # record digest and expanded model-field mappings are validated above.
        return []
    v11_direct_current, _v11_direct_error = v11_direct_semantic_review_state(
        folder,
        status,
        require_source_bytes=require_source_bytes,
        context=context,
    )
    if v11_direct_current:
        # A current v11 ledger is the selected replacement for the historical
        # generated source-record lane.  The ledger and every material library
        # dependency are validated above; a final closure receipt adds build
        # and closure binding later, rather than requiring a duplicate v10
        # source-record reissue during preparation.
        return []
    if legacy_state is not None:
        audit_path = legacy_state.inputs.audit_snapshot.path
        audit_path_error = legacy_state.inputs.audit_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
    if audit_path_error:
        return [
            Finding(
                source_record_judgment_freshness_severity(status),
                folder.name,
                rel(folder / "status.json"),
                audit_path_error,
            )
        ]
    assert audit_path is not None
    audit_payload = (
        legacy_state.inputs.audit_snapshot.payload
        if legacy_state is not None
        else load_json(audit_path)
    )
    if not isinstance(audit_payload, dict):
        return []
    map_digest = (
        context.paper_statement_map_sha256
        if context is not None
        else current_paper_statement_map_sha256(folder)
    )
    if legacy_state is not None:
        semantic_contract_revalidation = legacy_state.semantic_contract_revalidation
        semantic_contract_revalidation_error = (
            legacy_state.semantic_contract_revalidation_error
        )
        identity_error = legacy_state.source_record_identity_error
    else:
        (
            semantic_contract_revalidation,
            semantic_contract_revalidation_error,
        ) = source_record_semantic_contract_revalidation_context(
            folder, audit_payload
        )
        identity_error = source_record_audit_identity_error(
            audit_payload,
            expected_paper_statement_map_sha256=map_digest,
            folder=folder,
            semantic_contract_revalidation=semantic_contract_revalidation,
            prevalidated_semantic_contract_revalidation_error=(
                semantic_contract_revalidation_error
            ),
        )
    if identity_error:
        direct_receipt_current, _direct_receipt_error = (
            direct_source_row_review_receipt_state(
            folder, require_source_bytes=require_source_bytes
            )
        )
        if direct_receipt_current:
            return []
        return [
            Finding(
                source_record_judgment_freshness_severity(status),
                folder.name,
                rel(audit_path),
                "saved source-record audit cannot support current judgments: "
                + identity_error,
            )
        ]
    # A current direct-row receipt is a deliberately selected alternative to
    # the aggregate raw source-record judgment sidecar.  Its v11 ledger is
    # independently checked by `v11_raw_source_spec_screening_findings`; do
    # not make that selected evidence lane falsely depend on historical raw
    # response-key coordinates after the raw audit itself has changed.
    direct_receipt_current, _direct_receipt_error = direct_source_row_review_receipt_state(
        folder, require_source_bytes=require_source_bytes
    )
    if direct_receipt_current:
        return []
    if legacy_state is not None:
        match_path = legacy_state.inputs.match_snapshot.path
        match_path_error = legacy_state.inputs.match_path_error
    else:
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if match_path_error:
        return [
            Finding(
                source_record_judgment_freshness_severity(status),
                folder.name,
                rel(folder / "status.json"),
                match_path_error,
            )
        ]
    assert match_path is not None
    match_payload = (
        (legacy_state.inputs.match_snapshot.payload or {})
        if legacy_state is not None
        else (load_json(match_path) or {})
    )
    current_items = (
        legacy_state.current_source_record_judgments
        if legacy_state is not None
        else current_source_record_judgment_items(
            audit_payload,
            match_payload,
            expected_paper_statement_map_sha256=map_digest,
            folder=folder,
        )
    )
    if canonical_source_record_match_sidecar_path(match_path, folder):
        coverage_error = canonical_source_record_sidecar_effective_coverage_error(
            audit_payload,
            match_payload,
            effective_items=current_items,
            paper_dir=folder,
            sidecar_path=match_path,
            primary_closeout_source_record_receipt=(
                context is not None
                and _has_current_primary_closeout_source_record_judgment_receipt(
                    context
                )
            ),
        )
        if coverage_error:
            return [
                Finding(
                    source_record_judgment_freshness_severity(status),
                    folder.name,
                    rel(match_path),
                    coverage_error,
                )
            ]
    required = source_record_required_keys(
        audit_payload,
        semantic_contract_revalidation=semantic_contract_revalidation,
    )
    if not required:
        return []
    current = set(current_items)
    missing = [key for key in required if key not in current]
    if not missing:
        return []
    if (
        context is not None
        and _has_current_primary_closeout_source_record_judgment_receipt(context)
    ):
        # The exact primary closeout gate has already checked this generated
        # source-record surface, including any strict full-Spec receipt
        # coverage.  Keep the path, raw identity, and current-sidecar checks
        # above; only avoid reporting the same missing-count result a second
        # time inside this one evidence transaction.
        return []
    return [
        Finding(
            source_record_judgment_freshness_severity(status),
            folder.name,
            rel(match_path),
            f"source-record audit has {len(required)} required boundary/field/semantic-model item(s), "
            f"but {len(missing)} lack current validated judgments for the same "
            "prompt version and audit digest: "
            + ", ".join(missing[:5])
            + ("; ..." if len(missing) > 5 else ""),
        )
    ]


def direct_source_row_review_receipt_state(
    folder: Path, *, require_source_bytes: bool = True
) -> tuple[bool, str]:
    """Return whether a canonical receipt selects and validates the direct lane.

    The receipt is optional.  Its absence does not change the ordinary raw
    source-record policy; an existing but invalid receipt remains visible as a
    separate closeout error rather than silently falling back to a bypass.
    """

    try:
        from scripts.final_closure_receipt import (
            DIRECT_SOURCE_ROW_REVIEW_LANE,
            final_closure_receipt_error,
            final_closure_receipt_path,
        )
        receipt_path = final_closure_receipt_path(ROOT, folder.name)
        if not receipt_path.is_file():
            return False, ""
        error = final_closure_receipt_error(
            ROOT,
            folder.name,
            required_lane=DIRECT_SOURCE_ROW_REVIEW_LANE,
            allow_missing_source_bytes=not require_source_bytes,
        )
        return error == "", error
    except Exception as exc:  # noqa: BLE001 - receipt validation must fail closed.
        return False, f"could not validate canonical direct-review receipt: {exc}"


def final_closure_receipt_findings(
    folder: Path, *, require_source_bytes: bool = True
) -> list[Finding]:
    """Expose an invalid optional canonical receipt without inventing a lane."""

    current, error = direct_source_row_review_receipt_state(
        folder, require_source_bytes=require_source_bytes
    )
    if current or not error:
        return []
    try:
        path = (folder / "FINAL_CLOSURE_RECEIPT.md").relative_to(ROOT)
        display = str(path)
    except ValueError:
        display = str(folder / "FINAL_CLOSURE_RECEIPT.md")
    return [
        Finding(
            "ERROR",
            folder.name,
            display,
            "canonical direct-source-row-review receipt is invalid: " + error,
        )
    ]


def graph_native_closure_fast_path_findings(
    folder: Path,
    *,
    release: bool,
    require_source_bytes: bool = True,
) -> list[Finding] | None:
    """Validate a selected graph credential without replaying legacy producers.

    ``None`` means that the paper does not select the graph-native schema and
    must continue through the historical evidence-integrity transaction.  A
    list means that a graph-native receipt is canonical for this paper. Schema
    5 selects the transitional accepting bundle; schema 6 selects the accepted
    graph itself. Validate that one credential directly and never fall back to
    an independent legacy replay.
    An invalid graph therefore returns one fail-closed finding instead of
    spending minutes reconstructing evidence that cannot confer acceptance.

    Human review remains an optional, reviewer-owned annotation layer.  Its
    incomplete status stays visible as a warning but cannot manufacture or
    revoke graph acceptance.
    """

    try:
        from scripts.final_closure_receipt import (
            FinalClosureReceiptError,
            final_closure_receipt_error,
            load_final_closure_receipt,
        )
        receipt = load_final_closure_receipt(ROOT, folder.name)
    except (FinalClosureReceiptError, OSError, UnicodeError, ValueError):
        return None
    if receipt.payload.get("schema") not in {5, 6}:
        return None

    error = final_closure_receipt_error(
        ROOT,
        folder.name,
        allow_missing_source_bytes=not require_source_bytes,
    )
    if error:
        return [
            Finding(
                "ERROR",
                folder.name,
                rel(receipt.path),
                "canonical obligation-graph credential is invalid: " + error,
            )
        ]

    status, payload = paper_status(folder)
    return check_human_review(folder, status, payload, release)


def source_record_semantic_target_disposition_findings(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate current v10 semantic target verdicts against map and ledger.

    The ordinary source-record freshness gate proves that a response belongs to
    the current generated Lean surface.  This complementary gate decides what
    target that response is allowed to call source-faithful: literal archival
    text, a documented source-model convention, or an approved replacement.
    It runs only for v10 generated records with an explicit source-map
    association, preserving pre-v10 sidecars unchanged.
    """

    if context is not None and context.v11_lean_claim_graph_selected:
        return []
    legacy_state = (
        context.require_legacy_source_record_state()
        if context is not None
        else None
    )

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    if legacy_state is not None:
        audit_path = legacy_state.inputs.audit_snapshot.path
        audit_path_error = legacy_state.inputs.audit_path_error
        match_path = legacy_state.inputs.match_snapshot.path
        match_path_error = legacy_state.inputs.match_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if audit_path_error or match_path_error:
        return []
    assert audit_path is not None and match_path is not None
    audit_payload = (
        legacy_state.inputs.audit_snapshot.payload
        if legacy_state is not None
        else load_json(audit_path)
    )
    if (
        not isinstance(audit_payload, dict)
        or str(audit_payload.get("prompt_version") or "").strip()
        != CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
    ):
        return []
    raw_semantic_items = audit_payload.get("semantic_model_items")
    if not isinstance(raw_semantic_items, list):
        return []
    current = (
        legacy_state.current_source_record_judgments
        if legacy_state is not None
        else current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    )
    if not current:
        return []

    v11_direct_current, _v11_direct_error = v11_direct_semantic_review_state(
        folder,
        status,
        context=context,
    )
    if v11_direct_current:
        # The selected v11 source-to-Spec screen is the current authority for
        # literal-versus-corrected source targets.  Retain the legacy semantic
        # row as dimensional comparison metadata, but do not run its older
        # target-label vocabulary as a second source-target adjudication.
        # An incomplete v11 lane falls through to the strict v10 check below.
        return []

    statement_map_path = transaction_sidecar(
        folder, "paper_statement_map.json", context
    )
    statement_map = transaction_json(statement_map_path, context)
    ledger_path, ledger_path_error = source_proof_fidelity_ledger_path(
        folder, status_payload
    )
    source_proof_fidelity = (
        transaction_json(ledger_path, context)
        if ledger_path_error == "" and ledger_path is not None
        else None
    )
    severity = source_record_judgment_freshness_severity(status)
    findings: list[Finding] = []
    if legacy_state is not None:
        rebind = legacy_state.administrative_projection_rebind
        rebind_path = legacy_state.administrative_projection_rebind_path
        rebind_error = legacy_state.administrative_projection_rebind_error
    else:
        rebind, rebind_path, rebind_error = (
            source_record_administrative_projection_rebind_context(
                folder,
                status_payload,
                audit_path=audit_path,
                audit_payload=audit_payload,
                statement_map_path=statement_map_path,
                statement_map=statement_map,
            )
        )
    if rebind_error:
        findings.append(
            Finding(
                severity,
                folder.name,
                rel(rebind_path or audit_path),
                "administrative source-status projection rebind is invalid: " + rebind_error,
            )
        )
    for item in raw_semantic_items:
        if not isinstance(item, dict):
            continue
        key = str(item.get("judgment_key") or "").strip()
        judgment = current.get(key)
        if not key or not isinstance(judgment, dict):
            continue
        responses = judgment.get("semantic_model_dimensions")
        dimensions = item.get("dimensions")
        if not isinstance(responses, dict) or not isinstance(dimensions, list):
            continue
        for raw_dimension in dimensions:
            if not isinstance(raw_dimension, dict):
                continue
            dimension = str(raw_dimension.get("id") or "").strip()
            response = responses.get(dimension)
            if not dimension or not isinstance(response, dict):
                continue
            for error in semantic_target_disposition_errors(
                item,
                response,
                statement_map=statement_map,
                source_proof_fidelity=source_proof_fidelity,
                validated_vocabulary_binding_source_item_ids=(
                    audit_payload.get(
                        "source_coverage_validated_vocabulary_binding_source_items"
                    )
                ),
                validated_vocabulary_direct_route_source_item_ids=(
                    audit_payload.get(
                        "source_coverage_validated_vocabulary_direct_route_source_items"
                    )
                ),
                administrative_projection_rebind=rebind,
            ):
                findings.append(
                    Finding(
                        severity,
                        folder.name,
                        rel(match_path),
                        f"source-record semantic judgment `{key}` dimension "
                        f"`{dimension}` has invalid source target disposition: {error}",
                    )
                )
    return findings


def has_explicit_semantic_contract_route(statement_map: object) -> bool:
    """Return whether a source map declares a fully-qualified direct/Spec route.

    This is a structural source-map check. It deliberately does not compare a
    source map key, row, binder, or Lean function name with any audit item.
    The generator supplies the stronger declaration-content association once
    this route family is present.
    """

    if not isinstance(statement_map, dict):
        return False
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, dict):
        return False
    for source_item in raw_items.values():
        if not isinstance(source_item, dict) or source_item.get("claim_bearing") is not True:
            continue
        contract = source_item.get("semantic_contract")
        if not isinstance(contract, dict):
            continue
        evidence = str(contract.get("evidence_declaration") or "").strip()
        spec = str(contract.get("spec_declaration") or "").strip()
        if evidence and spec and evidence != spec and "." in evidence and "." in spec:
            return True
    return False


def has_explicit_legacy_direct_source_route(statement_map: object) -> bool:
    """Return whether the selected source surface has a direct non-contract route.

    This follows the same source-presentation selection policy as the
    source-record generator. It does not infer a route from a map key, row, or
    declaration spelling: the map must explicitly list a fully-qualified
    direct route under one of the legacy direct-route fields, and an item with
    any semantic-contract metadata is intentionally left to the contract lane.
    """

    if not isinstance(statement_map, dict):
        return False
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, dict):
        return False
    mode, mode_error = source_coverage_mode_from_map(statement_map)
    if mode_error:
        return False
    selected_items = filter_source_map_items_for_coverage(
        raw_items,
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            statement_map
        ),
    )
    for source_item in selected_items.values():
        if not isinstance(source_item, dict):
            continue
        if source_item.get("claim_bearing") is False:
            continue
        if source_item.get("semantic_contract") is not None:
            continue
        for field in (
            "lean_declarations",
            "proof_lean_declarations",
            "spec_lean_declarations",
        ):
            routes = source_item.get(field)
            if not isinstance(routes, list):
                continue
            if any(
                isinstance(route, str)
                and route.strip()
                and "." in route.strip()
                for route in routes
            ):
                return True
    return False


def source_record_input_target_disposition_findings(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate current v10 boundary/conclusion source-credit dispositions.

    This mirrors the repository gate, but runs from saved artifacts during the
    fast integrity pass.  It validates only generator-owned source-contract
    associations and their content pins; no row, binder, or Lean function name
    is used to decide the route.
    """

    if context is not None and context.v11_lean_claim_graph_selected:
        return []
    legacy_state = (
        context.require_legacy_source_record_state()
        if context is not None
        else None
    )

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    if legacy_state is not None:
        audit_path = legacy_state.inputs.audit_snapshot.path
        audit_path_error = legacy_state.inputs.audit_path_error
        match_path = legacy_state.inputs.match_snapshot.path
        match_path_error = legacy_state.inputs.match_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if audit_path_error or match_path_error:
        return []
    assert audit_path is not None and match_path is not None
    audit_payload = (
        legacy_state.inputs.audit_snapshot.payload
        if legacy_state is not None
        else load_json(audit_path)
    )
    if (
        not isinstance(audit_payload, dict)
        or str(audit_payload.get("prompt_version") or "").strip()
        != CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
    ):
        return []
    severity = source_record_judgment_freshness_severity(status)
    findings: list[Finding] = []
    if legacy_state is not None:
        semantic_contract_revalidation = legacy_state.semantic_contract_revalidation
        semantic_contract_revalidation_error = (
            legacy_state.semantic_contract_revalidation_error
        )
    else:
        (
            semantic_contract_revalidation,
            semantic_contract_revalidation_error,
        ) = source_record_semantic_contract_revalidation_context(
            folder, audit_payload
        )
    if semantic_contract_revalidation_error:
        findings.append(
            Finding(
                severity,
                folder.name,
                rel(audit_path),
                "semantic-contract revalidation is invalid: "
                + semantic_contract_revalidation_error,
            )
        )
    effective_semantic_errors = source_record_effective_semantic_errors(
        audit_payload,
        semantic_contract_revalidation=semantic_contract_revalidation,
    )
    statement_map_path = transaction_sidecar(
        folder, "paper_statement_map.json", context
    )
    statement_map = transaction_json(statement_map_path, context)
    if legacy_state is not None:
        rebind = legacy_state.administrative_projection_rebind
        rebind_path = legacy_state.administrative_projection_rebind_path
        rebind_error = legacy_state.administrative_projection_rebind_error
    else:
        rebind, rebind_path, rebind_error = (
            source_record_administrative_projection_rebind_context(
                folder,
                status_payload,
                audit_path=audit_path,
                audit_payload=audit_payload,
                statement_map_path=statement_map_path,
                statement_map=statement_map,
            )
        )
    if rebind_error:
        findings.append(
            Finding(
                severity,
                folder.name,
                rel(rebind_path or audit_path),
                "administrative source-status projection rebind is invalid: "
                + rebind_error,
            )
        )
    has_input_surface = any(
        isinstance(audit_payload.get(section), list)
        and bool(audit_payload.get(section))
        for section in ("boundary_input_items", "conclusion_dependency_items")
    )
    has_contract_route = has_explicit_semantic_contract_route(statement_map)
    has_legacy_direct_route = has_explicit_legacy_direct_source_route(statement_map)
    if (
        (has_legacy_direct_route or (has_input_surface and has_contract_route))
        and not schema_version_is_supported(
            audit_payload.get("source_contract_association_schema"), {1, 2}
        )
    ):
        missing_schema_message = (
            "v10 source-record artifact has an explicit semantic-contract route but "
            "no generated declaration-content source-contract association schema; regenerate the audit"
            if has_contract_route and not has_legacy_direct_route
            else "v10 source-record artifact has an explicit source route but no "
            "generated declaration-content source association schema; regenerate the audit"
        )
        findings.append(
            Finding(
                severity,
                folder.name,
                rel(audit_path),
                missing_schema_message,
            )
        )
    if has_legacy_direct_route:
        counts = audit_payload.get("source_contract_association_counts")
        direct_declaration_count = (
            counts.get("explicit_direct_route_declaration_count")
            if isinstance(counts, dict)
            else None
        )
        direct_association_count = (
            counts.get("explicit_direct_route_association_count")
            if isinstance(counts, dict)
            else None
        )
        if not isinstance(direct_declaration_count, int) or not isinstance(
            direct_association_count, int
        ):
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(audit_path),
                    "v10 source-record artifact has an explicit selected direct source route "
                    "but no generated direct-route association inventory; regenerate the audit",
                )
            )
        elif direct_declaration_count != direct_association_count:
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(audit_path),
                    "generated explicit direct source-route associations are incomplete or "
                    "ambiguous; inspect source_contract_association_errors and regenerate the audit",
                )
            )
    for error in effective_semantic_errors.get(
        "source_contract_association_errors",
        audit_payload.get("source_contract_association_errors") or [],
    ):
        message = str(error).strip()
        if message:
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(audit_path),
                    "generated source-contract association is invalid: " + message,
                )
            )

    current = (
        legacy_state.current_source_record_judgments
        if legacy_state is not None
        else current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    )
    if not current:
        return findings
    ledger_path, ledger_path_error = source_proof_fidelity_ledger_path(
        folder, status_payload
    )
    source_proof_fidelity = (
        transaction_json(ledger_path, context)
        if ledger_path_error == "" and ledger_path is not None
        else None
    )
    if legacy_state is not None:
        regularity_context = legacy_state.configured_assumption_regularity_context
    else:
        regularity_context, _regularity_context_error = (
            load_configured_assumption_formalization_regularity_context(
                folder,
                audit_payload,
                status_payload=status_payload,
            )
        )
    seen: set[tuple[str, str]] = set()
    for section in ("boundary_input_items", "conclusion_dependency_items"):
        raw_items = audit_payload.get(section)
        if not isinstance(raw_items, list):
            continue
        for item in raw_items:
            if not isinstance(item, dict):
                continue
            key = str(item.get("judgment_key") or "").strip()
            judgment = current.get(key)
            if not key or not isinstance(judgment, dict):
                continue
            for error in source_input_target_disposition_errors(
                item,
                judgment,
                statement_map=statement_map,
                source_proof_fidelity=source_proof_fidelity,
                status=status,
                administrative_projection_rebind=rebind,
                configured_assumption_formalization_regularity_context=(
                    regularity_context
                ),
            ):
                dedupe_key = (key, error)
                if dedupe_key in seen:
                    continue
                seen.add(dedupe_key)
                findings.append(
                    Finding(
                        severity,
                        folder.name,
                        rel(match_path),
                        f"source-record input judgment `{key}` has invalid source target disposition: {error}",
                    )
                )
    return findings


def source_record_recursive_field_target_disposition_findings(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate convention credit on generated recursive-field route receipts.

    A recursive-field receipt is narrower than a normal theorem-input source
    contract: it binds one structural ancestry path and one convention.  Run
    this saved-artifact check separately so a current LLM sidecar cannot swap
    the convention or use a container receipt to credit an unscoped leaf.
    """

    if context is not None and context.v11_lean_claim_graph_selected:
        return []
    legacy_state = (
        context.require_legacy_source_record_state()
        if context is not None
        else None
    )

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    if legacy_state is not None:
        audit_path = legacy_state.inputs.audit_snapshot.path
        audit_path_error = legacy_state.inputs.audit_path_error
        match_path = legacy_state.inputs.match_snapshot.path
        match_path_error = legacy_state.inputs.match_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if audit_path_error or match_path_error:
        return []
    assert audit_path is not None and match_path is not None
    audit_payload = (
        legacy_state.inputs.audit_snapshot.payload
        if legacy_state is not None
        else load_json(audit_path)
    )
    if (
        not isinstance(audit_payload, dict)
        or str(audit_payload.get("prompt_version") or "").strip()
        != CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
    ):
        return []
    raw_items = audit_payload.get("recursive_field_items")
    if not isinstance(raw_items, list):
        return []
    current = (
        legacy_state.current_source_record_judgments
        if legacy_state is not None
        else current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    )
    if not current:
        return []
    statement_map_path = transaction_sidecar(
        folder, "paper_statement_map.json", context
    )
    statement_map = transaction_json(statement_map_path, context)
    ledger_path, ledger_path_error = source_proof_fidelity_ledger_path(
        folder, status_payload
    )
    source_proof_fidelity = (
        transaction_json(ledger_path, context)
        if ledger_path_error == "" and ledger_path is not None
        else None
    )
    severity = source_record_judgment_freshness_severity(status)
    findings: list[Finding] = []
    if legacy_state is not None:
        rebind = legacy_state.administrative_projection_rebind
        rebind_path = legacy_state.administrative_projection_rebind_path
        rebind_error = legacy_state.administrative_projection_rebind_error
    else:
        rebind, rebind_path, rebind_error = (
            source_record_administrative_projection_rebind_context(
                folder,
                status_payload,
                audit_path=audit_path,
                audit_payload=audit_payload,
                statement_map_path=statement_map_path,
                statement_map=statement_map,
            )
        )
    if rebind_error:
        findings.append(
            Finding(
                severity,
                folder.name,
                rel(rebind_path or audit_path),
                "administrative source-status projection rebind is invalid: "
                + rebind_error,
            )
        )
    for item in raw_items:
        if not isinstance(item, dict):
            continue
        key = str(item.get("judgment_key") or "").strip()
        judgment = current.get(key)
        if not key or not isinstance(judgment, dict):
            continue
        for error in recursive_field_target_disposition_errors(
            item,
            judgment,
            statement_map=statement_map,
            source_proof_fidelity=source_proof_fidelity,
            administrative_projection_rebind=rebind,
        ):
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(match_path),
                    f"source-record recursive-field judgment `{key}` has invalid "
                    f"source target disposition: {error}",
                )
            )
    return findings


def check_plain_formalized_unresolved_source_record_math(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Plain `formalized` cannot retain current unresolved proof obligations."""

    if status != PLAIN_FORMALIZED:
        return []
    if context is not None and context.v11_lean_claim_graph_selected:
        return []
    legacy_state = (
        context.require_legacy_source_record_state()
        if context is not None
        else None
    )
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    corrected_scope_current = (
        context.corrected_scope_current
        if context is not None
        else author_approved_corrected_scope_contract_is_current(
            folder, status_payload
        )
    )
    if corrected_scope_current:
        return []
    if legacy_state is not None:
        audit_path = legacy_state.inputs.audit_snapshot.path
        audit_path_error = legacy_state.inputs.audit_path_error
        match_path = legacy_state.inputs.match_snapshot.path
        match_path_error = legacy_state.inputs.match_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if audit_path_error or match_path_error:
        return [
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                audit_path_error or match_path_error,
            )
        ]
    assert audit_path is not None and match_path is not None
    audit_payload = (
        legacy_state.inputs.audit_snapshot.payload
        if legacy_state is not None
        else load_json(audit_path)
    )
    if audit_payload is None:
        return []
    semantic_contract_revalidation = (
        legacy_state.semantic_contract_revalidation
        if legacy_state is not None
        else source_record_semantic_contract_revalidation_context(
            folder, audit_payload
        )[0]
    )
    required = set(
        source_record_required_keys(
            audit_payload,
            semantic_contract_revalidation=semantic_contract_revalidation,
        )
    )
    current = (
        legacy_state.current_source_record_judgments
        if legacy_state is not None
        else current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    )
    unresolved = sorted(
        key
        for key, value in current.items()
        if key in required
        and str(
            value.get("classification")
            or value.get("judgment")
            or value.get("verdict")
            or value.get("status")
            or ""
        ).strip()
        == "unresolved_assumed_math"
    )
    if not unresolved:
        return []
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(match_path),
            "plain `formalized` status conflicts with "
            f"{len(unresolved)} current source-record item(s) still classified "
            "as unresolved_assumed_math: "
            + ", ".join(unresolved[:5])
            + ("; ..." if len(unresolved) > 5 else ""),
        )
    ]


def check_full_closeout_open_semantic_model_dimensions(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Block either full status when current model semantics remain unresolved."""

    if status not in FULL_CLOSEOUT_STATUSES:
        return []
    if context is not None and context.v11_lean_claim_graph_selected:
        return []
    legacy_state = (
        context.require_legacy_source_record_state()
        if context is not None
        else None
    )
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    corrected_scope_current = (
        context.corrected_scope_current
        if context is not None
        else author_approved_corrected_scope_contract_is_current(
            folder, status_payload
        )
    )
    if corrected_scope_current:
        return []
    if legacy_state is not None:
        audit_path = legacy_state.inputs.audit_snapshot.path
        audit_path_error = legacy_state.inputs.audit_path_error
        match_path = legacy_state.inputs.match_snapshot.path
        match_path_error = legacy_state.inputs.match_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if audit_path_error or match_path_error:
        return [
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                audit_path_error or match_path_error,
            )
        ]
    assert audit_path is not None and match_path is not None
    audit_payload = (
        legacy_state.inputs.audit_snapshot.payload
        if legacy_state is not None
        else load_json(audit_path)
    )
    if audit_payload is None:
        return []
    current = (
        legacy_state.current_source_record_judgments
        if legacy_state is not None
        else current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    )
    open_semantic_dimensions = current_open_semantic_model_dimensions(
        audit_payload, current
    )
    if not open_semantic_dimensions:
        return []
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(match_path),
            f"full-closeout status `{status}` conflicts with "
            f"{len(open_semantic_dimensions)} current semantic-model dimension(s) "
            "that remain mismatch_or_open/documented_partial_boundary: "
            + ", ".join(open_semantic_dimensions[:5])
            + ("; ..." if len(open_semantic_dimensions) > 5 else ""),
        )
    ]


def check_current_unresolved_source_record_math(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Opt-in remediation tracker for current unresolved source-record math debt."""

    if status == PLAIN_FORMALIZED:
        return []
    if context is not None and context.v11_lean_claim_graph_selected:
        return []
    legacy_state = (
        context.require_legacy_source_record_state()
        if context is not None
        else None
    )
    audit_path = canonical_sidecar(folder, "source_record_audit.json")
    match_path = canonical_sidecar(folder, "source_record_match_llm.json")
    use_context = (
        legacy_state is not None
        and legacy_state.inputs.audit_snapshot.path.resolve() == audit_path.resolve()
        and legacy_state.inputs.match_snapshot.path.resolve() == match_path.resolve()
    )
    audit_payload = (
        legacy_state.inputs.audit_snapshot.payload
        if use_context and legacy_state is not None
        else load_json(audit_path)
    )
    if audit_payload is None:
        return []
    semantic_contract_revalidation = (
        legacy_state.semantic_contract_revalidation
        if use_context and legacy_state is not None
        else source_record_semantic_contract_revalidation_context(
            folder, audit_payload
        )[0]
    )
    required = set(
        source_record_required_keys(
            audit_payload,
            semantic_contract_revalidation=semantic_contract_revalidation,
        )
    )
    if not required:
        return []
    current = (
        legacy_state.current_source_record_judgments
        if use_context and legacy_state is not None
        else current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    )
    unresolved = sorted(
        key
        for key, value in current.items()
        if key in required
        and str(
            value.get("classification")
            or value.get("judgment")
            or value.get("verdict")
            or value.get("status")
            or ""
        ).strip()
        == "unresolved_assumed_math"
    )
    open_semantic_dimensions = (
        []
        if status in FULL_CLOSEOUT_STATUSES
        else current_open_semantic_model_dimensions(audit_payload, current)
    )
    if not unresolved and not open_semantic_dimensions:
        return []
    details: list[str] = []
    if unresolved:
        details.append(
            f"{len(unresolved)} current source-record item(s) remain "
            "classified as unresolved_assumed_math: "
            + ", ".join(unresolved[:5])
            + ("; ..." if len(unresolved) > 5 else "")
        )
    if open_semantic_dimensions:
        details.append(
            f"{len(open_semantic_dimensions)} current semantic-model dimension(s) "
            "remain mismatch_or_open/documented_partial_boundary: "
            + ", ".join(open_semantic_dimensions[:5])
            + ("; ..." if len(open_semantic_dimensions) > 5 else "")
        )
    return [
        Finding(
            "WARN",
            folder.name,
            rel(match_path),
            " | ".join(details),
        )
    ]


def check_validator_independence(
    folder: Path,
    status: str,
    release: bool = False,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Report shared audit identities without mistaking them for proof failure.

    A paper can be mathematically closed after a transparently recorded
    single-agent audit, but it cannot be release-certified as independently
    reviewed. Keep the lack of independence visible in every mode and make it
    blocking only for the explicit release gate.
    """

    lane_payloads: dict[str, dict[str, Any]] = {}
    for basename in INDEPENDENT_LANES:
        path = transaction_sidecar(folder, basename, context)
        payload = transaction_json(path, context)
        if payload is None or not sidecar_has_items(payload):
            continue
        lane_payloads[basename] = payload

    judge_keys = {"validator", "model", "judge", "agent"}
    translator_ids = identities_for_keys(
        lane_payloads.get("lean_to_tex_llm.json", {}),
        {"translator", "translation_producer", "producer"},
    )
    statement_judge_ids = identities_for_keys(
        lane_payloads.get("statement_match_llm.json", {}), judge_keys
    )
    coverage_judge_ids = identities_for_keys(
        lane_payloads.get("paper_coverage_llm.json", {}), judge_keys
    )
    defect_support_judge_ids = identities_for_keys(
        lane_payloads.get("defect_support_match_llm.json", {}), judge_keys
    )
    source_manifest_path = transaction_sidecar(
        folder, "paper_statement_map.json", context
    )
    source_manifest = transaction_json(source_manifest_path, context) or {}
    source_curator_ids = identities_for_keys(
        source_manifest,
        {"source_curator", "curator", "source_inventory_producer", "producer"},
    )
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    formalizer_ids = identities_for_keys(
        status_payload,
        {"formalizer", "formalization_agent", "formalization_producer"},
    )

    roles = [
        ("formalizer", formalizer_ids),
        ("source curator", source_curator_ids),
        ("Lean translator", translator_ids),
        ("statement judge", statement_judge_ids),
        ("coverage judge", coverage_judge_ids),
        ("defect-support judge", defect_support_judge_ids),
    ]
    role_pairs = [
        (left_role, left_ids, right_role, right_ids)
        for index, (left_role, left_ids) in enumerate(roles)
        for right_role, right_ids in roles[index + 1 :]
    ]
    findings: list[Finding] = []
    severity = "ERROR" if release and status in CLOSEOUT_STATUSES else "WARN"
    for left_role, left_ids, right_role, right_ids in role_pairs:
        overlap = sorted(left_ids & right_ids)
        if not overlap:
            continue
        findings.append(
            Finding(
                severity,
                folder.name,
                rel(folder / "audit"),
                f"{left_role} and {right_role} roles share identity attestation(s): "
                f"{', '.join(overlap)}; this is single-agent review evidence, "
                "not independent-review certification",
            )
        )
    return findings


def check_human_review(
    folder: Path,
    status: str,
    payload: dict[str, Any],
    release: bool,
    *,
    review_log_present: bool | None = None,
) -> list[Finding]:
    review = payload.get("human_review")
    if not isinstance(review, dict):
        return [
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                "paper status has no `human_review` object",
            )
        ]
    findings: list[Finding] = []
    counts: dict[str, int] = {}
    for field in ("reviewed_rows", "total_rows", "stale_rows", "mismatch_rows"):
        value = review.get(field)
        if isinstance(value, bool) or not isinstance(value, int) or value < 0:
            findings.append(
                Finding(
                    "ERROR",
                    folder.name,
                    rel(folder / "status.json"),
                    f"human_review.{field} should be a nonnegative integer",
                )
            )
        else:
            counts[field] = value
    if len(counts) != 4:
        return findings
    reviewed = counts["reviewed_rows"]
    total = counts["total_rows"]
    if reviewed > total:
        findings.append(
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                "human_review.reviewed_rows is greater than total_rows",
            )
        )
    for field in ("stale_rows", "mismatch_rows"):
        if counts[field] > total:
            findings.append(
                Finding(
                    "ERROR",
                    folder.name,
                    rel(folder / "status.json"),
                    f"human_review.{field} is greater than total_rows",
                )
            )
    log_path = folder / ".review_traces" / "paper_theorem_validations.jsonl"
    log_present = log_path.exists() if review_log_present is None else review_log_present
    if reviewed > 0 and not log_present:
        findings.append(
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                f"status claims {reviewed} human-reviewed row(s), but no append-only review log is tracked at {rel(log_path)}",
            )
        )
    if status in CLOSEOUT_STATUSES and reviewed < total:
        findings.append(
            Finding(
                # A human packet is deliberately a review invitation and
                # evidence record, not a prerequisite for publishing a
                # mathematically closed paper.  Keep an incomplete packet
                # visible in every mode, but never manufacture a sign-off or
                # turn its absence into a release block.
                "WARN",
                folder.name,
                rel(folder / "status.json"),
                f"source-to-Lean human review is incomplete ({reviewed}/{total}); independent human review remains pending",
            )
        )
    return findings


def check_vacuous_assumptions(
    folder: Path,
    status: str,
    *,
    source_bytes_override: bytes | None | object = _UNSET,
) -> list[Finding]:
    path = folder / "Assumptions.lean"
    if source_bytes_override is _UNSET:
        try:
            source_text = path.read_text(encoding="utf-8")
        except OSError:
            return []
    elif source_bytes_override is None:
        return []
    elif isinstance(source_bytes_override, bytes):
        try:
            source_text = source_bytes_override.decode("utf-8")
        except UnicodeDecodeError:
            return [
                Finding(
                    finding_severity(status),
                    folder.name,
                    rel(path),
                    "Assumptions.lean is not valid UTF-8",
                )
            ]
    else:
        return []
    names = sorted(set(VACUOUS_ASSUMPTION_RE.findall(source_text)))
    if not names:
        return []
    return [
        Finding(
            finding_severity(status),
            folder.name,
            rel(path),
            "vacuous `Prop := True` assumption wrapper(s) can hide data/certificate boundaries: "
            + ", ".join(names),
        )
    ]


def active_papers_from_payload(payload: Mapping[str, Any]) -> set[str]:
    """Read active-paper routing from one already snapshotted config."""

    raw = payload.get("active_papers") or []
    return {str(item) for item in raw if str(item)} if isinstance(raw, list) else set()


def check_active_status(folder: Path, status: str, active: set[str]) -> list[Finding]:
    if folder.name not in active or status not in {"formalized", "formalized with caveat"}:
        return []
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(AUDIT_CONFIG),
            f"paper is skipped as active while claiming closeout status `{status}`",
        )
    ]


def lake_targets(
    *, raw_bytes_override: bytes | None | object = _UNSET
) -> tuple[set[str], set[str]]:
    try:
        if raw_bytes_override is _UNSET:
            source = LAKEFILE.read_text(encoding="utf-8")
        elif isinstance(raw_bytes_override, bytes):
            source = raw_bytes_override.decode("utf-8")
        else:
            return set(), set()
        payload = tomllib.loads(source)
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError):
        return set(), set()
    defaults = {str(item) for item in payload.get("defaultTargets") or []}
    libraries = {
        str(item.get("name"))
        for item in payload.get("lean_lib") or []
        if isinstance(item, dict) and item.get("name")
    }
    return defaults, libraries


def _configured_build_command_segments(command: str) -> list[list[str]]:
    """Return shell-command segments from a status ``build_target`` string.

    This is intentionally a narrow static parser: the audit never executes a
    status command, and only recognizes ordinary ``lake`` invocations separated
    by shell control operators. Malformed quoting simply yields no recognized
    focused route and therefore fails closed at closeout.
    """

    try:
        raw_segments = re.split(r"(?:&&|\|\||;)", command)
        return [shlex.split(segment) for segment in raw_segments if segment.strip()]
    except ValueError:
        return []


def _strip_environment_prefix(tokens: list[str]) -> list[str]:
    """Remove conventional leading environment assignments from one command."""

    index = 0
    assignment = re.compile(r"[A-Za-z_][A-Za-z0-9_]*=.*")
    while index < len(tokens) and assignment.fullmatch(tokens[index]):
        index += 1
    if index < len(tokens) and tokens[index] == "env":
        index += 1
        while index < len(tokens) and (
            assignment.fullmatch(tokens[index]) or tokens[index].startswith("-")
        ):
            index += 1
    return tokens[index:]


def configured_focused_build_routes(
    folder: Path, payload: Mapping[str, Any]
) -> tuple[set[str], bool]:
    """Find explicit paper-scoped build routes in ``status.build_target``.

    A closeout may build the registered paper library, a module beneath that
    library (including a forced ``+Paper.PaperInterface`` target), or directly
    elaborate the canonical paper interface with ``lake env lean``. The latter
    supports papers whose interface needs a separate direct elaboration after a
    shared-library build. Merely being listed in ``defaultTargets`` is not a
    paper build route.
    """

    command = payload.get("build_target")
    if not isinstance(command, str) or not command.strip():
        return set(), False

    library = folder.name
    interface_path = f"papers/{library}/PaperInterface.lean"
    targets: set[str] = set()
    direct_interface = False
    for raw_tokens in _configured_build_command_segments(command):
        tokens = _strip_environment_prefix(raw_tokens)
        if len(tokens) >= 3 and tokens[:2] == ["lake", "build"]:
            target = tokens[2]
            canonical_target = target[1:] if target.startswith("+") else target
            if canonical_target == library or canonical_target.startswith(
                library + "."
            ):
                targets.add(target)
            continue
        if len(tokens) >= 4 and tokens[:3] == ["lake", "env", "lean"]:
            direct_interface = direct_interface or any(
                argument.removeprefix("./") == interface_path
                for argument in tokens[3:]
            )
    return targets, direct_interface


def check_build_coverage(
    folder: Path,
    status: str,
    payload: dict[str, Any],
    _defaults: set[str],
    libraries: set[str],
) -> list[Finding]:
    if status not in CLOSEOUT_STATUSES:
        return []
    findings: list[Finding] = []
    if folder.name not in libraries:
        findings.append(
            Finding(
                "ERROR",
                folder.name,
                rel(LAKEFILE),
                f"closeout paper Lean library `{folder.name}` is not declared in `lean_lib`",
            )
        )
    focused_targets, direct_interface = configured_focused_build_routes(
        folder, payload
    )
    if not focused_targets and not direct_interface:
        findings.append(
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                "closeout paper needs an explicit focused `build_target`: "
                f"`lake build {folder.name}`, a `{folder.name}.…` module target, "
                f"or `lake env lean papers/{folder.name}/PaperInterface.lean`",
            )
        )
    return findings


def check_report_generator(
    *, raw_bytes_override: bytes | None | object = _UNSET
) -> list[Finding]:
    path = ROOT / "scripts" / "refresh_validation_report_audit_summaries.py"
    try:
        if raw_bytes_override is _UNSET:
            text = path.read_text(encoding="utf-8")
        elif isinstance(raw_bytes_override, bytes):
            text = raw_bytes_override.decode("utf-8")
        else:
            return []
    except (OSError, UnicodeDecodeError):
        return []
    if not re.search(r"holistic source-first audit PASS|audit \([^\n]+\): PASS", text):
        return []
    return [
        Finding(
            "ERROR",
            "REPO",
            rel(path),
            "report generator contains unconditional PASS certification text",
        )
    ]


@dataclass(frozen=True)
class _EvidenceRunContextSnapshotRoot(CurrentV11EvidenceSnapshotRoot):
    """Current transaction root plus the isolated historical builder."""

    allow_noncanonical_legacy_folder = True

    @classmethod
    def acquire(cls, folder: Path) -> _EvidenceRunContextSnapshotRoot:
        """Acquire one exact transaction under the repository root."""

        return super().acquire(folder, repository_root=ROOT)

    def _acquire_legacy_review_inputs(
        self,
    ) -> tuple[EvidenceJSONSnapshot, EvidenceJSONSnapshot]:
        """Freeze every historical raw-lane input and compatibility alias."""

        snapshot = self.transaction.snapshot
        for basename in sorted(AUDIT_SIDECARS):
            snapshot(self.folder / basename)
            snapshot(self.folder / "audit" / basename)

        paper_prerequisites_path = self.transaction.canonical_sidecar_path(
            "paper_semantic_prerequisites.json"
        )
        library_review_path = self.transaction.canonical_sidecar_path(
            "library_semantic_review.json"
        )
        paper_prerequisites = snapshot(paper_prerequisites_path)
        library_review = snapshot(library_review_path)
        snapshot(self.folder / "source.txt")

        if self.review_surface is not None:
            for section_name in (
                "llm_statement_review",
                "llm_paper_coverage_review",
                "llm_source_record_review",
            ):
                section = self.review_surface.get(section_name)
                if not isinstance(section, Mapping):
                    continue
                for field_name, raw_path in section.items():
                    if not str(field_name).endswith("_file"):
                        continue
                    configured_path, configured_error = resolve_paper_source_path(
                        self.folder, raw_path
                    )
                    if configured_path is not None and not configured_error:
                        snapshot(configured_path)

        statement_map_payload = self.statement_map_snapshot.payload
        raw_statement_items = (
            statement_map_payload.get("items")
            if isinstance(statement_map_payload, dict)
            else None
        )
        if isinstance(raw_statement_items, dict):
            for raw_item in raw_statement_items.values():
                if not isinstance(raw_item, dict):
                    continue
                corrected_target = raw_item.get("corrected_target")
                approval = (
                    corrected_target.get("approval")
                    if isinstance(corrected_target, dict)
                    else None
                )
                if isinstance(approval, dict):
                    approval_path = _paper_local_artifact_path(
                        self.folder, approval.get("artifact_path")
                    )
                    if approval_path is not None:
                        snapshot(approval_path)

        corrected_scope = author_approved_corrected_scope(self.status_payload)
        if isinstance(corrected_scope, dict):
            for reference_field in ("approval", "semantic_contract", "base_archive"):
                reference = corrected_scope.get(reference_field)
                if not isinstance(reference, dict):
                    continue
                artifact_path = _paper_local_artifact_path(
                    self.folder, reference.get("path")
                )
                if artifact_path is None and reference_field == "approval":
                    artifact_path = _paper_local_artifact_path(
                        self.folder, reference.get("artifact_path")
                    )
                if artifact_path is not None:
                    snapshot(artifact_path)

        try:
            if isinstance(self.status_snapshot.raw_bytes, bytes):
                from scripts.review_dashboard import (
                    required_dashboard_audit_input_paths,
                )

                selected_paths = required_dashboard_audit_input_paths(
                    self.folder,
                    status_bytes=self.status_snapshot.raw_bytes,
                    statement_map_bytes=self.statement_map_snapshot.raw_bytes,
                    repository_root=ROOT,
                )
                for selected_path in selected_paths:
                    snapshot(selected_path)
        except (OSError, RuntimeError, ValueError):
            # Malformed status/map inputs receive their ordinary closeout
            # findings. Do not derive a partial configured path set.
            pass

        snapshot(LAKEFILE)
        snapshot(ROOT / "scripts" / "refresh_validation_report_audit_summaries.py")
        snapshot(self.folder / "Assumptions.lean")
        snapshot(
            self.folder / ".review_traces" / "paper_theorem_validations.jsonl"
        )
        return paper_prerequisites, library_review

    def _configured_source_record_path(
        self,
        *,
        config_field: str,
        default_basename: str,
    ) -> tuple[Path, str]:
        source_record_review = (
            self.review_surface.get("llm_source_record_review")
            if self.review_surface is not None
            else None
        )
        raw_path = (
            source_record_review.get(config_field)
            if isinstance(source_record_review, Mapping)
            else None
        )
        if not isinstance(raw_path, str) or not raw_path.strip():
            return self.transaction.canonical_sidecar_path(default_basename), ""
        configured, error = source_record_review_sidecar_path(
            self.folder,
            self.status_payload,
            config_field=config_field,
            default_basename=default_basename,
        )
        if configured is None:
            return self.transaction.canonical_sidecar_path(default_basename), error
        self.transaction.snapshot(configured)
        return configured, error

    def build_legacy(
        self,
        *,
        diagnostics: MutableMapping[str, int] | None,
    ) -> LegacyEvidenceRunContext:
        """Acquire historical authority and dispatch its typed derivation."""

        snapshot = self.transaction.snapshot
        audit_path, audit_path_error = self._configured_source_record_path(
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
        match_path, match_path_error = self._configured_source_record_path(
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
        audit_snapshot = snapshot(audit_path)
        match_snapshot = snapshot(match_path)

        for basename in SOURCE_RECORD_OPTIONAL_AUTHORITY_SIDECARS:
            snapshot(self.folder / basename)
            snapshot(self.folder / "audit" / basename)
        revalidation_artifact = snapshot(
            self.folder
            / "audit"
            / "source_record_semantic_contract_revalidation.json"
        )
        revalidation_authority = snapshot(
            self.folder / "audit" / "lean_signature_manifest_cache_authority.json"
        )
        semantic_reuse_authority = snapshot(
            self.folder / "audit" / SOURCE_RECORD_SEMANTIC_VALIDATION_BASENAME
        )
        snapshot(
            self.folder / SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
        )
        snapshot(
            self.folder
            / "audit"
            / SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
        )
        regularity_path = (
            self.folder / CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE
        )
        snapshot(regularity_path)

        paper_prerequisites, library_review = self._acquire_legacy_review_inputs()

        try:
            from scripts.source_record_semantic_rebind import (
                SOURCE_RECORD_SEMANTIC_REBIND_FILENAME,
                source_record_semantic_rebind_declared_provenance_paths,
            )

            provenance_queue = [
                snapshot(
                    self.folder / "audit" / SOURCE_RECORD_SEMANTIC_REBIND_FILENAME
                ),
                snapshot(self.folder / SOURCE_RECORD_SEMANTIC_REBIND_FILENAME),
            ]
            seen_provenance_payload_paths: set[Path] = set()
            while provenance_queue:
                provenance_snapshot = provenance_queue.pop()
                try:
                    provenance_key = provenance_snapshot.path.resolve()
                except (OSError, RuntimeError):
                    continue
                if provenance_key in seen_provenance_payload_paths:
                    continue
                seen_provenance_payload_paths.add(provenance_key)
                if len(seen_provenance_payload_paths) > 256:
                    raise ValueError("semantic rebind provenance graph is too large")
                payload = provenance_snapshot.payload
                if not isinstance(payload, Mapping):
                    continue
                for provenance_path in (
                    source_record_semantic_rebind_declared_provenance_paths(
                        payload,
                        paper_dir=self.folder,
                    )
                ):
                    declared_snapshot = snapshot(provenance_path)
                    if declared_snapshot.payload is not None:
                        provenance_queue.append(declared_snapshot)
        except (OSError, RuntimeError, ValueError):
            # The replay validator rejects malformed provenance. The acquired
            # root remains watched and no invalid path grants authority.
            pass

        common_context = self._common_context(
            protocol_core_snapshots=(audit_snapshot, match_snapshot)
        )
        return _build_legacy_evidence_run_context(
            _LegacyEvidenceRunContextBuildInputs(
                common_context=common_context,
                audit_path=audit_path,
                audit_path_error=audit_path_error,
                match_path_error=match_path_error,
                audit_snapshot=audit_snapshot,
                match_snapshot=match_snapshot,
                paper_semantic_prerequisites_snapshot=paper_prerequisites,
                library_semantic_review_snapshot=library_review,
                semantic_contract_revalidation_artifact_snapshot=(
                    revalidation_artifact
                ),
                semantic_contract_revalidation_authority_snapshot=(
                    revalidation_authority
                ),
                semantic_reuse_authority_snapshot=semantic_reuse_authority,
                regularity_path=regularity_path,
                snapshots_by_path=MappingProxyType(
                    dict(self.transaction.snapshots_by_path)
                ),
            ),
            diagnostics=diagnostics,
        )


@dataclass(frozen=True)
class _LegacyEvidenceRunContextBuildInputs:
    """Already-acquired immutable inputs for the historical protocol builder."""

    common_context: _CommonEvidenceRunContextInputs
    audit_path: Path
    audit_path_error: str
    match_path_error: str
    audit_snapshot: EvidenceJSONSnapshot
    match_snapshot: EvidenceJSONSnapshot
    paper_semantic_prerequisites_snapshot: EvidenceJSONSnapshot
    library_semantic_review_snapshot: EvidenceJSONSnapshot
    semantic_contract_revalidation_artifact_snapshot: EvidenceJSONSnapshot
    semantic_contract_revalidation_authority_snapshot: EvidenceJSONSnapshot
    semantic_reuse_authority_snapshot: EvidenceJSONSnapshot
    regularity_path: Path
    snapshots_by_path: Mapping[Path, EvidenceJSONSnapshot]


def _build_legacy_evidence_run_context(
    inputs: _LegacyEvidenceRunContextBuildInputs,
    *,
    diagnostics: MutableMapping[str, int] | None,
) -> LegacyEvidenceRunContext:
    """Derive historical raw-source state from one frozen input transaction."""

    common_context = inputs.common_context
    folder = common_context.folder
    status = common_context.status
    status_snapshot = common_context.status_snapshot
    status_payload = status_snapshot.payload or {}
    statement_map_snapshot = common_context.statement_map_snapshot
    statement_map_path = statement_map_snapshot.path
    audit_path = inputs.audit_path
    audit_path_error = inputs.audit_path_error
    match_path_error = inputs.match_path_error
    audit_snapshot = inputs.audit_snapshot
    match_snapshot = inputs.match_snapshot
    paper_semantic_prerequisites_snapshot = (
        inputs.paper_semantic_prerequisites_snapshot
    )
    library_semantic_review_snapshot = inputs.library_semantic_review_snapshot
    semantic_contract_revalidation_artifact_snapshot = (
        inputs.semantic_contract_revalidation_artifact_snapshot
    )
    semantic_contract_revalidation_authority_snapshot = (
        inputs.semantic_contract_revalidation_authority_snapshot
    )
    semantic_reuse_authority_snapshot = inputs.semantic_reuse_authority_snapshot
    regularity_path = inputs.regularity_path
    snapshots_by_path = inputs.snapshots_by_path

    audit_payload = audit_snapshot.payload if audit_snapshot is not None else None
    watched_input_digest = ""
    identity_error = ""
    current_surface = False
    semantic_contract_revalidation = None
    semantic_contract_revalidation_error = ""
    semantic_reuse_authority: CurrentSemanticReuseAuthority | None = None
    if isinstance(audit_payload, dict):
        assert audit_snapshot is not None
        assert match_snapshot is not None
        current_surface = (
            str(audit_payload.get("source_record_policy_version") or "").strip()
            == CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
            or str(audit_payload.get("prompt_version") or "").strip()
            == CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
        )
        if current_surface:
            try:
                replay = _semantic_contract_revalidation_module()
                (
                    semantic_contract_revalidation,
                    semantic_contract_revalidation_error,
                ) = replay.semantic_contract_revalidation_projection(
                    paper_dir=folder,
                    paper=folder.name,
                    raw_audit=audit_payload,
                    raw_audit_raw_bytes=audit_snapshot.raw_bytes,
                    statement_map_payload=statement_map_snapshot.payload,
                    statement_map_raw_bytes=statement_map_snapshot.raw_bytes,
                    paper_prerequisites_payload=(
                        paper_semantic_prerequisites_snapshot.payload
                    ),
                    paper_prerequisites_raw_bytes=(
                        paper_semantic_prerequisites_snapshot.raw_bytes
                    ),
                    library_semantic_review_payload=(
                        library_semantic_review_snapshot.payload
                    ),
                    library_semantic_review_raw_bytes=(
                        library_semantic_review_snapshot.raw_bytes
                    ),
                    status_payload=status_snapshot.payload,
                    status_raw_bytes=status_snapshot.raw_bytes,
                    artifact_payload=(
                        semantic_contract_revalidation_artifact_snapshot.payload
                    ),
                    artifact_raw_bytes=(
                        semantic_contract_revalidation_artifact_snapshot.raw_bytes
                    ),
                    authority_payload=(
                        semantic_contract_revalidation_authority_snapshot.payload
                    ),
                    authority_raw_bytes=(
                        semantic_contract_revalidation_authority_snapshot.raw_bytes
                    ),
                )
            except Exception as error:  # noqa: BLE001 - authority fails closed.
                semantic_contract_revalidation = None
                semantic_contract_revalidation_error = (
                    "could not validate semantic-contract revalidation: "
                    f"{type(error).__name__}: {error}"
                )
        # Validate the cheap, byte-pinned replay before spawning the expensive
        # current-input fingerprint subprocess. A malformed optional replay
        # cannot authorize anything, so failing before that subprocess saves a
        # full closeout wait without changing accepted evidence.
        fingerprint_error = ""
        if not current_surface or not semantic_contract_revalidation_error:
            _increment_diagnostic(diagnostics, EVIDENCE_DIAGNOSTIC_WATCH_DIGESTS)
            watched_input_digest = _source_record_identity_process_watch_digest(
                folder, audit_payload=audit_payload
            )
            _increment_diagnostic(
                diagnostics, EVIDENCE_DIAGNOSTIC_IDENTITY_VALIDATIONS
            )
            if current_surface and audit_snapshot.sha256:
                semantic_reuse_authority = load_current_semantic_reuse_authority(
                    root=ROOT,
                    paper_dir=folder,
                    raw_audit_file_sha256=audit_snapshot.sha256,
                    raw_audit=audit_payload,
                    authority_raw_bytes=(
                        semantic_reuse_authority_snapshot.raw_bytes
                    ),
                )
            # The authority loader has independently rebound the successful
            # Lean result to every current configured row and every exact input
            # watched by that pass.  Replaying the historical whole-import
            # byte validator here would redo the same semantic work and would
            # falsely stale on unrelated imported-file bytes.
            if current_surface and semantic_reuse_authority is None:
                fingerprint_error = _source_record_current_input_fingerprint_error(
                    folder,
                    audit_payload,
                    verify_watch_inputs=False,
                    semantic_contract_revalidation=(
                        semantic_contract_revalidation
                    ),
                )
        identity_error = _source_record_audit_identity_error(
            audit_payload,
            expected_paper_statement_map_sha256=(
                statement_map_snapshot.sha256 or ""
            ),
            folder=folder,
            prevalidated_current_input_fingerprint_error=fingerprint_error,
            semantic_contract_revalidation=semantic_contract_revalidation,
            prevalidated_semantic_contract_revalidation_error=(
                semantic_contract_revalidation_error
            ),
            semantic_reuse_authority=semantic_reuse_authority,
        )

    corrected_findings: tuple[Finding, ...] = ()
    corrected_model_field_items: dict[str, dict[str, Any]] = {}
    source_record_identity_context: object | None = None
    legacy_source_record_identity_current = bool(
        isinstance(audit_payload, dict) and not identity_error
    )
    if legacy_source_record_identity_current:
        assert isinstance(audit_payload, dict)
        assert audit_snapshot is not None
        # The strict gate above has already replayed the external-artifact
        # fingerprint for this exact snapshot.  Issue a nonserialized context
        # only if canonical raw/map/watch state still agrees, then pass it to
        # every nested overlay loader below instead of replaying the helper.
        canonical_raw_path = folder / "audit" / "source_record_audit.json"
        try:
            snapshot_is_canonical_raw = (
                audit_snapshot.path.resolve() == canonical_raw_path.resolve()
            )
        except (OSError, RuntimeError):
            snapshot_is_canonical_raw = False
        source_record_identity_context = _issue_current_source_record_identity_context(
            folder,
            folder.name,
            audit_payload,
            source_record_identity_error=identity_error,
            watched_input_digest=watched_input_digest or None,
            trusted_canonical_raw_file_sha256=(
                audit_snapshot.sha256 if snapshot_is_canonical_raw else None
            ),
        )
    if legacy_source_record_identity_current:
        assert isinstance(audit_payload, dict)
        _increment_diagnostic(diagnostics, EVIDENCE_DIAGNOSTIC_CORRECTED_SCOPE)
        corrected_findings = tuple(
            _corrected_model_scope_contract_findings(
                folder,
                status,
                status_payload,
                audit_payload_override=audit_payload,
                prevalidated_source_record_identity_error=identity_error,
                validated_field_items_out=corrected_model_field_items,
                artifact_snapshots_override=snapshots_by_path,
            )
        )
    scope = author_approved_corrected_scope(status_payload)
    scope_role = None
    scope_role_error = ""
    if scope is not None:
        scope_role, scope_role_error = corrected_model_scope_role(scope)
    corrected_scope_current = bool(
        legacy_source_record_identity_current
        and scope is not None
        and not scope_role_error
        and scope_role == WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE
        and not corrected_findings
    )

    administrative_rebind = None
    administrative_rebind_path = None
    administrative_rebind_error = ""
    regularity_context = None
    regularity_context_error = ""
    auxiliary_routing_context = None
    auxiliary_routing_context_error = ""
    if legacy_source_record_identity_current:
        assert isinstance(audit_payload, dict)
        regularity_snapshot = snapshots_by_path.get(regularity_path.resolve())
        regularity_source_snapshot = snapshots_by_path.get(
            (folder / "source.txt").resolve()
        )
        regularity_context, regularity_context_error = (
            load_configured_assumption_formalization_regularity_context(
                folder,
                audit_payload,
                status_payload=status_payload,
                ledger_bytes_override=(
                    regularity_snapshot.raw_bytes
                    if regularity_snapshot is not None
                    else None
                ),
                source_artifact_sha256_override=(
                    regularity_source_snapshot.sha256
                    if regularity_source_snapshot is not None
                    else None
                ),
            )
        )
        if current_surface:
            rebind_path, _rebind_path_error = source_record_review_sidecar_path(
                folder,
                status_payload,
                config_field=(
                    "source_record_administrative_projection_rebind_file"
                ),
                default_basename=(
                    SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
                ),
            )
            rebind_snapshot = (
                snapshots_by_path.get(rebind_path.resolve())
                if rebind_path is not None
                else None
            )
            (
                administrative_rebind,
                administrative_rebind_path,
                administrative_rebind_error,
            ) = source_record_administrative_projection_rebind_context(
                folder,
                status_payload,
                audit_path=audit_path,
                audit_payload=audit_payload,
                statement_map_path=statement_map_path,
                statement_map=statement_map_snapshot.payload,
                receipt_bytes_override=(
                    rebind_snapshot.raw_bytes
                    if rebind_snapshot is not None
                    else None
                ),
                raw_audit_bytes_override=audit_snapshot.raw_bytes,
                statement_map_bytes_override=statement_map_snapshot.raw_bytes,
            )
        if (
            str(audit_payload.get("prompt_version") or "").strip()
            == CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
            and str(audit_payload.get("paper") or "").strip() == folder.name
        ):
            (
                auxiliary_routing_context,
                auxiliary_routing_context_error,
            ) = current_auxiliary_routing_context(
                root=ROOT,
                paper_dir=folder,
                paper=folder.name,
                audit_payload=audit_payload,
                verify_current_raw_identity=False,
            )

    current_judgments: dict[str, dict[str, Any]] = {}
    if legacy_source_record_identity_current:
        assert isinstance(audit_payload, dict)
        _increment_diagnostic(diagnostics, EVIDENCE_DIAGNOSTIC_CURRENT_JUDGMENTS)
        current_judgments = _current_source_record_judgment_items(
            audit_payload,
            match_snapshot.payload or {},
            expected_paper_statement_map_sha256=(
                statement_map_snapshot.sha256 or ""
            ),
            folder=folder,
            prevalidated_source_record_identity_error=identity_error,
            statement_map_override=statement_map_snapshot.payload,
            status_payload_override=status_payload,
            configured_assumption_regularity_context_override=regularity_context,
            source_record_identity_context=source_record_identity_context,
        )
    frozen_current_judgments = _freeze_json(
        current_judgments,
        preserve_dict_subclasses=True,
    )
    assert isinstance(frozen_current_judgments, dict)
    frozen_corrected_model_field_items = _freeze_json(
        corrected_model_field_items,
        preserve_dict_subclasses=True,
    )
    assert isinstance(frozen_corrected_model_field_items, dict)

    assert audit_snapshot is not None
    assert match_snapshot is not None
    legacy_source_record_state = LegacySourceRecordState(
        inputs=LegacySourceRecordInputs(
            audit_snapshot=audit_snapshot,
            match_snapshot=match_snapshot,
            audit_path_error=audit_path_error,
            match_path_error=match_path_error,
        ),
        source_record_identity_error=identity_error,
        semantic_contract_revalidation=semantic_contract_revalidation,
        semantic_contract_revalidation_error=(
            semantic_contract_revalidation_error
        ),
        corrected_scope_findings=corrected_findings,
        corrected_scope_current=corrected_scope_current,
        corrected_model_field_items=MappingProxyType(
            frozen_corrected_model_field_items
        ),
        administrative_projection_rebind=administrative_rebind,
        administrative_projection_rebind_path=administrative_rebind_path,
        administrative_projection_rebind_error=administrative_rebind_error,
        configured_assumption_regularity_context=regularity_context,
        configured_assumption_regularity_context_error=(regularity_context_error),
        current_source_record_judgments=MappingProxyType(
            frozen_current_judgments
        ),
        auxiliary_routing_context=auxiliary_routing_context,
        auxiliary_routing_context_error=auxiliary_routing_context_error,
        watched_input_digest=watched_input_digest,
        source_record_identity_context=source_record_identity_context,
        semantic_reuse_authority=semantic_reuse_authority,
    )

    return common_context.issue_legacy(legacy_source_record_state)


def build_evidence_run_context(
    folder: Path,
    *,
    diagnostics: MutableMapping[str, int] | None = None,
    v11_lean_review_graph_reference: Mapping[str, object] | None = None,
    reuse_v11_graph_checkpoint: bool = False,
) -> EvidenceRunContext:
    """Select and build one exact, nonpersistent evidence transaction."""

    _increment_diagnostic(diagnostics, EVIDENCE_DIAGNOSTIC_CONTEXTS)
    snapshot_root = _EvidenceRunContextSnapshotRoot.acquire(folder)
    if snapshot_root.v11_selected:
        if reuse_v11_graph_checkpoint and v11_lean_review_graph_reference is None:
            return snapshot_root.build_v11_with_graph_checkpoint()
        return snapshot_root.build_v11(v11_lean_review_graph_reference)
    if v11_lean_review_graph_reference is not None:
        raise ValueError(
            "a v11 Lean review graph carrier was supplied for a non-v11 paper"
        )
    return snapshot_root.build_legacy(diagnostics=diagnostics)


def source_record_legacy_semantic_complement_findings(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext,
) -> list[Finding]:
    """Run generated raw semantic dispositions only in the legacy lane.

    A selected v11 transaction owns source-to-Spec and prerequisite semantics.
    Its own failures remain blocking, but cannot cause the deliberately
    unacquired raw source-record carrier to become a competing acceptance path
    or veto.
    """

    if context.v11_lean_claim_graph_selected:
        return []
    return [
        *source_record_semantic_target_disposition_findings(
            folder, status, context=context
        ),
        *source_record_input_target_disposition_findings(
            folder, status, context=context
        ),
        *source_record_recursive_field_target_disposition_findings(
            folder, status, context=context
        ),
    ]


def evidence_run_context_mutation_findings(
    context: EvidenceRunContext,
    *,
    diagnostics: MutableMapping[str, int] | None = None,
) -> list[Finding]:
    """Fail closed if any content bound to a run context changed during use."""

    if not isinstance(context, EvidenceRunContext) or not context.issued_by_builder:
        raw_folder = getattr(context, "folder", None)
        paper = raw_folder.name if isinstance(raw_folder, Path) else "unknown"
        return [
            Finding(
                "ERROR",
                paper,
                "papers",
                "evidence transaction was not issued by the exact snapshot builder",
            )
        ]

    changed_paths = list(context.changed_input_paths())

    watched_changed = False
    legacy_state = context.legacy_source_record_state
    if legacy_state is not None and legacy_state.watched_input_digest:
        _increment_diagnostic(diagnostics, EVIDENCE_DIAGNOSTIC_WATCH_DIGESTS)
        audit_payload = legacy_state.inputs.audit_snapshot.payload
        current_watch_digest = _source_record_identity_process_watch_digest(
            context.folder,
            audit_payload=audit_payload,
        )
        watched_changed = current_watch_digest != legacy_state.watched_input_digest
    if not changed_paths and not watched_changed:
        return []

    _increment_diagnostic(diagnostics, EVIDENCE_DIAGNOSTIC_INPUT_MUTATIONS)
    details: list[str] = []
    if changed_paths:
        details.append(
            "exact inputs changed: "
            + ", ".join(rel(path) for path in changed_paths[:5])
            + ("; ..." if len(changed_paths) > 5 else "")
        )
    if watched_changed:
        details.append("source-record producer/source watch digest changed")
    return [
        Finding(
            "ERROR",
            context.folder.name,
            rel(context.folder / "status.json"),
            "evidence inputs changed during the paper audit transaction; "
            "discard all run-scoped authorization results ("
            + "; ".join(details)
            + ")",
        )
    ]


def _legacy_evidence_integrity_findings(
    folder: Path,
    context: LegacyEvidenceRunContext,
    *,
    include_source_obligations: bool,
    require_source_bytes: bool,
) -> list[Finding]:
    """Run the complete historical raw-source lane for a legacy transaction."""

    status = context.status
    payload = context.status_payload
    findings = historical_statement_manifest_replay_evidence_findings(
        folder, status, context=context
    )
    findings.extend(
        coverage_row_signature_pin_findings(folder, status, context=context)
    )
    findings.extend(
        corrected_target_coverage_findings(folder, status, context=context)
    )
    findings.extend(check_status_alignment(folder, status, context=context))
    findings.extend(context.corrected_scope_findings)
    findings.extend(check_source_record_configured_rows(folder, context=context))
    findings.extend(
        check_source_premise_consistency(folder, status, context=context)
    )
    findings.extend(
        check_source_record_judgments(
            folder,
            status,
            require_source_bytes=require_source_bytes,
            context=context,
        )
    )
    findings.extend(
        source_record_legacy_semantic_complement_findings(
            folder, status, context=context
        )
    )
    findings.extend(
        explicit_source_route_semantic_model_findings(
            folder,
            status,
            payload,
            require_source_bytes=require_source_bytes,
            context=context,
        )
    )
    findings.extend(
        check_plain_formalized_unresolved_source_record_math(
            folder, status, context=context
        )
    )
    findings.extend(
        check_full_closeout_open_semantic_model_dimensions(
            folder, status, context=context
        )
    )
    if include_source_obligations:
        findings.extend(
            check_current_unresolved_source_record_math(
                folder, status, context=context
            )
        )
    return findings


def current_v11_source_route_findings(
    folder: Path,
    status: str,
    *,
    context: V11EvidenceRunContext,
) -> list[Finding]:
    """Adapt the Lean-owned current route gate to evidence findings."""

    surface = context.retained_v11_review_surface()
    if surface is None:
        return [
            Finding(
                finding_severity(status),
                folder.name,
                rel(folder / "PaperInterface.lean"),
                "current v11 evidence has no retained Lean source-route surface",
            )
        ]
    errors = v11_source_route_gate.current_v11_source_route_errors(
        paper_id=folder.name,
        status_payload=context.status_payload,
        source_map=context.statement_map,
        surface=surface,
    )
    return [
        Finding(
            finding_severity(status),
            folder.name,
            rel(folder / "audit" / "paper_statement_map.json"),
            error,
        )
        for error in errors
    ]


def _legacy_evidence_integrity_prefix_findings(
    folder: Path,
    context: EvidenceRunContext,
    *,
    require_source_bytes: bool,
) -> list[Finding]:
    """Evaluate common source families before historical protocol checks."""

    status = context.status
    payload = context.status_payload
    findings = check_duplicate_sidecars(folder, status, context=context)
    findings.extend(check_placeholder_evidence(folder, status, context=context))
    findings.extend(
        check_source_manifest(
            folder,
            status,
            require_source_bytes=require_source_bytes,
            context=context,
        )
    )
    findings.extend(
        semantic_contract_inventory_findings(
            folder,
            status,
            require_source_bytes=require_source_bytes,
            context=context,
        )
    )
    findings.extend(
        source_proof_fidelity_findings(
            folder,
            status,
            payload,
            require_source_bytes=require_source_bytes,
            context=context,
        )
    )
    return findings


def _legacy_evidence_integrity_suffix_findings(
    folder: Path,
    context: EvidenceRunContext,
    *,
    release: bool,
    active: set[str],
    defaults: set[str],
    libraries: set[str],
) -> list[Finding]:
    """Evaluate metadata shared by the historical diagnostic lane."""

    status = context.status
    payload = context.status_payload
    findings: list[Finding] = []
    findings.extend(
        check_validator_independence(folder, status, release, context=context)
    )
    review_log_snapshot = context.json_snapshot(
        folder / ".review_traces" / "paper_theorem_validations.jsonl"
    )
    assumptions_snapshot = context.json_snapshot(folder / "Assumptions.lean")
    findings.extend(
        check_human_review(
            folder,
            status,
            payload,
            release,
            review_log_present=(
                review_log_snapshot.sha256 is not None
                if review_log_snapshot is not None
                else None
            ),
        )
    )
    findings.extend(
        check_vacuous_assumptions(
            folder,
            status,
            source_bytes_override=(
                assumptions_snapshot.raw_bytes
                if assumptions_snapshot is not None
                else _UNSET
            ),
        )
    )
    findings.extend(check_active_status(folder, status, active))
    findings.extend(
        check_build_coverage(folder, status, payload, defaults, libraries)
    )
    return findings


def current_v11_evidence_integrity_findings(
    folder: Path,
    context: V11EvidenceRunContext,
    *,
    release: bool,
    require_source_bytes: bool,
    active: set[str],
    defaults: set[str],
    libraries: set[str],
) -> list[Finding]:
    """Compatibility diagnostic backed by the one current family registry."""

    from scripts.current_closeout.evidence_gate import (
        current_evidence_transaction_findings,
    )

    return current_evidence_transaction_findings(
        folder=folder,
        context=context,
        release=release,
        require_source_bytes=require_source_bytes,
        active=active,
        defaults=defaults,
        libraries=libraries,
    )


def _run_evidence_integrity(
    paper_filter: str | None,
    release: bool,
    include_source_obligations: bool = False,
    *,
    public_complete: bool = False,
    require_source_bytes: bool = True,
    diagnostics: MutableMapping[str, int] | None = None,
    context: EvidenceRunContext | None = None,
    finalize_context: bool,
    require_current_final_closure_receipt: bool,
) -> list[Finding]:
    folders = paper_dirs(paper_filter, public_complete=public_complete)
    if context is not None and (
        not isinstance(context, EvidenceRunContext)
        or not context.issued_by_builder
    ):
        return [
            Finding(
                "ERROR",
                paper_filter or "REPO",
                "papers",
                "run-scoped evidence context was not issued by the exact "
                "evidence snapshot builder",
            )
        ]
    report_snapshot = (
        context.json_snapshot(
            ROOT / "scripts" / "refresh_validation_report_audit_summaries.py"
        )
        if context is not None
        else None
    )
    lake_snapshot = context.json_snapshot(LAKEFILE) if context is not None else None
    findings = check_report_generator(
        raw_bytes_override=(
            report_snapshot.raw_bytes if report_snapshot is not None else _UNSET
        )
    )
    defaults, libraries = lake_targets(
        raw_bytes_override=(
            lake_snapshot.raw_bytes if lake_snapshot is not None else _UNSET
        )
    )
    if paper_filter and not folders:
        return findings + [
            Finding("ERROR", paper_filter, "papers", "paper folder/status.json not found")
        ]
    if context is not None and (
        len(folders) != 1 or folders[0].resolve() != context.folder
    ):
        return findings + [
            Finding(
                "ERROR",
                paper_filter or "REPO",
                "papers",
                "run-scoped evidence context does not match the selected paper",
            )
        ]
    for folder in folders:
        if context is None and require_current_final_closure_receipt:
            graph_native_findings = graph_native_closure_fast_path_findings(
                folder,
                release=release,
                require_source_bytes=require_source_bytes,
            )
            if graph_native_findings is not None:
                findings.extend(graph_native_findings)
                continue
        selected_context = context or build_evidence_run_context(
            folder, diagnostics=diagnostics, reuse_v11_graph_checkpoint=True,
        )
        if not isinstance(
            selected_context, (V11EvidenceRunContext, LegacyEvidenceRunContext)
        ):
            findings.append(
                Finding(
                    "ERROR",
                    folder.name,
                    rel(folder / "status.json"),
                    "evidence transaction has an unsupported protocol context "
                    f"type: {type(selected_context).__name__}",
                )
            )
            continue
        active = active_papers_from_payload(
            selected_context.audit_config_snapshot.payload or {}
        )
        if isinstance(selected_context, V11EvidenceRunContext):
            findings.extend(
                current_v11_evidence_integrity_findings(
                    folder,
                    selected_context,
                    release=release,
                    require_source_bytes=require_source_bytes,
                    active=active,
                    defaults=defaults,
                    libraries=libraries,
                )
            )
        else:
            findings.extend(
                _legacy_evidence_integrity_prefix_findings(
                    folder,
                    selected_context,
                    require_source_bytes=require_source_bytes,
                )
            )
            findings.extend(
                _legacy_evidence_integrity_findings(
                    folder,
                    selected_context,
                    include_source_obligations=include_source_obligations,
                    require_source_bytes=require_source_bytes,
                )
            )
            findings.extend(
                _legacy_evidence_integrity_suffix_findings(
                    folder,
                    selected_context,
                    release=release,
                    active=active,
                    defaults=defaults,
                    libraries=libraries,
                )
            )
        # A standalone evidence audit validates the already-issued canonical
        # receipt. The consolidated closeout transaction deliberately omits
        # this check because its finalizer issues the receipt after every
        # evidence, provenance, and focused-build stage passes.
        if require_current_final_closure_receipt:
            findings.extend(
                final_closure_receipt_findings(
                    folder, require_source_bytes=require_source_bytes
                )
            )
        if finalize_context:
            findings.extend(
                evidence_run_context_mutation_findings(
                    selected_context, diagnostics=diagnostics
                )
            )
    return unique_findings(findings)


def run(
    paper_filter: str | None,
    release: bool,
    include_source_obligations: bool = False,
    *,
    public_complete: bool = False,
    require_source_bytes: bool = True,
    diagnostics: MutableMapping[str, int] | None = None,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Run evidence validation and always finalize its transaction."""

    return _run_evidence_integrity(
        paper_filter,
        release,
        include_source_obligations,
        public_complete=public_complete,
        require_source_bytes=require_source_bytes,
        diagnostics=diagnostics,
        context=context,
        finalize_context=True,
        require_current_final_closure_receipt=True,
    )


def run_for_consolidated_closeout_transaction(
    paper_filter: str,
    release: bool,
    include_source_obligations: bool = False,
    *,
    require_source_bytes: bool = True,
    diagnostics: MutableMapping[str, int] | None = None,
    context: EvidenceRunContext,
) -> list[Finding]:
    """Run inside a closeout whose owner will perform the final mutation check.

    This deliberately separate API prevents an ordinary caller from disabling
    finalization with a Boolean option and mistaking an unfinalized list for a
    complete audit result. ``audit_repository`` owns the only production use,
    finalizes the same context after every repository-level consumer, and then
    hands the successful transaction to the canonical receipt finalizer.  The
    prior receipt is therefore not an input gate for this lane.
    """

    if isinstance(context, V11EvidenceRunContext):
        from scripts.current_closeout.evidence_gate import (
            run_current_evidence_gate,
        )

        return run_current_evidence_gate(
            repository_root=ROOT,
            paper_id=paper_filter,
            release=release,
            require_source_bytes=require_source_bytes,
            diagnostics=diagnostics,
            context=context,
        )

    findings = _run_evidence_integrity(
        paper_filter,
        release,
        include_source_obligations,
        public_complete=False,
        require_source_bytes=require_source_bytes,
        diagnostics=diagnostics,
        context=context,
        finalize_context=False,
        require_current_final_closure_receipt=False,
    )
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--paper", help="restrict the audit to one paper folder")
    selection.add_argument(
        "--public-complete",
        action="store_true",
        help=(
            "audit only papers explicitly marked repository_visibility=public "
            "whose mathematical status is formalized or formalized with caveat; "
            "fail if any paper omits repository visibility"
        ),
    )
    parser.add_argument(
        "--release",
        action="store_true",
        help="treat missing independent validator attestations as blocking release errors",
    )
    parser.add_argument(
        "--include-source-obligations",
        action="store_true",
        help=(
            "include non-blocking WARN findings for current source-record items "
            "classified as unresolved_assumed_math"
        ),
    )
    parser.add_argument(
        "--allow-missing-source-bytes",
        action="store_true",
        help=(
            "structural public-checkout mode: require a safe canonical path and "
            "SHA-256 but warn, rather than certify, when licensed source bytes are absent"
        ),
    )
    parser.add_argument("--json", action="store_true", help="emit findings as JSON")
    args = parser.parse_args()

    try:
        selected = paper_dirs(args.paper, public_complete=args.public_complete)
    except ValueError as exc:
        parser.error(str(exc))
    if args.public_complete and not selected:
        parser.error("no explicitly public fully formalized papers found")
    findings = run(
        args.paper,
        args.release,
        args.include_source_obligations,
        public_complete=args.public_complete,
        require_source_bytes=not args.allow_missing_source_bytes,
    )
    if args.json:
        print(json.dumps([asdict(finding) for finding in findings], indent=2, sort_keys=True))
    else:
        for finding in findings:
            print(finding.format())
        errors = sum(finding.severity == "ERROR" for finding in findings)
        warnings = sum(finding.severity == "WARN" for finding in findings)
        print(f"Evidence-integrity audit: {errors} error(s), {warnings} warning(s)")
    return 1 if any(finding.severity == "ERROR" for finding in findings) else 0


if __name__ == "__main__":
    sys.exit(main())
