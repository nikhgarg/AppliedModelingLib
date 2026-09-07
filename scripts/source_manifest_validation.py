"""Shared source-only statement-map validation.

This owner validates source pins, exact anchors, inventory/scope, semantic
contexts, approved corrections/exclusions, fidelity ledgers, and surface schemas.
It neither discovers Lean declarations nor issues acceptance evidence.
Frozen transactions retain the existing nominal context and Finding types.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
from collections import Counter
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping

from scripts import source_claim_atom_schema
from scripts.obligation_routes import (
    ObligationRouteError as CloseoutPipelineError,
    EvidenceRouteSet,
    typed_route_validation_required,
)
from scripts.configured_paper_inputs import (
    configured_source_proof_fidelity_ledger_path,
)
from scripts.corrected_target_identity import (
    CORRECTED_TARGET_APPROVAL_PROTOCOL,
    corrected_target_record_digest as _shared_corrected_target_record_digest,
    corrected_target_approval_artifact_error,
    corrected_target_approval_excerpt_material,
    corrected_target_original_artifact_path_error,
    corrected_target_review_digest,
)
from scripts.evidence_run_context import (
    EvidenceRunContext,
    Finding,
    run_scoped_cached_value as _run_scoped_cached_value,
    run_scoped_validation_findings as _run_scoped_validation_findings,
)
from scripts.source_archive_surface import (
    source_archive_surface_validation_issues,
)
from scripts.source_artifact_companion import (
    semantic_review_source_identity,
    source_text_companion_validation_issues,
)
from scripts.source_claim_policy import (
    NON_NAMED_COMPUTATIONAL_ILLUSTRATION,
    USER_APPROVED_SCOPE_EXCLUSION,
    USER_APPROVED_SCOPE_EXCLUSION_APPROVAL_KIND,
    USER_APPROVED_SCOPE_EXCLUSION_SCHEMA,
    USER_APPROVED_SCOPE_EXCLUSION_TIMESTAMP_RE,
    source_inventory_item_user_approved_scope_exclusion_error,
)
from scripts.source_coverage_scope import (
    DEEP_ONLY_SOURCE_KINDS,
    NAMED_THEORETICAL_STATEMENTS,
    SOURCE_PRESENTATION_ALIAS_EXPLICIT_RENUMBERED_RESTATEMENT,
    SOURCE_PRESENTATION_ALIAS_LABEL_RELATION_FIELD,
    SOURCE_PRESENTATION_ALIAS_RENUMBERED_EVIDENCE_FIELD,
    THEOREM_REALIZATION_SOURCE_KINDS,
    THEOREM_REALIZATION_NONCLAIM_STATUSES,
    source_index_byte_pinned_anchor_item_ids as _source_index_byte_pinned_anchor_item_ids_uncached,
    deep_source_coverage_attestation_error,
    filter_source_map_items_for_proof_obligations,
    source_coverage_mode_from_map,
    source_coverage_mode_migration_error,
    source_item_effective_route_policy,
    source_item_in_coverage_scope,
    source_map_structural_errors,
    source_named_presentation_in_coverage_scope,
    source_named_result_environment_kinds_from_map,
    source_presentation_aliases,
    source_prose_definition_alias_pairs,
    source_prose_definition_replaced_named_presentation_spans,
    source_vocabulary_definition_binding_item_ids,
)
from scripts.source_named_result_index import (
    OPEN_NAMED_PRESENTATION_KIND,
    SOURCE_PRESENTATION_RECONCILIATION_FIELD,
    UNCLASSIFIED_NAMED_PRESENTATION_KIND,
    named_result_presentations_sha256,
    reconcile_named_result_presentations,
    reviewed_source_presentation_inventory,
    source_presentation_reconciliation_errors,
    uncovered_named_result_presentations,
)
from scripts.source_review_input import (
    SEMANTIC_CONTEXT_ROLES,
)
from scripts.source_review_scope import (
    current_closeout_review_policy_errors,
)


ROOT = Path(
    os.environ.get("APPLIEDMODELINGLIB_REPO_ROOT", Path(__file__).resolve().parents[1])
).resolve()


CLOSEOUT_STATUSES = {
    "formalized",
    "formalized with caveat",
    "partially formalized",
    "conditional",
}


FULL_CLOSEOUT_STATUSES = {
    "formalized",
    "formalized with caveat",
}


PLACEHOLDER_SOURCE_RE = re.compile(
    r"\b(?:tbd|todo|unknown|not recorded|not available)\b|"
    r"exact source location (?:to be )?refined|"
    r"paper-facing review target|"
    r"paper source location recorded by group-level|"
    r"source location recorded by group-level|"
    r"exact premise is the Lean audit-premise key",
    re.I,
)


SHA256_RE = re.compile(r"^[0-9a-fA-F]{64}$")


CORRECTED_SOURCE_STATEMENT_STATUS = "corrected_source_statement"


CORRECTED_TARGET_SCHEMA = 1


CORRECTED_TARGET_APPROVAL_KINDS = {
    "explicit_user_instruction",
    "documented_source_correction",
    "documented_author_correction",
}


LEGACY_SOURCE_DIGEST_KEYS = {
    "source_file_sha256",
    "source_pdf_sha256",
    "source_tex_sha256",
    "source_text_sha256",
}


SEMANTIC_CONTRACT_SCHEMA = 1


# Schema 1 remains the historical exact-proposition contract.  Schema 2 adds
# one source-model shape with its own source-pinned clauses and generated
# review obligation; accepting it must not make existing schema-1 maps stale.
SEMANTIC_CONTRACT_SCHEMA_2 = 2


SEMANTIC_CONTRACT_SCHEMAS = {
    SEMANTIC_CONTRACT_SCHEMA,
    SEMANTIC_CONTRACT_SCHEMA_2,
}


def schema_version_is_exact(value: object, expected: int) -> bool:
    """Return true only for the exact non-Boolean integer schema marker.

    Python's ``bool`` is an ``int`` subclass, so bare equality and set
    membership would otherwise let JSON ``true`` activate schema 1.  Every
    schema marker is an explicit protocol version, never a truthy flag.
    """

    return type(value) is int and value == expected


def schema_version_is_supported(value: object, supported: Iterable[int]) -> bool:
    """Return whether a non-Boolean integer is one supported schema version."""

    return type(value) is int and value in supported


# A semantic-surface contract is deliberately separate from a semantic proof
# contract.  The latter checks that one Lean theorem proves one specification;
# the former makes the source-facing signature itself auditable.  In
# particular, source coverage cannot rest only on a theorem's suggestive name
# or on a bundled predicate whose contents have not been exposed on the
# PaperInterface surface.
# Schema 1 is the original lexical declaration-surface guard.  Schema 2 adds
# an optional high-assurance lane whose formula requirements are checked
# against Lean's elaborated *conclusion* rather than against arbitrary source
# text.  Schema 3 is the result-only, exact-primitive contract used for new
# high-risk rows: it deliberately has no lexical term or structural-token
# fields, because those can otherwise be satisfied by a premise or a familiar
# helper name.
SEMANTIC_SURFACE_LEGACY_SCHEMA = 1


SEMANTIC_SURFACE_SCHEMA = 2


SEMANTIC_SURFACE_RESULT_SCHEMA = 3


SEMANTIC_SURFACE_SCHEMAS = {
    SEMANTIC_SURFACE_LEGACY_SCHEMA,
    SEMANTIC_SURFACE_SCHEMA,
    SEMANTIC_SURFACE_RESULT_SCHEMA,
}


SEMANTIC_SURFACE_STRUCTURAL_TOKENS = {
    "∀",
    "∃",
    "∧",
    "∨",
    "↔",
    "→",
    "=",
    "≠",
    "<",
    "≤",
    ">",
    "≥",
    "/",
    "if",
    "match",
    "∫",
    "∑",
}


SEMANTIC_SURFACE_V1_FIELDS = {
    "schema",
    "required_structural_tokens",
    "required_terms",
    "forbidden_opaque_terms",
}


SEMANTIC_SURFACE_CONCLUSION_COMPONENT_FIELDS = {
    "selector",
    "relation",
    "left_operand",
    "required_semantic_features",
    "required_constant_suffixes",
    "min_matches",
}


SEMANTIC_SURFACE_CONCLUSION_SELECTORS = {
    "rightmost_top_level_conjunct",
    "any_result_component",
}


SEMANTIC_SURFACE_CONCLUSION_RELATIONS = {"eq", "iff", "lt", "le"}


SEMANTIC_SURFACE_CONCLUSION_LEFT_OPERANDS = {"zero"}


# These are mathematical operator categories, not declaration-route labels.
# Their exact canonical Lean constants are interpreted by audit_repository.py
# after elaboration.
SEMANTIC_SURFACE_CONCLUSION_FEATURES = {
    "addition",
    "conditional",
    "division",
    "exponential",
    "integral",
    "multiplication",
    "subtraction",
    "sum",
}


SEMANTIC_SURFACE_V2_FIELDS = (
    SEMANTIC_SURFACE_V1_FIELDS | {"required_conclusion_components"}
)


# Schema 3 is intentionally compact.  Every requirement is evaluated against
# the elaborated result atom by audit_repository.py; no declaration, binder,
# proof, or source-text spelling is evidence.
SEMANTIC_SURFACE_RESULT_FEATURES = {
    "addition",
    "conditional",
    "continuous",
    "density",
    "density_coercion",
    "division",
    "differentiable",
    "exponential",
    "finite_sum",
    "finite_cardinality",
    "finite_nonempty",
    "integral",
    "measure_map",
    "measure_comp_prod",
    "measure_pi",
    "measure_product",
    "multiplication",
    "measure_dirac",
    "pmf_map",
    "pmf_to_measure",
    "power",
    "subtraction",
    "tendsto",
}


SEMANTIC_SURFACE_RESULT_CAPTURE_FEATURES = {
    *SEMANTIC_SURFACE_RESULT_FEATURES,
    # This is structural: it captures the argument of an exact PMF-to-measure
    # operation rather than recognizing an implementation helper by its name.
    "pmf_law",
}


SEMANTIC_SURFACE_RESULT_PATTERN_FIELDS = {
    "id",
    "relation",
    "all_features",
    "minimum_feature_counts",
    "canonical_sha256",
    "operand_patterns",
    "require_distinct_operands",
    "guard_patterns",
    "quantifier_shape",
    "capture",
    "equality_alias_capture",
    "allow_leaf_reuse",
    "requires_captures",
    "requires_equality_aliases",
    "min_matches",
}


SEMANTIC_SURFACE_RESULT_OPERAND_PATTERN_FIELDS = {
    "side",
    "all_features",
    "minimum_feature_counts",
    "requires_captures",
    "requires_equality_aliases",
}


SEMANTIC_SURFACE_RESULT_OPERAND_SIDES = {"left", "right", "argument"}


SEMANTIC_SURFACE_RESULT_GUARD_PATTERN_FIELDS = {
    "relation",
    "all_features",
    "minimum_feature_counts",
    "canonical_sha256",
}


SEMANTIC_SURFACE_RESULT_QUANTIFIER_FIELDS = {"forall", "exists"}


SEMANTIC_SURFACE_ASSUMPTION_PATTERN_FIELDS = {
    "id",
    "relation",
    "all_features",
    "minimum_feature_counts",
    "min_matches",
}


SEMANTIC_SURFACE_RESULT_RELATIONS = {"any", "eq", "iff", "lt", "le", "not"}


SEMANTIC_SURFACE_RESULT_CAPTURE_FIELDS = {
    "feature",
    "as",
    "distinct_from",
    "mode",
}


SEMANTIC_SURFACE_RESULT_CAPTURE_MODES = {"root", "opposite_relation_operand"}


# A directional equality bridge.  ``alias_side`` selects the Eq operand that
# must recur verbatim in a later asserted result leaf; the opposite operand
# must expose exactly one ``construction_feature`` subtree.  This is
# structural evidence only: it never follows equality rewrites or names.
SEMANTIC_SURFACE_RESULT_EQUALITY_ALIAS_CAPTURE_FIELDS = {
    "alias_side",
    "construction_feature",
    "as",
}


SEMANTIC_SURFACE_V3_FIELDS = {
    "schema",
    "outer_binder_sha256",
    "required_result_patterns",
    "required_assumption_patterns",
}


SOURCE_PROOF_LOCATOR_RE = re.compile(
    r"(?:"
    r"\b(?:page|p\.?)\s*\d+|"
    r"\b(?:appendix|section|theorem|lemma|proposition|corollary|definition|"
    r"equation|claim|proof)\s+(?:[A-Z]?\d[\w.()/-]*|[A-Z](?:\.\d+)*)|"
    r"\b[\w./-]+\.(?:tex|txt|md|pdf):\d+"
    r")",
    re.I,
)


SOURCE_FILE_LINE_RE = re.compile(
    r"(?P<path>[A-Za-z0-9_./-]+\.(?:tex|txt|md|pdf)):"
    r"(?P<start>\d+)(?:-(?P<end>\d+))?",
    re.I,
)


TEXT_SOURCE_SUFFIXES = {".tex", ".txt", ".md"}


SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY = "source_anchor_evidence_required"


SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY = "source_named_result_inventory_review"


SOURCE_NAMED_RESULT_INVENTORY_REVIEW_SCHEMA = 1


SOURCE_ANCHOR_EVIDENCE_FIELDS = {
    "path",
    "line_start",
    "line_end",
    "quoted_text",
    "quoted_text_sha256",
}


# Source-map context is deliberately a source-text-only lane.  It exposes a
# convention or domain restriction that matters when reviewing the expanded
# Lean surface, but it is never a proof route or a substitute for a theorem
# statement/contract.  Keep the schema small enough that a Lean declaration or
# function name cannot be smuggled in as purported semantic evidence.
SEMANTIC_CONTEXT_REQUIREMENTS_KEY = "semantic_context_requirements"


SEMANTIC_CONTEXT_REQUIREMENT_FIELDS = {
    "semantic_role",
    "kind",
    "source_location",
    "explanation",
    "source_anchor_evidence",
    "cited_source_artifact_id",
}


SEMANTIC_CONTEXT_REQUIREMENT_KIND_RE = re.compile(
    r"^[a-z][a-z0-9_]*(?:[.-][a-z][a-z0-9_]*)*$"
)


# A cited paper can supply a model premise or prior result needed to interpret
# one primary-paper claim.  Its bytes remain a separately authenticated input:
# the registry does not widen the primary paper's named-result inventory and a
# reference is valid only for one of the descriptor's bounded semantic roles.
CITED_SOURCE_ARTIFACTS_SCHEMA_KEY = "cited_source_artifacts_schema"
CITED_SOURCE_ARTIFACTS_KEY = "cited_source_artifacts"
CITED_SOURCE_ARTIFACT_ID_FIELD = "cited_source_artifact_id"
CITED_SOURCE_ROLE_FIELD = "cited_source_role"
CITED_SOURCE_ARTIFACT_SCHEMA = 1
CITED_SOURCE_ARTIFACT_FIELDS = {
    "id",
    "path",
    "sha256",
    "provenance_path",
    "provenance_sha256",
    "source_url",
    "semantic_roles",
}
CITED_SOURCE_ARTIFACT_ID_RE = re.compile(r"^[a-z][a-z0-9_]*(?:[.-][a-z][a-z0-9_]*)*$")


# A source can define a type/class partition *by* equality of a source feature
# vector.  That is stronger than the common one-way implementation condition
# that equal labels have equal features.  This opt-in source context makes the
# two logical directions independently auditable without treating a record,
# field, binder, or declaration spelling as evidence.
EQUALITY_DEFINED_PARTITION_CONTEXT_KIND = "equality_defined_partition"


EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD = "equality_partition_contract"


EQUALITY_DEFINED_PARTITION_CONTRACT_SCHEMA = 1


EQUALITY_DEFINED_PARTITION_RELATION = "feature_equality_iff_class_equality"


EQUALITY_DEFINED_PARTITION_REQUIRED_DIRECTIONS = {
    "feature_equality_implies_class_equality",
    "class_equality_implies_feature_equality",
}


EQUALITY_DEFINED_PARTITION_CONTRACT_FIELDS = {
    "schema",
    "relation",
    "feature_description",
    "class_description",
    "required_directions",
}


# A game-theoretic source statement can quantify a best response over every
# feasible action while evaluating some actions through a posterior,
# conditional expectation, or other observation-contingent value.  Such a
# value is not automatically defined on an observation branch of probability
# zero.  This opt-in source context makes the totality question an explicit,
# source-pinned review obligation.  It is deliberately selected only by the
# source-map context and its byte-verified quote, never by a Lean theorem,
# predicate, field, binder, or function name.
STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_KIND = "strategic_observation_totality"


STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD = (
    "strategic_observation_totality_contract"
)


# Schema 2 safely represents one conditionalization mode. Schema 3 preserves
# that form while allowing one source route to use several distinct modes, for
# example a positive selected event together with an a.e. posterior kernel.
STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA = 2


STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA = 3


STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMAS = {
    STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA,
    STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA,
}


STRATEGIC_OBSERVATION_TOTALITY_ACTION_SCOPES = {
    "all_feasible_actions",
    "source_defined_restricted_action_domain",
}


STRATEGIC_OBSERVATION_TOTALITY_VALUE_KINDS = {
    "conditional_expectation_or_posterior",
    "observation_contingent_payoff_or_belief",
}


# A conditional value can be taken on the entire source population, a source
# subgroup/access event, or an already conditioned/restricted population.  A
# source map must say which semantic carrier is being selected; an arbitrary
# Lean measure restriction is not source credit merely because it gives a
# convenient conditional-expectation route.
STRATEGIC_OBSERVATION_TOTALITY_CONDITIONING_POPULATION_SCOPES = {
    "entire_source_population",
    "source_defined_subpopulation_or_access_event",
    "source_defined_conditioned_or_restricted_population",
}


# Sequential games must make the selected event's history explicit.  The
# single-action value is intentionally available for static games, but it is a
# source-semantic declaration rather than an inference from local names.
STRATEGIC_OBSERVATION_TOTALITY_SELECTED_EVENT_HISTORY_SCOPES = {
    "single_action_without_prior_strategic_history",
    "source_defined_sequential_action_history",
    "source_defined_pre_action_state_or_history",
}


# These modes determine how a conditional value is meaningful.  In
# particular, an RCD/disintegration only supplies a version on an a.e. base;
# it cannot silently support a pointwise fibre claim.
STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES = {
    "positive_measurable_event",
    "source_totalized_pointwise_observation_branch",
    "ae_regular_conditional_distribution_or_disintegration",
}


STRATEGIC_OBSERVATION_TOTALITY_REQUIRED_CHECKS = {
    "equilibrium_action_domain",
    "observation_branch_domain",
    "zero_probability_observation_branches",
    "conditional_value_totality",
    "offpath_completion_or_infeasibility",
    "conditioning_population_carrier",
    "sequential_action_history_in_selected_event",
    "action_observation_event_measurability",
    "ae_fibre_or_base_scope",
}


STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_BASE_FIELDS = {
    "schema",
    "equilibrium_action_scope",
    "action_description",
    "observation_description",
    "conditional_value_kind",
    "conditional_value_description",
    "conditioning_population_scope",
    "conditioning_population_description",
    "selected_event_history_scope",
    "selected_event_history_description",
    "selected_event_description",
    "required_checks",
}


STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONDITIONALIZATION_SCOPE_FIELD = (
    "conditionalization_scope"
)


STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES_FIELD = (
    "conditionalization_scopes"
)


STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELDS_BY_SCHEMA = {
    STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA: {
        *STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_BASE_FIELDS,
        STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONDITIONALIZATION_SCOPE_FIELD,
    },
    STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA: {
        *STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_BASE_FIELDS,
        STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES_FIELD,
    },
}


# A conditional expectation, posterior/PBO belief, or regular conditional law
# can look source-faithful while conditioning on a strictly coarser Lean
# observation or on an unselected population.  This opt-in context records the
# source conditioning information as semantic component/stage identifiers,
# rather than trying to infer it from a theorem, function, field, or binder
# name.  The observed-component list may be empty for conditioning on the
# trivial sigma-algebra; its presence still distinguishes that case from an
# omitted contract. The source-record response then has to account for the
# corresponding Lean observation, selection stages, law population, and
# a.e./pointwise scope.
CONDITIONING_INFORMATION_CONTEXT_KIND = "conditioning_information"


CONDITIONING_INFORMATION_CONTRACT_FIELD = "conditioning_information_contract"


CONDITIONING_INFORMATION_CONTRACT_SCHEMA = 1


CONDITIONING_INFORMATION_VALUE_KINDS = {
    "conditional_expectation",
    "bayesian_or_pbo_belief",
    "conditional_law",
}


CONDITIONING_INFORMATION_LAW_POPULATIONS = {
    "raw_unselected_source_law",
    "selected_by_source_actions",
    "source_restricted_nonaction_population",
}


CONDITIONING_INFORMATION_CONDITIONALIZATION_SCOPES = {
    "positive_measurable_event",
    "pointwise_totalized_observation",
    "ae_regular_conditional_distribution_or_disintegration",
}


CONDITIONING_INFORMATION_COMPONENT_FIELDS = {"id", "description"}


CONDITIONING_INFORMATION_STAGE_FIELDS = {"id", "description"}


CONDITIONING_INFORMATION_SEMANTIC_ID_RE = re.compile(
    r"^[a-z][a-z0-9_]*(?:[.-][a-z][a-z0-9_]*)*$"
)


CONDITIONING_INFORMATION_CONTRACT_FIELDS = {
    "schema",
    "conditional_value_kind",
    "source_observed_components",
    "source_action_selection_stages",
    "source_law_population",
    "conditionalization_scopes",
}


# A source model may state primitive laws/recurrences while the Lean-facing
# theorem takes a record that already contains the material process, execution,
# cycle, or conditional-law consequence.  This opt-in source context records
# the primitive basis and conclusion that must be connected by a checked Lean
# derivation. It is keyed only by byte-pinned source content and the generated
# semantic association, not by a Lean record, field, theorem, or function name.
SOURCE_MODEL_DERIVATION_CONTEXT_KIND = "source_model_derivation"


SOURCE_MODEL_DERIVATION_CONTRACT_FIELD = "source_model_derivation_contract"


SOURCE_MODEL_DERIVATION_CONTRACT_SCHEMA = 2


SOURCE_MODEL_DERIVATION_COMPONENT_FIELDS = {
    "id",
    "description",
    "source_location",
    "source_anchor_evidence",
}


SOURCE_MODEL_DERIVATION_CONCLUSION_FIELDS = {
    "description",
    "source_location",
    "source_anchor_evidence",
}


SOURCE_MODEL_DERIVATION_CONTRACT_FIELDS = {
    "schema",
    "source_primitive_components",
    "derived_conclusion",
}


def _conditioning_information_semantic_entries_errors(
    value: object,
    *,
    field: str,
    entry_fields: set[str],
    require_nonempty: bool,
) -> list[str]:
    """Validate source-semantic component/stage entries without Lean names."""

    if not isinstance(value, list):
        return [f"{field} must be a list"]
    if require_nonempty and not value:
        return [f"{field} must be a nonempty list"]
    errors: list[str] = []
    ids: list[str] = []
    for index, entry in enumerate(value):
        prefix = f"{field}[{index}]"
        if not isinstance(entry, dict):
            errors.append(f"{prefix} must be an object")
            continue
        unexpected = sorted(set(entry) - entry_fields)
        if unexpected:
            errors.append(
                f"{prefix} has unsupported field(s): " + ", ".join(unexpected)
            )
        identifier = entry.get("id")
        if not isinstance(identifier, str) or not CONDITIONING_INFORMATION_SEMANTIC_ID_RE.fullmatch(
            identifier.strip()
        ):
            errors.append(
                f"{prefix}.id must be a lowercase source-semantic identifier"
            )
        else:
            ids.append(identifier.strip())
        description = entry.get("description")
        if not isinstance(description, str) or not description.strip():
            errors.append(
                f"{prefix}.description must be a nonempty source-semantic description"
            )
    if len(ids) != len(set(ids)):
        errors.append(f"{field} must not duplicate a semantic id")
    return errors


def conditioning_information_context_contract_errors(
    requirement: object,
) -> list[str]:
    """Validate source conditioning information before a direct match is credited.

    The contract is deliberately source-side only.  A generated review response
    has to state the Lean-side components and compare them component-by-component
    against this byte-pinned source contract; a raw law, selected law, and RCD
    scope are not interchangeable merely because a posterior helper has a
    familiar name.
    """

    if not isinstance(requirement, dict):
        return ["must be an object"]
    contract = requirement.get(CONDITIONING_INFORMATION_CONTRACT_FIELD)
    if not isinstance(contract, dict):
        return [f"{CONDITIONING_INFORMATION_CONTRACT_FIELD} must be an object"]
    errors: list[str] = []
    unexpected = sorted(set(contract) - CONDITIONING_INFORMATION_CONTRACT_FIELDS)
    if unexpected:
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD} has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if not schema_version_is_exact(
        contract.get("schema"), CONDITIONING_INFORMATION_CONTRACT_SCHEMA
    ):
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD}.schema must be "
            f"{CONDITIONING_INFORMATION_CONTRACT_SCHEMA}"
        )
    value_kind = str(contract.get("conditional_value_kind") or "").strip()
    if value_kind not in CONDITIONING_INFORMATION_VALUE_KINDS:
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD}.conditional_value_kind "
            "must identify a conditional expectation, Bayesian/PBO belief, or "
            "conditional law"
        )
    errors.extend(
        _conditioning_information_semantic_entries_errors(
            contract.get("source_observed_components"),
            field=(
                f"{CONDITIONING_INFORMATION_CONTRACT_FIELD}."
                "source_observed_components"
            ),
            entry_fields=CONDITIONING_INFORMATION_COMPONENT_FIELDS,
            require_nonempty=False,
        )
    )
    errors.extend(
        _conditioning_information_semantic_entries_errors(
            contract.get("source_action_selection_stages"),
            field=(
                f"{CONDITIONING_INFORMATION_CONTRACT_FIELD}."
                "source_action_selection_stages"
            ),
            entry_fields=CONDITIONING_INFORMATION_STAGE_FIELDS,
            require_nonempty=False,
        )
    )
    law_population = str(contract.get("source_law_population") or "").strip()
    if law_population not in CONDITIONING_INFORMATION_LAW_POPULATIONS:
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD}.source_law_population "
            "must say whether the source law is raw/unselected, selected by source "
            "actions, or restricted by a nonaction source population"
        )
    stages = contract.get("source_action_selection_stages")
    has_stages = isinstance(stages, list) and bool(stages)
    if law_population == "raw_unselected_source_law" and has_stages:
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD} cannot list action-selection "
            "stages for a raw_unselected_source_law"
        )
    if law_population == "selected_by_source_actions" and not has_stages:
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD} must list ordered "
            "source_action_selection_stages for a selected_by_source_actions law"
        )
    raw_scopes = contract.get("conditionalization_scopes")
    scopes = (
        [scope.strip() for scope in raw_scopes]
        if isinstance(raw_scopes, list) and all(isinstance(scope, str) for scope in raw_scopes)
        else []
    )
    if (
        not scopes
        or len(scopes) != len(raw_scopes)
        or len(set(scopes)) != len(scopes)
        or any(
            scope not in CONDITIONING_INFORMATION_CONDITIONALIZATION_SCOPES
            for scope in scopes
        )
    ):
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD}.conditionalization_scopes "
            "must be a nonempty duplicate-free list of positive-event, pointwise "
            "totalized, or a.e. RCD/disintegration scopes"
        )
    return errors


def _source_model_derivation_component_anchor_errors(
    entry: dict[str, Any],
    *,
    field: str,
) -> list[str]:
    """Require one independently byte-pinned source basis component.

    The later canonical-source pass verifies the line slice and digest. This
    shape pass rejects the easier failure mode first: treating a broad parent
    context quote as evidence for a separately claimed primitive or conclusion.
    """

    errors: list[str] = []
    location = entry.get("source_location")
    matches = list(SOURCE_FILE_LINE_RE.finditer(location)) if isinstance(location, str) else []
    if not isinstance(location, str) or not location.strip() or len(matches) != 1:
        errors.append(
            f"{field}.source_location must contain exactly one source anchor for "
            "this primitive or derived conclusion"
        )
    raw_anchors = entry.get("source_anchor_evidence")
    if not isinstance(raw_anchors, list) or not raw_anchors:
        errors.append(
            f"{field}.source_anchor_evidence must be a nonempty byte-pinned "
            "source-anchor list for this primitive or derived conclusion"
        )
    else:
        for index, raw_anchor in enumerate(raw_anchors):
            prefix = f"{field}.source_anchor_evidence[{index}]"
            if not isinstance(raw_anchor, dict):
                errors.append(f"{prefix} must be an object")
                continue
            missing = sorted(SOURCE_ANCHOR_EVIDENCE_FIELDS - set(raw_anchor))
            if missing:
                errors.append(
                    f"{prefix} is missing required field(s): " + ", ".join(missing)
                )
    return errors


def source_model_derivation_context_contract_errors(
    requirement: object,
) -> list[str]:
    """Validate an opt-in source primitive-to-consequence contract.

    The contract deliberately lives on the source side. Every primitive and
    the derived conclusion carries its own byte-pinned source anchor, rather
    than relying on one broadly relevant parent quote. A later generated
    semantic-model row has to account for every primitive and can receive a
    direct-match verdict only through a checked derivation, rather than by
    accepting the consequence as record data.
    """

    if not isinstance(requirement, dict):
        return ["must be an object"]
    contract = requirement.get(SOURCE_MODEL_DERIVATION_CONTRACT_FIELD)
    if not isinstance(contract, dict):
        return [f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD} must be an object"]
    errors: list[str] = []
    unexpected = sorted(set(contract) - SOURCE_MODEL_DERIVATION_CONTRACT_FIELDS)
    if unexpected:
        errors.append(
            f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD} has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if not schema_version_is_exact(
        contract.get("schema"), SOURCE_MODEL_DERIVATION_CONTRACT_SCHEMA
    ):
        errors.append(
            f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD}.schema must be "
            f"{SOURCE_MODEL_DERIVATION_CONTRACT_SCHEMA}"
        )
    primitive_field = (
        f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD}.source_primitive_components"
    )
    raw_primitives = contract.get("source_primitive_components")
    errors.extend(
        _conditioning_information_semantic_entries_errors(
            raw_primitives,
            field=primitive_field,
            entry_fields=SOURCE_MODEL_DERIVATION_COMPONENT_FIELDS,
            require_nonempty=True,
        )
    )
    if isinstance(raw_primitives, list):
        for index, primitive in enumerate(raw_primitives):
            if not isinstance(primitive, dict):
                continue
            errors.extend(
                _source_model_derivation_component_anchor_errors(
                    primitive,
                    field=f"{primitive_field}[{index}]",
                )
            )
    derived = contract.get("derived_conclusion")
    if not isinstance(derived, dict):
        errors.append(
            f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD}.derived_conclusion "
            "must be an object"
        )
    else:
        unexpected_derived = sorted(
            set(derived) - SOURCE_MODEL_DERIVATION_CONCLUSION_FIELDS
        )
        if unexpected_derived:
            errors.append(
                f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD}.derived_conclusion "
                "has unsupported field(s): "
                + ", ".join(unexpected_derived)
            )
        description = derived.get("description")
        if not isinstance(description, str) or not description.strip():
            errors.append(
                f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD}.derived_conclusion."
                "description must be a nonempty source-semantic description"
            )
        errors.extend(
            _source_model_derivation_component_anchor_errors(
                derived,
                field=(
                    f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD}.derived_conclusion"
                ),
            )
        )
    return errors


def equality_defined_partition_context_contract_errors(
    requirement: object,
) -> list[str]:
    """Validate the source-only exact-partition context payload.

    This validates metadata declared by the source-map author, not a Lean
    route.  The exact source quote is checked by the normal context-anchor
    lane.  Requiring both directions here prevents a map from asking only
    whether a formalization has the easier within-class agreement direction.
    """

    if not isinstance(requirement, dict):
        return ["must be an object"]
    contract = requirement.get(EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD)
    if not isinstance(contract, dict):
        return [
            f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD} must be an object"
        ]
    errors: list[str] = []
    unexpected = sorted(
        set(contract) - EQUALITY_DEFINED_PARTITION_CONTRACT_FIELDS
    )
    if unexpected:
        errors.append(
            f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD} has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if not schema_version_is_exact(
        contract.get("schema"), EQUALITY_DEFINED_PARTITION_CONTRACT_SCHEMA
    ):
        errors.append(
            f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD}.schema must be "
            f"{EQUALITY_DEFINED_PARTITION_CONTRACT_SCHEMA}"
        )
    if contract.get("relation") != EQUALITY_DEFINED_PARTITION_RELATION:
        errors.append(
            f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD}.relation must be "
            f"`{EQUALITY_DEFINED_PARTITION_RELATION}`"
        )
    for field in ("feature_description", "class_description"):
        if not isinstance(contract.get(field), str) or not str(
            contract.get(field) or ""
        ).strip():
            errors.append(
                f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD}.{field} "
                "must be a nonempty source-semantic description"
            )
    directions = contract.get("required_directions")
    if not isinstance(directions, list):
        errors.append(
            f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD}.required_directions "
            "must be a list containing both equality directions"
        )
    else:
        normalized = [
            direction.strip()
            for direction in directions
            if isinstance(direction, str) and direction.strip()
        ]
        if (
            len(normalized) != len(directions)
            or len(set(normalized)) != len(normalized)
            or set(normalized) != EQUALITY_DEFINED_PARTITION_REQUIRED_DIRECTIONS
        ):
            errors.append(
                f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD}.required_directions "
                "must contain exactly `feature_equality_implies_class_equality` "
                "and `class_equality_implies_feature_equality`"
            )
    return errors


def strategic_observation_totality_context_contract_errors(
    requirement: object,
) -> list[str]:
    """Validate a source-pinned game-observation totality requirement.

    The schema records only the source semantics that make an off-path review
    necessary.  It does not assert that the source is safe: the generated
    semantic-model response must separately establish totality, infeasibility,
    or an explicitly restricted equilibrium domain.
    """

    if not isinstance(requirement, dict):
        return ["must be an object"]
    contract = requirement.get(STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD)
    if not isinstance(contract, dict):
        return [
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD} must be an object"
        ]
    errors: list[str] = []
    schema = contract.get("schema")
    schema_is_supported = (
        isinstance(schema, int)
        and not isinstance(schema, bool)
        and schema in STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMAS
    )
    allowed_fields = STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELDS_BY_SCHEMA.get(
        schema if schema_is_supported else None,
        set().union(*STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELDS_BY_SCHEMA.values()),
    )
    unexpected = sorted(set(contract) - allowed_fields)
    if unexpected:
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD} has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if not schema_is_supported:
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}.schema must be "
            f"{STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA} or "
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA}"
        )
    action_scope = str(contract.get("equilibrium_action_scope") or "").strip()
    if action_scope not in STRATEGIC_OBSERVATION_TOTALITY_ACTION_SCOPES:
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}.equilibrium_action_scope "
            "must state whether the source quantifies all feasible actions or a "
            "source-defined restricted action domain"
        )
    value_kind = str(contract.get("conditional_value_kind") or "").strip()
    if value_kind not in STRATEGIC_OBSERVATION_TOTALITY_VALUE_KINDS:
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}.conditional_value_kind "
            "must identify a conditional/posterior or observation-contingent value"
        )
    conditioning_population_scope = str(
        contract.get("conditioning_population_scope") or ""
    ).strip()
    if (
        conditioning_population_scope
        not in STRATEGIC_OBSERVATION_TOTALITY_CONDITIONING_POPULATION_SCOPES
    ):
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}."
            "conditioning_population_scope must identify whether the conditional "
            "value is taken on the whole source population, a source subgroup/access "
            "event, or a source-conditioned/restricted population"
        )
    selected_event_history_scope = str(
        contract.get("selected_event_history_scope") or ""
    ).strip()
    if (
        selected_event_history_scope
        not in STRATEGIC_OBSERVATION_TOTALITY_SELECTED_EVENT_HISTORY_SCOPES
    ):
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}."
            "selected_event_history_scope must state whether the selected event has "
            "no prior strategic history, source-defined sequential action history, or "
            "a source-defined pre-action state/history"
        )
    if schema == STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA:
        conditionalization_scope = str(
            contract.get(
                STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONDITIONALIZATION_SCOPE_FIELD
            )
            or ""
        ).strip()
        if (
            conditionalization_scope
            not in STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES
        ):
            errors.append(
                f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}."
                f"{STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONDITIONALIZATION_SCOPE_FIELD} "
                "must identify a positive measurable event, a source-totalized "
                "pointwise branch, or an a.e. regular conditional "
                "distribution/disintegration"
            )
    elif schema == STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA:
        raw_scopes = contract.get(
            STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES_FIELD
        )
        scopes = (
            [scope.strip() for scope in raw_scopes]
            if isinstance(raw_scopes, list)
            and all(isinstance(scope, str) for scope in raw_scopes)
            else []
        )
        if (
            not scopes
            or len(scopes) != len(raw_scopes)
            or len(set(scopes)) != len(scopes)
            or any(
                scope not in STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES
                for scope in scopes
            )
        ):
            errors.append(
                f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}."
                f"{STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES_FIELD} "
                "must be a nonempty duplicate-free list of positive measurable-event, "
                "source-totalized pointwise-branch, or a.e. regular-conditional "
                "distribution/disintegration scopes"
            )
    for field in (
        "action_description",
        "observation_description",
        "conditional_value_description",
        "conditioning_population_description",
        "selected_event_history_description",
        "selected_event_description",
    ):
        if not isinstance(contract.get(field), str) or not str(
            contract.get(field) or ""
        ).strip():
            errors.append(
                f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}.{field} "
                "must be a nonempty source-semantic description"
            )
    raw_checks = contract.get("required_checks")
    if not isinstance(raw_checks, list):
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}.required_checks "
            "must list every totality check"
        )
    else:
        checks = [
            check.strip()
            for check in raw_checks
            if isinstance(check, str) and check.strip()
        ]
        if (
            len(checks) != len(raw_checks)
            or len(set(checks)) != len(checks)
            or set(checks) != STRATEGIC_OBSERVATION_TOTALITY_REQUIRED_CHECKS
        ):
            errors.append(
                f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}.required_checks "
                "must contain every equilibrium-domain, observation-branch, "
                "zero-probability, conditional-value, and off-path check exactly once"
            )
    return errors


def source_index_byte_pinned_anchor_item_ids(
    folder: Path,
    map_payload: object,
    mode: str,
    *,
    repository_root: Path | None = None,
    context: EvidenceRunContext | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> set[str]:
    """Project the source index once for one exact evidence transaction.

    The pure source-index implementation remains the only selector. This
    wrapper supplies the transaction's frozen source bytes and memoizes only
    the exact statement-map snapshot held by its issuer-bound context. A
    standalone call, copied context, caller-provided bytes, or different map
    payload executes the complete selector again.
    """

    selected_root = repository_root or ROOT
    exact_context_map = (
        context.statement_map_snapshot.payload
        if isinstance(context, EvidenceRunContext)
        else None
    )
    exact_bytes = (
        context.file_bytes_override()
        if isinstance(context, EvidenceRunContext)
        and file_bytes_override is None
        else file_bytes_override
    )

    def compute() -> tuple[str, ...]:
        return tuple(
            sorted(
                _source_index_byte_pinned_anchor_item_ids_uncached(
                    folder,
                    map_payload,
                    mode,
                    repository_root=selected_root,
                    file_bytes_override=exact_bytes,
                )
            )
        )

    if (
        file_bytes_override is not None
        or map_payload is not exact_context_map
        or selected_root.resolve() != ROOT.resolve()
    ):
        return set(compute())
    value = _run_scoped_cached_value(
        context,
        folder=folder,
        key=(
            "projection",
            "source_index_byte_pinned_anchor_item_ids",
            str(mode),
            context.statement_map_snapshot.sha256,
        ),
        compute=compute,
    )
    if not isinstance(value, tuple) or any(
        not isinstance(item, str) or not item for item in value
    ):
        raise TypeError("source-index projection cache contains a foreign value")
    return set(value)


def load_json(path: Path) -> dict[str, Any] | None:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, dict) else None


def _exact_file_bytes(
    path: Path,
    file_bytes_override: Mapping[Path, bytes | None] | None,
) -> bytes:
    """Read one file, or require it from an exact frozen-input mapping."""

    if file_bytes_override is None:
        return path.read_bytes()
    resolved = path.resolve()
    if resolved not in file_bytes_override:
        raise RuntimeError(f"frozen input bundle omits {resolved}")
    raw = file_bytes_override[resolved]
    if raw is None:
        raise FileNotFoundError(resolved)
    if not isinstance(raw, bytes):
        raise RuntimeError(f"frozen input bundle has non-byte content for {resolved}")
    return raw


def finding_severity(status: str) -> str:
    return "ERROR" if status in CLOSEOUT_STATUSES else "WARN"


def rel(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def canonical_sidecar(folder: Path, basename: str) -> Path:
    organized = folder / "audit" / basename
    return organized if organized.exists() else folder / basename


def transaction_sidecar(
    folder: Path,
    basename: str,
    context: EvidenceRunContext | None = None,
) -> Path:
    """Resolve a sidecar from the initial transaction state when available."""

    if context is not None and context.folder == folder.resolve():
        return context.canonical_sidecar_path(basename)
    return canonical_sidecar(folder, basename)


def transaction_json(
    path: Path,
    context: EvidenceRunContext | None = None,
) -> dict[str, Any] | None:
    """Load JSON once per transaction, falling back only in standalone mode."""

    return context.json_payload(path) if context is not None else load_json(path)


def walk_values(value: Any, prefix: tuple[str, ...] = ()) -> Iterable[tuple[tuple[str, ...], Any]]:
    if isinstance(value, dict):
        for key, item in value.items():
            item_prefix = prefix + (str(key),)
            yield item_prefix, item
            yield from walk_values(item, item_prefix)
    elif isinstance(value, list):
        for index, item in enumerate(value):
            item_prefix = prefix + (str(index),)
            yield item_prefix, item
            yield from walk_values(item, item_prefix)


def legacy_source_digest_locations(payload: dict[str, Any]) -> list[str]:
    """Return legacy digest fields that cannot identify bytes to verify."""

    locations: list[str] = []
    for path, _value in walk_values(payload):
        if path and path[-1] in LEGACY_SOURCE_DIGEST_KEYS:
            locations.append(".".join(path))
        elif path and path[-1] == "source_artifact_sha256" and len(path) != 1:
            locations.append(".".join(path))
    return sorted(set(locations))


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _paper_local_artifact_path(folder: Path, raw_path: object) -> Path | None:
    """Resolve a declared paper-local artifact without permitting path escape."""

    if not isinstance(raw_path, str) or not raw_path.strip():
        return None
    candidate = Path(raw_path.strip())
    if candidate.is_absolute():
        return None
    resolved_folder = folder.resolve()
    resolved = (folder / candidate).resolve()
    try:
        resolved.relative_to(resolved_folder)
    except ValueError:
        return None
    return resolved


def source_artifact_pin_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Validate the canonical source pin against paper-local artifact bytes."""

    severity = finding_severity(status)

    def companion_findings() -> list[Finding]:
        """Check an opted-in companion even when canonical bytes are absent.

        Structural checkouts may intentionally omit licensed source artifacts.
        That only relaxes findings explicitly caused by missing bytes; it must
        not bypass the companion's schema, path-safety, or page-map checks.
        """

        companion_issues = source_text_companion_validation_issues(
            folder,
            payload,
            repository_root=ROOT,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
        return [
            Finding(
                severity if not issue.missing_bytes or require_source_bytes else "WARN",
                folder.name,
                rel(manifest_path),
                f"source_text_companion: {issue.message}",
            )
            for issue in companion_issues
        ]

    def archive_surface_findings() -> list[Finding]:
        """Validate an opted-in archive-derived text surface independently.

        A public structural checkout can omit the archive and the derived text,
        but it cannot hide malformed paths, schema, member identities, or a
        claimed digest that does not reconstruct from private source bytes.
        """

        archive_issues = source_archive_surface_validation_issues(
            folder,
            payload,
            repository_root=ROOT,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
        return [
            Finding(
                severity if not issue.missing_bytes or require_source_bytes else "WARN",
                folder.name,
                rel(manifest_path),
                f"source_archive_surface: {issue.message}",
            )
            for issue in archive_issues
        ]

    raw_path = payload.get("source_artifact_path")
    raw_digest = payload.get("source_artifact_sha256")
    source_path = raw_path.strip() if isinstance(raw_path, str) else ""
    expected_digest = raw_digest.strip() if isinstance(raw_digest, str) else ""
    legacy_locations = legacy_source_digest_locations(payload)

    if not source_path or not expected_digest:
        missing = []
        if not source_path:
            missing.append("source_artifact_path")
        if not expected_digest:
            missing.append("source_artifact_sha256")
        legacy_note = ""
        if legacy_locations:
            legacy_note = (
                "; legacy/unscoped digest field(s) cannot pin verifiable bytes: "
                + ", ".join(legacy_locations)
            )
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source statement inventory lacks the top-level canonical source pin; "
                f"missing {', '.join(missing)}{legacy_note}",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]

    if not SHA256_RE.fullmatch(expected_digest):
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source_artifact_sha256 must be exactly 64 hexadecimal characters",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]

    relative_path = Path(source_path)
    if relative_path.is_absolute():
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source_artifact_path must be relative to the paper folder or repository root",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]

    # Prefer portable paper-relative paths.  Repository-relative `papers/...`
    # paths are accepted, but both forms must resolve inside this paper folder.
    anchor = ROOT if relative_path.parts[:1] == ("papers",) else folder
    try:
        paper_root = folder.resolve()
        artifact_path = (anchor / relative_path).resolve()
        artifact_path.relative_to(paper_root)
    except (OSError, RuntimeError, ValueError):
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source_artifact_path escapes the paper folder",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]

    frozen_artifact_present = None
    if file_bytes_override is not None:
        if artifact_path not in file_bytes_override:
            return [
                Finding(
                    severity,
                    folder.name,
                    rel(manifest_path),
                    f"frozen input bundle omits source_artifact_path: {source_path}",
                ),
                *companion_findings(),
                *archive_surface_findings(),
            ]
        frozen_artifact_present = file_bytes_override[artifact_path] is not None
    if (
        frozen_artifact_present is False
        or (file_bytes_override is None and not artifact_path.exists())
    ):
        return [
            Finding(
                severity if require_source_bytes else "WARN",
                folder.name,
                rel(manifest_path),
                (
                    f"source_artifact_path does not exist: {source_path}"
                    if require_source_bytes
                    else (
                        "source bytes are not provisioned in this structural checkout: "
                        f"{source_path}; the recorded SHA-256 is not release certification"
                    )
                ),
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]
    if file_bytes_override is None and not artifact_path.is_file():
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                f"source_artifact_path is not a regular file: {source_path}",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]

    try:
        actual_digest = (
            hashlib.sha256(
                _exact_file_bytes(artifact_path, file_bytes_override)
            ).hexdigest()
            if file_bytes_override is not None
            else sha256_file(artifact_path)
        )
    except (OSError, RuntimeError) as error:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                f"cannot read source_artifact_path `{source_path}`: {error}",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]
    if actual_digest != expected_digest.lower():
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source artifact SHA-256 mismatch: "
                f"manifest has {expected_digest.lower()}, file has {actual_digest}",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]
    return [*companion_findings(), *archive_surface_findings()]


def resolve_paper_source_path(folder: Path, raw_path: object) -> tuple[Path | None, str]:
    """Resolve a paper-local or repository-relative source path safely."""

    if not isinstance(raw_path, str) or not raw_path.strip():
        return None, "path must be a nonempty string"
    relative_path = Path(raw_path.strip())
    if relative_path.is_absolute():
        return None, "path must be relative to the paper folder or repository root"
    anchor = ROOT if relative_path.parts[:1] == ("papers",) else folder
    try:
        candidate = (anchor / relative_path).resolve()
        candidate.relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return None, "path escapes the paper folder"
    return candidate, ""


def cited_source_artifact_registry(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: Mapping[str, Any],
    *,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> tuple[dict[str, dict[str, Any]], list[Finding]]:
    """Validate and materialize the map's narrow cited-source registry.

    Every descriptor pins both the cited UTF-8 text and its provenance record.
    In a frozen transaction both byte strings must be present in the supplied
    snapshot; this function never falls back to the live checkout.
    """

    raw_schema = payload.get(CITED_SOURCE_ARTIFACTS_SCHEMA_KEY)
    raw_descriptors = payload.get(CITED_SOURCE_ARTIFACTS_KEY)
    if raw_schema is None and raw_descriptors is None:
        return {}, []

    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(manifest_path), message))

    if (
        not isinstance(raw_schema, int)
        or isinstance(raw_schema, bool)
        or raw_schema != CITED_SOURCE_ARTIFACT_SCHEMA
    ):
        add(
            f"{CITED_SOURCE_ARTIFACTS_SCHEMA_KEY} must be "
            f"{CITED_SOURCE_ARTIFACT_SCHEMA}"
        )
    if not isinstance(raw_descriptors, list) or not raw_descriptors:
        add(f"{CITED_SOURCE_ARTIFACTS_KEY} must be a nonempty list")
        return {}, findings

    primary_path, _ = resolve_paper_source_path(
        folder, payload.get("source_artifact_path")
    )
    registry: dict[str, dict[str, Any]] = {}
    source_owners: dict[Path, str] = {}
    provenance_owners: dict[Path, str] = {}

    def read_pinned_bytes(
        path: Path | None,
        raw_path: object,
        expected_digest: object,
        *,
        label: str,
    ) -> bytes | None:
        if path is None:
            return None
        digest = str(expected_digest or "").strip().lower()
        if not SHA256_RE.fullmatch(digest):
            add(f"{label}.sha256 must be exactly 64 hexadecimal characters")
            return None
        if file_bytes_override is None and not path.is_file():
            add(f"{label}.path does not identify a regular file: {raw_path}")
            return None
        try:
            raw = _exact_file_bytes(path, file_bytes_override)
        except (OSError, RuntimeError) as error:
            add(f"cannot read {label}.path `{raw_path}`: {error}")
            return None
        actual_digest = hashlib.sha256(raw).hexdigest()
        if actual_digest != digest:
            add(
                f"{label}.sha256 mismatch: descriptor has {digest}, "
                f"file has {actual_digest}"
            )
            return None
        return raw

    for index, raw_descriptor in enumerate(raw_descriptors):
        label = f"{CITED_SOURCE_ARTIFACTS_KEY}[{index}]"
        if not isinstance(raw_descriptor, Mapping):
            add(f"{label} must be an object")
            continue
        unexpected = sorted(set(raw_descriptor) - CITED_SOURCE_ARTIFACT_FIELDS)
        missing = sorted(CITED_SOURCE_ARTIFACT_FIELDS - set(raw_descriptor))
        if unexpected:
            add(f"{label} has unsupported field(s): {', '.join(unexpected)}")
        if missing:
            add(f"{label} is missing required field(s): {', '.join(missing)}")

        artifact_id = str(raw_descriptor.get("id") or "").strip()
        if not CITED_SOURCE_ARTIFACT_ID_RE.fullmatch(artifact_id):
            add(f"{label}.id must use lowercase semantic identifier syntax")
        elif artifact_id in registry:
            add(f"{label}.id duplicates cited source artifact `{artifact_id}`")

        source_path, source_path_error = resolve_paper_source_path(
            folder, raw_descriptor.get("path")
        )
        if source_path is None:
            add(f"{label}.path {source_path_error}")
        elif source_path == primary_path:
            add(f"{label}.path must differ from the primary canonical source artifact")
        elif source_path in source_owners:
            add(
                f"{label}.path duplicates cited source artifact "
                f"`{source_owners[source_path]}`"
            )
        elif artifact_id:
            source_owners[source_path] = artifact_id

        provenance_path, provenance_path_error = resolve_paper_source_path(
            folder, raw_descriptor.get("provenance_path")
        )
        if provenance_path is None:
            add(f"{label}.provenance_path {provenance_path_error}")
        elif provenance_path == source_path:
            add(f"{label}.provenance_path must differ from its cited text path")
        elif provenance_path in provenance_owners:
            add(
                f"{label}.provenance_path duplicates cited source artifact "
                f"`{provenance_owners[provenance_path]}`"
            )
        elif artifact_id:
            provenance_owners[provenance_path] = artifact_id

        source_url = str(raw_descriptor.get("source_url") or "").strip()
        if not re.fullmatch(r"https?://[^\s]+", source_url):
            add(f"{label}.source_url must be an absolute HTTP(S) URL")

        raw_roles = raw_descriptor.get("semantic_roles")
        roles: set[str] = set()
        if (
            not isinstance(raw_roles, list)
            or not raw_roles
            or any(not isinstance(role, str) or not role.strip() for role in raw_roles)
        ):
            add(f"{label}.semantic_roles must be a nonempty string list")
        else:
            normalized_roles = [role.strip() for role in raw_roles]
            roles = set(normalized_roles)
            if len(roles) != len(normalized_roles):
                add(f"{label}.semantic_roles must not contain duplicates")
            unsupported_roles = sorted(roles - SEMANTIC_CONTEXT_ROLES)
            if unsupported_roles:
                add(
                    f"{label}.semantic_roles contains unsupported role(s): "
                    + ", ".join(unsupported_roles)
                )

        source_bytes = read_pinned_bytes(
            source_path,
            raw_descriptor.get("path"),
            raw_descriptor.get("sha256"),
            label=label,
        )
        source_lines: list[str] | None = None
        if source_bytes is not None:
            try:
                source_lines = normalized_source_lines(normalized_source_text(source_bytes))
            except UnicodeDecodeError:
                add(f"{label}.path must identify a UTF-8 text artifact")

        provenance_bytes = read_pinned_bytes(
            provenance_path,
            raw_descriptor.get("provenance_path"),
            raw_descriptor.get("provenance_sha256"),
            label=f"{label}.provenance",
        )
        provenance: object = None
        if provenance_bytes is not None:
            try:
                def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
                    result: dict[str, Any] = {}
                    for key, value in pairs:
                        if key in result:
                            raise ValueError(f"duplicate key `{key}`")
                        result[key] = value
                    return result

                provenance = json.loads(
                    provenance_bytes.decode("utf-8"),
                    object_pairs_hook=reject_duplicate_keys,
                )
            except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as error:
                add(f"{label}.provenance_path is not valid duplicate-free UTF-8 JSON: {error}")
        if provenance is not None:
            if not isinstance(provenance, Mapping):
                add(f"{label}.provenance_path must contain a JSON object")
            else:
                provenance_schema = provenance.get("schema")
                if (
                    not isinstance(provenance_schema, int)
                    or isinstance(provenance_schema, bool)
                    or provenance_schema != 1
                ):
                    add(f"{label}.provenance_path schema must be 1")
                if str(provenance.get("source_url") or "").strip() != source_url:
                    add(f"{label}.provenance_path source_url does not match the descriptor")
                if (
                    str(provenance.get("source_artifact_sha256") or "").strip().lower()
                    != str(raw_descriptor.get("sha256") or "").strip().lower()
                ):
                    add(
                        f"{label}.provenance_path source_artifact_sha256 does not "
                        "match the descriptor"
                    )
                provenance_copy, _ = resolve_paper_source_path(
                    folder, provenance.get("paper_local_copy_path")
                )
                if provenance_copy != source_path:
                    add(
                        f"{label}.provenance_path paper_local_copy_path does not "
                        "match the descriptor"
                    )
                if not isinstance(provenance.get("source_version"), str) or not str(
                    provenance.get("source_version")
                ).strip():
                    add(
                        f"{label}.provenance_path source_version must be a nonempty string"
                    )
                if "original_repository_path" in provenance and (
                    not isinstance(provenance.get("original_repository_path"), str)
                    or not str(provenance.get("original_repository_path")).strip()
                ):
                    add(
                        f"{label}.provenance_path original_repository_path must be "
                        "a nonempty string when present"
                    )

        if (
            artifact_id
            and artifact_id not in registry
            and source_path is not None
            and source_lines is not None
        ):
            registry[artifact_id] = {
                "path": source_path,
                "lines": source_lines,
                "semantic_roles": roles,
            }
    return registry, findings


def normalized_source_text(raw: bytes) -> str:
    """Return the canonical text view used by source line anchors.

    The artifact's raw SHA-256 remains the source pin.  Line-oriented evidence
    intentionally normalizes only line endings, so a source extracted on a
    CRLF host has the same quoted line slices as the LF version.
    """

    return raw.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")


def normalized_source_lines(text: str) -> list[str]:
    """Split canonical source text into one-based logical lines.

    A terminating newline ends the final content line rather than adding a
    synthetic empty line.  Empty lines that are actually present in the source
    remain part of the line inventory.
    """

    if not text:
        return []
    lines = text.split("\n")
    if text.endswith("\n"):
        lines.pop()
    return lines


def normalized_source_line_excerpt(
    lines: list[str], line_start: int, line_end: int
) -> str | None:
    """Return the canonical no-terminal-newline slice, or ``None`` if invalid."""

    if line_start < 1 or line_end < line_start or line_end > len(lines):
        return None
    return "\n".join(lines[line_start - 1 : line_end])


def source_anchor_evidence_nodes(
    value: object, path: str = "$") -> Iterable[tuple[str, dict[str, Any]]]:
    """Yield every structured source-location declaration in an inventory.

    This deliberately follows JSON structure, not row keys or Lean declaration
    names. Nested component-level anchors therefore receive the same evidence
    requirement as top-level statement-map rows when a paper opts in.
    ``semantic_context_requirements`` are validated by their dedicated,
    always-on source-only lane below so they cannot be skipped when a map has
    not opted into global anchor evidence.
    """

    if isinstance(value, dict):
        if "source_location" in value:
            yield path, value
        for key, child in value.items():
            if key in {
                "source_anchor_evidence",
                SEMANTIC_CONTEXT_REQUIREMENTS_KEY,
            }:
                continue
            yield from source_anchor_evidence_nodes(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from source_anchor_evidence_nodes(child, f"{path}[{index}]")


def scoped_computational_observation_nodes(
    value: object, path: str = "$"
) -> Iterable[tuple[str, dict[str, Any]]]:
    """Yield explicit computational-exception rows without using their keys.

    A byte-pinned quote is mandatory for this narrow scope exemption even when a
    paper has not elected to require quote evidence for its entire source map.
    Traverse the JSON structure instead of recognizing map keys or Lean names so
    a renamed item cannot escape the same source-evidence requirement.
    """

    if isinstance(value, dict):
        if (
            str(value.get("source_scope_classification") or "").strip().lower()
            == NON_NAMED_COMPUTATIONAL_ILLUSTRATION
        ):
            yield path, value
        for key, child in value.items():
            if key == "source_anchor_evidence":
                continue
            yield from scoped_computational_observation_nodes(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from scoped_computational_observation_nodes(child, f"{path}[{index}]")


def user_approved_scope_exclusion_nodes(
    value: object, path: str = "$"
) -> Iterable[tuple[str, dict[str, Any]]]:
    """Yield source-map items carrying explicit user-scope metadata.

    The approval does not make a source claim non-claim-bearing.  It only
    creates a separately auditable scope disposition, so its exact source
    location needs the same byte-pinned quote evidence as any other exception.
    This structural traversal never consults map keys or Lean names.
    """

    if isinstance(value, dict):
        if USER_APPROVED_SCOPE_EXCLUSION in value:
            yield path, value
        for key, child in value.items():
            if key == "source_anchor_evidence":
                continue
            yield from user_approved_scope_exclusion_nodes(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from user_approved_scope_exclusion_nodes(child, f"{path}[{index}]")


def semantic_context_requirement_shape_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
) -> list[Finding]:
    """Validate the source-only context schema before quote checking.

    The requirement is intentionally not attached to a Lean endpoint. Its only
    job is to force a reviewer to account for a source convention/domain fact
    that could otherwise be silently assumed in a formal statement.
    """

    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return []
    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(manifest_path), message))

    for raw_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict):
            continue
        if SEMANTIC_CONTEXT_REQUIREMENTS_KEY not in raw_item:
            continue
        node_path = f"items.{raw_key}.{SEMANTIC_CONTEXT_REQUIREMENTS_KEY}"
        requirements = raw_item.get(SEMANTIC_CONTEXT_REQUIREMENTS_KEY)
        if not isinstance(requirements, list) or not requirements:
            add(f"{node_path} must be a nonempty list")
            continue
        for index, requirement in enumerate(requirements):
            requirement_path = f"{node_path}[{index}]"
            if not isinstance(requirement, dict):
                add(f"{requirement_path} must be an object")
                continue
            kind = requirement.get("kind")
            semantic_role = requirement.get("semantic_role")
            allowed_fields = set(SEMANTIC_CONTEXT_REQUIREMENT_FIELDS)
            if kind == EQUALITY_DEFINED_PARTITION_CONTEXT_KIND:
                allowed_fields.add(EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD)
            if kind == STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_KIND:
                allowed_fields.add(STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD)
            if kind == CONDITIONING_INFORMATION_CONTEXT_KIND:
                allowed_fields.add(CONDITIONING_INFORMATION_CONTRACT_FIELD)
            if kind == SOURCE_MODEL_DERIVATION_CONTEXT_KIND:
                allowed_fields.add(SOURCE_MODEL_DERIVATION_CONTRACT_FIELD)
            unexpected = sorted(
                set(requirement) - allowed_fields
            )
            if unexpected:
                add(
                    f"{requirement_path} has unsupported field(s): "
                    + ", ".join(unexpected)
                )
            required_fields = ["source_anchor_evidence"]
            # Pre-v11 maps used a curator-facing `kind`/location/explanation
            # triple.  Preserve that narrow compatibility lane, but whenever
            # a bounded `semantic_role` is supplied it is the authority for
            # what the raw-source statement judge may use as context.
            if semantic_role is None:
                required_fields.extend(["kind", "source_location", "explanation"])
            for field in required_fields:
                if field not in requirement:
                    add(f"{requirement_path} is missing required field `{field}`")
            if semantic_role is not None:
                if not isinstance(semantic_role, str) or semantic_role.strip() not in SEMANTIC_CONTEXT_ROLES:
                    add(
                        f"{requirement_path}.semantic_role must be one of: "
                        + ", ".join(sorted(SEMANTIC_CONTEXT_ROLES))
                    )
            # If legacy curation fields are present, retain their validation;
            # role-only v11 context instead relies exclusively on the pinned
            # source quotes and its bounded semantic role.
            uses_legacy_curation = semantic_role is None or any(
                field in requirement for field in ("kind", "source_location", "explanation")
            )
            if uses_legacy_curation:
                if not isinstance(kind, str) or not kind.strip():
                    add(f"{requirement_path}.kind must be a nonempty semantic identifier")
                elif not SEMANTIC_CONTEXT_REQUIREMENT_KIND_RE.fullmatch(kind.strip()):
                    add(
                        f"{requirement_path}.kind must use lowercase semantic identifier "
                        "syntax (letters, digits, `_`, `.`, or `-`)"
                    )
                location = requirement.get("source_location")
                if not isinstance(location, str) or not location.strip():
                    add(f"{requirement_path}.source_location must be a nonempty string")
                elif not list(SOURCE_FILE_LINE_RE.finditer(location)):
                    add(
                        f"{requirement_path}.source_location must include one or more "
                        "file:line anchors into the canonical pinned source artifact"
                    )
                explanation = requirement.get("explanation")
                if not isinstance(explanation, str) or not explanation.strip():
                    add(f"{requirement_path}.explanation must be a nonempty semantic explanation")
            anchors = requirement.get("source_anchor_evidence")
            if not isinstance(anchors, list) or not anchors:
                add(
                    f"{requirement_path}.source_anchor_evidence must be a nonempty "
                    "byte-pinned source-anchor list"
                )
            if kind == EQUALITY_DEFINED_PARTITION_CONTEXT_KIND:
                for error in equality_defined_partition_context_contract_errors(
                    requirement
                ):
                    add(f"{requirement_path}.{error}")
            elif kind == STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_KIND:
                for error in strategic_observation_totality_context_contract_errors(
                    requirement
                ):
                    add(f"{requirement_path}.{error}")
            elif kind == CONDITIONING_INFORMATION_CONTEXT_KIND:
                for error in conditioning_information_context_contract_errors(
                    requirement
                ):
                    add(f"{requirement_path}.{error}")
            elif kind == SOURCE_MODEL_DERIVATION_CONTEXT_KIND:
                for error in source_model_derivation_context_contract_errors(
                    requirement
                ):
                    add(f"{requirement_path}.{error}")
            elif EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD in requirement:
                add(
                    f"{requirement_path}.{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD} "
                    f"is allowed only with kind `{EQUALITY_DEFINED_PARTITION_CONTEXT_KIND}`"
                )
            elif STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD in requirement:
                add(
                    f"{requirement_path}.{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD} "
                    "is allowed only with kind "
                    f"`{STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_KIND}`"
                )
            elif CONDITIONING_INFORMATION_CONTRACT_FIELD in requirement:
                add(
                    f"{requirement_path}.{CONDITIONING_INFORMATION_CONTRACT_FIELD} "
                    "is allowed only with kind "
                    f"`{CONDITIONING_INFORMATION_CONTEXT_KIND}`"
                )
            elif SOURCE_MODEL_DERIVATION_CONTRACT_FIELD in requirement:
                add(
                    f"{requirement_path}.{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD} "
                    "is allowed only with kind "
                    f"`{SOURCE_MODEL_DERIVATION_CONTEXT_KIND}`"
                )
    return findings


def semantic_context_requirement_anchor_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Byte-validate every declared semantic context requirement.

    The synthetic map limits the ordinary quote validator to these source-only
    requirements. It neither looks at, nor gives credit for, any source-map
    Lean route. A malformed requirement is handled by the shape validator so
    this helper can keep its diagnostics focused on exact canonical source
    bytes and line ranges.
    """

    context_items: dict[str, dict[str, Any]] = {}
    raw_items = payload.get("items")
    if isinstance(raw_items, dict):
        for raw_key, raw_item in raw_items.items():
            if not isinstance(raw_item, dict):
                continue
            if SEMANTIC_CONTEXT_REQUIREMENTS_KEY not in raw_item:
                continue
            # Use a neutral synthetic container so the ordinary quote walker
            # visits the requirement entries while its normal traversal keeps
            # this separately validated lane out of global-anchor diagnostics.
            # Role-only v11 context deliberately has no curator paraphrase or
            # independent location string.  Derive a validation-only locator
            # from the context's own declared anchor coordinates so the shared
            # anchor validator still checks exact current source bytes; this
            # does not add any source text or semantic content.
            raw_contexts = raw_item.get(SEMANTIC_CONTEXT_REQUIREMENTS_KEY)
            normalized_contexts: list[object] = []
            if isinstance(raw_contexts, list):
                for raw_context in raw_contexts:
                    if not isinstance(raw_context, dict):
                        normalized_contexts.append(raw_context)
                        continue
                    context = dict(raw_context)
                    if (
                        context.get("semantic_role") is not None
                        and not str(context.get("source_location") or "").strip()
                    ):
                        anchors = context.get("source_anchor_evidence")
                        locators: list[str] = []
                        if isinstance(anchors, list):
                            for anchor in anchors:
                                if not isinstance(anchor, dict):
                                    continue
                                path = str(anchor.get("path") or "").strip()
                                start = anchor.get("line_start")
                                end = anchor.get("line_end")
                                if path and isinstance(start, int) and isinstance(end, int):
                                    suffix = str(start) if start == end else f"{start}-{end}"
                                    locators.append(f"{path}:{suffix}")
                        if locators:
                            context["source_location"] = "; ".join(locators)
                    normalized_contexts.append(context)
            context_items[str(raw_key)] = {
                "context_entries": normalized_contexts
            }
    if not context_items:
        return []
    isolated_payload = {
        "source_artifact_path": payload.get("source_artifact_path"),
        "source_artifact_sha256": payload.get("source_artifact_sha256"),
        CITED_SOURCE_ARTIFACTS_SCHEMA_KEY: payload.get(
            CITED_SOURCE_ARTIFACTS_SCHEMA_KEY
        ),
        CITED_SOURCE_ARTIFACTS_KEY: payload.get(CITED_SOURCE_ARTIFACTS_KEY),
        SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY: True,
        "items": context_items,
    }
    if payload.get(CITED_SOURCE_ARTIFACTS_SCHEMA_KEY) is None:
        isolated_payload.pop(CITED_SOURCE_ARTIFACTS_SCHEMA_KEY)
    if payload.get(CITED_SOURCE_ARTIFACTS_KEY) is None:
        isolated_payload.pop(CITED_SOURCE_ARTIFACTS_KEY)
    return source_anchor_evidence_findings(
        folder,
        status,
        manifest_path,
        isolated_payload,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    )


def semantic_context_requirement_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Return schema and exact-source evidence failures for context requirements."""

    shape_findings = semantic_context_requirement_shape_findings(
        folder, status, manifest_path, payload
    )
    if shape_findings:
        return shape_findings
    return semantic_context_requirement_anchor_findings(
        folder,
        status,
        manifest_path,
        payload,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    )


def source_anchor_evidence_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Validate required source excerpts against the canonical pinned artifact.

    A map opts in with top-level ``source_anchor_evidence_required: true`` to
    require evidence for every structured ``source_location``. Independently,
    every ``non_named_computational_illustration`` scope exemption and every
    ``user_approved_scope_exclusion`` record always needs evidence, even when
    the map does not opt in globally. Each required node
    needs one
    ``source_anchor_evidence`` object per declared ``file:line[-line]`` anchor:

    ``{"path", "line_start", "line_end", "quoted_text", "quoted_text_sha256"}``

    Evidence paths must resolve to the top-level pinned artifact, the quote's
    UTF-8 SHA-256 must be current, and the quote must equal the exact canonical
    line slice.  The raw artifact SHA-256 is checked first, tying this content
    evidence to the byte-pinned source rather than to a declaration name.
    """

    raw_required = payload.get(SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY, False)
    severity = finding_severity(status)
    if raw_required is not False and raw_required is not True:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                f"{SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY} must be boolean true when present",
            )
        ]

    all_location_nodes = list(source_anchor_evidence_nodes(payload))
    scoped_nodes = list(scoped_computational_observation_nodes(payload))
    scoped_nodes.extend(user_approved_scope_exclusion_nodes(payload))
    # A malformed attempt to combine the two lanes should still be diagnosed by
    # their dedicated validators, not duplicate every quote-evidence finding.
    unique_scoped_nodes: list[tuple[str, dict[str, Any]]] = []
    seen_scoped_paths: set[str] = set()
    for node_path, node in scoped_nodes:
        if node_path not in seen_scoped_paths:
            seen_scoped_paths.add(node_path)
            unique_scoped_nodes.append((node_path, node))
    scoped_nodes = unique_scoped_nodes
    required_nodes = all_location_nodes if raw_required is True else scoped_nodes
    registry_present = (
        payload.get(CITED_SOURCE_ARTIFACTS_SCHEMA_KEY) is not None
        or payload.get(CITED_SOURCE_ARTIFACTS_KEY) is not None
    )
    if not required_nodes and raw_required is False and not registry_present:
        return []

    pin_findings = source_artifact_pin_findings(
        folder,
        status,
        manifest_path,
        payload,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    )
    if pin_findings:
        # A source quote cannot certify anything until the artifact it quotes is
        # itself byte-verified.  Returning the pin finding avoids a second,
        # misleading content diagnosis for an untrusted file.
        return pin_findings

    cited_sources, cited_source_findings = cited_source_artifact_registry(
        folder,
        status,
        manifest_path,
        payload,
        file_bytes_override=file_bytes_override,
    )
    if cited_source_findings:
        return cited_source_findings
    if not required_nodes:
        return []

    artifact_path, artifact_path_error = resolve_paper_source_path(
        folder, payload.get("source_artifact_path")
    )
    if artifact_path is None:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "cannot resolve canonical source artifact for source-anchor evidence: "
                + artifact_path_error,
            )
        ]
    try:
        source_bytes = _exact_file_bytes(artifact_path, file_bytes_override)
        source_text = normalized_source_text(source_bytes)
    except UnicodeDecodeError:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source-anchor evidence requires a UTF-8 text canonical source artifact",
            )
        ]
    except (OSError, RuntimeError) as error:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                f"cannot read canonical source artifact for source-anchor evidence: {error}",
            )
        ]

    expected_digest = str(payload.get("source_artifact_sha256") or "").strip().lower()
    actual_digest = hashlib.sha256(source_bytes).hexdigest()
    if actual_digest != expected_digest:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source artifact changed after pin validation; cannot certify source-anchor evidence",
            )
        ]

    source_lines = normalized_source_lines(source_text)
    semantic_path_text, semantic_expected_digest = semantic_review_source_identity(payload)
    semantic_artifact_path, semantic_path_error = resolve_paper_source_path(
        folder, semantic_path_text
    )
    if semantic_artifact_path is None:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "cannot resolve selected semantic source artifact for source-anchor evidence: "
                + semantic_path_error,
            )
        ]
    if not SHA256_RE.fullmatch(semantic_expected_digest):
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "selected semantic source artifact must carry an exact SHA-256 digest",
            )
        ]
    try:
        semantic_bytes = _exact_file_bytes(semantic_artifact_path, file_bytes_override)
        semantic_text = normalized_source_text(semantic_bytes)
    except UnicodeDecodeError:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "selected semantic source artifact must be UTF-8 text for source-anchor evidence",
            )
        ]
    except (OSError, RuntimeError) as error:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                f"cannot read selected semantic source artifact for source-anchor evidence: {error}",
            )
        ]
    if hashlib.sha256(semantic_bytes).hexdigest() != semantic_expected_digest:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "selected semantic source artifact changed after pin validation; "
                "cannot certify source-anchor evidence",
            )
        ]
    semantic_source_lines = normalized_source_lines(semantic_text)
    semantic_is_canonical = semantic_artifact_path == artifact_path
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(manifest_path), message))

    # An explicit, valid scope exclusion can leave no ordinary source rows.
    # It remains independently validated below in the raw-map lane; demanding
    # a synthetic in-scope locator here would turn an approved exclusion into
    # a false source-evidence failure.
    if not required_nodes:
        return findings

    for node_path, node in required_nodes:
        raw_cited_id = node.get(CITED_SOURCE_ARTIFACT_ID_FIELD)
        raw_cited_role = node.get(CITED_SOURCE_ROLE_FIELD)
        cited_id = str(raw_cited_id or "").strip()
        cited_role = str(
            raw_cited_role or node.get("semantic_role") or ""
        ).strip()
        if raw_cited_role is not None and not cited_id:
            add(
                f"{node_path}.{CITED_SOURCE_ROLE_FIELD} requires "
                f"{CITED_SOURCE_ARTIFACT_ID_FIELD}"
            )
            continue
        uses_cited_source = raw_cited_id is not None
        is_semantic_context = ".context_entries[" in node_path
        if uses_cited_source:
            if not cited_id:
                add(f"{node_path}.{CITED_SOURCE_ARTIFACT_ID_FIELD} must be nonempty")
                continue
            if is_semantic_context:
                if raw_cited_role is not None:
                    add(
                        f"{node_path}.{CITED_SOURCE_ROLE_FIELD} is reserved for "
                        "standalone cited prerequisites"
                    )
                    continue
            else:
                if raw_cited_role is None:
                    add(
                        f"{node_path}.{CITED_SOURCE_ARTIFACT_ID_FIELD} on a standalone "
                        f"cited prerequisite requires {CITED_SOURCE_ROLE_FIELD}"
                    )
                    continue
                inventory_role = str(node.get("inventory_role") or "").strip()
                source_status = str(node.get("source_status") or "").strip().lower()
                if (
                    inventory_role != "source_semantic_declaration"
                    and source_status != "support_only"
                ):
                    add(
                        f"{node_path} cites an external source directly but is not an "
                        "explicit source_semantic_declaration or support_only prerequisite"
                    )
                    continue
                if (
                    node.get("semantic_contract") is not None
                    or node.get("source_claim_atoms") is not None
                ):
                    add(
                        f"{node_path} cites an external prerequisite and cannot carry "
                        "a primary source claim atom or semantic contract"
                    )
                    continue
            cited_source = cited_sources.get(cited_id)
            if cited_source is None:
                add(
                    f"{node_path}.{CITED_SOURCE_ARTIFACT_ID_FIELD} names unknown "
                    f"cited source artifact `{cited_id}`"
                )
                continue
            if cited_role not in cited_source["semantic_roles"]:
                add(
                    f"{node_path} cites `{cited_id}` for unregistered semantic role "
                    f"`{cited_role}`"
                )
                continue
            node_location_artifact_path = cited_source["path"]
            node_location_lines = cited_source["lines"]
            node_evidence_artifact_path = cited_source["path"]
            node_evidence_lines = cited_source["lines"]
            compare_anchor_counters = True
        else:
            node_location_artifact_path = artifact_path
            node_location_lines = source_lines
            node_evidence_artifact_path = semantic_artifact_path
            node_evidence_lines = semantic_source_lines
            compare_anchor_counters = semantic_is_canonical

        raw_location = node.get("source_location")
        if not isinstance(raw_location, str) or not raw_location.strip():
            add(f"{node_path}.source_location must be a nonempty string")
            continue
        location_matches = list(SOURCE_FILE_LINE_RE.finditer(raw_location))
        if not location_matches:
            add(
                f"{node_path}.source_location must include one or more file:line anchors "
                "when source-anchor evidence is required"
            )
            continue

        expected_anchors: Counter[tuple[str, int, int]] = Counter()
        for match in location_matches:
            raw_anchor_path = match.group("path")
            candidate, path_error = resolve_paper_source_path(folder, raw_anchor_path)
            start = int(match.group("start"))
            end = int(match.group("end") or start)
            if candidate is None:
                add(
                    f"{node_path}.source_location anchor `{raw_anchor_path}:{start}-{end}` "
                    f"{path_error}"
                )
                continue
            if candidate != node_location_artifact_path:
                message = (
                    "does not identify its pinned cited source artifact"
                    if uses_cited_source
                    else "does not identify the canonical pinned source artifact"
                )
                add(
                    f"{node_path}.source_location anchor `{raw_anchor_path}:{start}-{end}` "
                    + message
                )
                continue
            if normalized_source_line_excerpt(node_location_lines, start, end) is None:
                message = (
                    f"is outside the {len(node_location_lines)}-line pinned cited source artifact"
                    if uses_cited_source
                    else f"is outside the {len(source_lines)}-line canonical source artifact"
                )
                add(
                    f"{node_path}.source_location anchor `{raw_anchor_path}:{start}-{end}` "
                    + message
                )
                continue
            expected_anchors[(str(node_location_artifact_path), start, end)] += 1

        raw_evidence = node.get("source_anchor_evidence")
        if not isinstance(raw_evidence, list) or not raw_evidence:
            add(
                f"{node_path}.source_anchor_evidence must be a nonempty list with one "
                "byte-verified quote for every declared source anchor"
            )
            continue

        actual_anchors: Counter[tuple[str, int, int]] = Counter()
        for index, raw_entry in enumerate(raw_evidence):
            entry_path = f"{node_path}.source_anchor_evidence[{index}]"
            if not isinstance(raw_entry, dict):
                add(f"{entry_path} must be an object")
                continue
            missing = sorted(
                field for field in SOURCE_ANCHOR_EVIDENCE_FIELDS if field not in raw_entry
            )
            if missing:
                add(f"{entry_path} is missing required field(s): {', '.join(missing)}")
                continue

            candidate, path_error = resolve_paper_source_path(folder, raw_entry.get("path"))
            line_start = raw_entry.get("line_start")
            line_end = raw_entry.get("line_end")
            valid_lines = (
                isinstance(line_start, int)
                and not isinstance(line_start, bool)
                and isinstance(line_end, int)
                and not isinstance(line_end, bool)
            )
            if candidate is None:
                add(f"{entry_path}.path {path_error}")
            elif candidate != node_evidence_artifact_path:
                if uses_cited_source:
                    add(
                        f"{entry_path}.path must identify the pinned cited source artifact"
                    )
                else:
                    add(
                        f"{entry_path}.path must identify the canonical pinned source artifact "
                        "or its selected semantic transcription"
                    )
            if not valid_lines:
                add(f"{entry_path}.line_start and line_end must be integers")
            elif normalized_source_line_excerpt(
                node_evidence_lines, line_start, line_end
            ) is None:
                if uses_cited_source:
                    add(
                        f"{entry_path}.line_start/line_end is outside the "
                        f"{len(node_evidence_lines)}-line pinned cited source artifact"
                    )
                else:
                    add(
                        f"{entry_path}.line_start/line_end is outside the "
                        f"{len(semantic_source_lines)}-line selected semantic source artifact"
                    )

            raw_quote = raw_entry.get("quoted_text")
            raw_quote_digest = raw_entry.get("quoted_text_sha256")
            if not isinstance(raw_quote, str):
                add(f"{entry_path}.quoted_text must be a string")
                quote = None
            else:
                quote = raw_quote.replace("\r\n", "\n").replace("\r", "\n")
                if not quote:
                    add(f"{entry_path}.quoted_text must not be empty")
            if not isinstance(raw_quote_digest, str) or not SHA256_RE.fullmatch(
                raw_quote_digest.strip()
            ):
                add(f"{entry_path}.quoted_text_sha256 must be 64 hexadecimal characters")
            elif quote is not None and hashlib.sha256(quote.encode("utf-8")).hexdigest() != raw_quote_digest.strip().lower():
                add(
                    f"{entry_path}.quoted_text_sha256 does not match the normalized quoted_text bytes"
                )

            excerpt = (
                normalized_source_line_excerpt(
                    node_evidence_lines, line_start, line_end
                )
                if valid_lines
                else None
            )
            if quote is not None and excerpt is not None and quote != excerpt:
                add(
                    f"{entry_path}.quoted_text does not equal the exact normalized source "
                    "line slice"
                )
            if (
                candidate == node_evidence_artifact_path
                and valid_lines
                and excerpt is not None
            ):
                actual_anchors[(str(node_evidence_artifact_path), line_start, line_end)] += 1

        if compare_anchor_counters:
            missing_anchors = expected_anchors - actual_anchors
            extra_anchors = actual_anchors - expected_anchors
            if missing_anchors:
                rendered = ", ".join(
                    f"{start}-{end}" for (_, start, end), count in sorted(missing_anchors.items()) for _ in range(count)
                )
                add(
                    f"{node_path}.source_anchor_evidence is missing declared source anchor "
                    f"line range(s): {rendered}"
                )
            if extra_anchors:
                rendered = ", ".join(
                    f"{start}-{end}" for (_, start, end), count in sorted(extra_anchors.items()) for _ in range(count)
                )
                add(
                    f"{node_path}.source_anchor_evidence has undeclared or duplicate source "
                    f"anchor line range(s): {rendered}"
                )
    return findings


def user_approved_scope_exclusion_map_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Fail closed on malformed user-approved exclusions in a source map."""

    findings: list[Finding] = []
    severity = finding_severity(status)

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(manifest_path), message))

    for node_path, node in user_approved_scope_exclusion_nodes(payload):
        if node.get("claim_bearing") is not True:
            add(
                f"{node_path}.user_approved_scope_exclusion must keep the source "
                "assertion claim_bearing: true"
            )
        if str(node.get("source_scope_classification") or "").strip():
            add(
                f"{node_path}.user_approved_scope_exclusion cannot coexist with "
                "source_scope_classification"
            )
        scope_error = source_inventory_item_user_approved_scope_exclusion_error(
            _semantic_contract_scope_item_context(payload, node)
        )
        if scope_error:
            add(f"{node_path}.{scope_error}")
        for error in user_approved_scope_exclusion_errors(
            folder,
            node.get(USER_APPROVED_SCOPE_EXCLUSION),
            expected_source_locator=node.get("source_location"),
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        ):
            add(f"{node_path}.{error}")
    return findings


def source_map_scope_integrity_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: object,
) -> list[Finding]:
    """Fail closed on raw source-map shape and presentation smuggling.

    Coverage selection is deliberately *not* a parsing or integrity boundary.
    A source item cannot escape review by being made non-object, given an
    unknown presentation kind, or classified as prose despite its own visible
    named-theory presentation.  This lane therefore traverses the raw map
    before normal/deep selection, and never consults map keys or Lean route
    names to decide whether an item is a source claim.
    """

    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(manifest_path), message))

    if not isinstance(payload, dict):
        add("source statement inventory must be a JSON object")
        return findings
    for error in source_map_structural_errors(
        payload.get("items"),
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            payload
        ),
    ):
        add(error)
    if typed_route_validation_required(payload):
        try:
            EvidenceRouteSet.from_source_map(payload)
        except CloseoutPipelineError as exc:
            add("typed_evidence_routes: " + str(exc))
    return findings


def source_coverage_mode_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: object,
) -> tuple[str, list[Finding]]:
    """Return the selected mode plus configuration/closeout findings.

    Legacy discovery may use the normal default, but every closeout status has
    to record its source scope explicitly.  That prevents an old map from
    silently changing meaning when scope policy evolves.
    """

    mode, mode_error = source_coverage_mode_from_map(payload)
    migration_error = source_coverage_mode_migration_error(
        payload, require_explicit=status in CLOSEOUT_STATUSES
    )
    deep_error = deep_source_coverage_attestation_error(payload, mode)
    messages = [message for message in (mode_error, migration_error, deep_error) if message]
    # ``migration_error`` includes malformed/invalid mode diagnostics from
    # the authoritative helper, so do not duplicate the same message.
    unique_messages = list(dict.fromkeys(messages))
    severity = finding_severity(status)
    findings = [
        Finding(severity, folder.name, rel(manifest_path), message)
        for message in unique_messages
    ]
    return mode, findings


def scoped_source_map_payload(
    payload: dict[str, Any],
    mode: str,
    *,
    folder: Path | None = None,
    repository_root: Path | None = None,
    context: EvidenceRunContext | None = None,
) -> tuple[dict[str, Any], dict[str, dict[str, Any]]]:
    """Project per-item source obligations to the active coverage surface.

    Top-level source-artifact data is preserved, while only source items in
    the configured ordinary/deep surface (plus explicit correction/exception
    rows) remain for quote and exact-contract validators. When current paper
    bytes are available, exact source-index/anchor reconciliation contributes
    an additional semantic selector without replacing the legacy row selector.
    Raw-map integrity must be checked separately with
    ``source_map_scope_integrity_findings``.
    """

    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return dict(payload), {}
    indexed_item_ids = (
        source_index_byte_pinned_anchor_item_ids(
            folder,
            payload,
            mode,
            repository_root=repository_root,
            context=context,
        )
        if folder is not None
        else set()
    )
    selected = filter_source_map_items_for_proof_obligations(
        raw_items,
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            payload
        ),
        additional_selected_item_ids=indexed_item_ids,
    )
    for raw_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict) or not str(raw_key).strip():
            continue
        # A nonempty source-defect route is an explicit proof-fidelity
        # obligation, even when its source presentation is outside ordinary
        # named-theory coverage.  Retain it for evidence integrity so a
        # `repaired_in_lean` ledger entry cannot be made to look unrouted by
        # classifying its source presentation as a formula, figure, or other
        # nonordinary display.  This does not alter the paper-facing coverage
        # selector, which remains owned by source_coverage_scope.
        raw_defect_ids = raw_item.get("source_defect_ids")
        has_defect_routing_obligation = (
            bool(raw_defect_ids)
            if isinstance(raw_defect_ids, list)
            else raw_defect_ids is not None
        )
        if has_defect_routing_obligation:
            selected[str(raw_key)] = raw_item
    scoped_payload = dict(payload)
    scoped_payload["items"] = selected
    return scoped_payload, selected


def source_named_result_inventory_review_errors(
    payload: object,
    *,
    require_explicit: bool,
    presentation_digest: str | None = None,
    candidate_digest: str | None = None,
) -> list[str]:
    """Validate the source-pinned receipt for named-result discovery.

    The receipt is a curator's completeness attestation, not a Lean route or a
    theorem proof.  Its only role is to make the boundary of the ordinary
    named-theory inventory explicit, including source formats with custom TeX
    environments that a generic extractor cannot recognize on its own.
    """

    if not isinstance(payload, dict):
        return ["named-result inventory requires a readable paper_statement_map.json"]
    review = payload.get(SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY)
    if review is None and not require_explicit:
        return []
    if not isinstance(review, dict):
        return [
            "source-coverage closeout requires "
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY} with a source-pinned complete: true attestation"
        ]
    errors: list[str] = []
    if not schema_version_is_exact(
        review.get("schema"), SOURCE_NAMED_RESULT_INVENTORY_REVIEW_SCHEMA
    ):
        errors.append(
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.schema must be "
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_SCHEMA}"
        )
    if review.get("complete") is not True:
        errors.append(
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.complete must be true"
        )
    for field in ("validator", "method"):
        if not isinstance(review.get(field), str) or not review[field].strip():
            errors.append(f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.{field} is required")
    validated_at = str(review.get("validated_at") or "").strip()
    if not USER_APPROVED_SCOPE_EXCLUSION_TIMESTAMP_RE.fullmatch(validated_at):
        errors.append(
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.validated_at must be an ISO-like timestamp"
        )
    expected_source_digest = str(payload.get("source_artifact_sha256") or "").strip().lower()
    recorded_source_digest = str(review.get("source_artifact_sha256") or "").strip().lower()
    if not SHA256_RE.fullmatch(expected_source_digest):
        errors.append(
            "named-result inventory requires a canonical source_artifact_sha256"
        )
    elif recorded_source_digest != expected_source_digest:
        errors.append(
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY} must pin the current source_artifact_sha256"
        )
    if presentation_digest is not None:
        recorded_presentation_digest = str(
            review.get("discovered_named_result_sha256") or ""
        ).strip().lower()
        if not SHA256_RE.fullmatch(recorded_presentation_digest):
            errors.append(
                f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.discovered_named_result_sha256 is required"
            )
        elif recorded_presentation_digest != presentation_digest:
            errors.append(
                f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.discovered_named_result_sha256 "
                "does not match the current source-only named-result index"
            )
    if candidate_digest is not None:
        recorded_candidate_digest = str(
            review.get("discovered_candidate_presentation_sha256") or ""
        ).strip().lower()
        if not SHA256_RE.fullmatch(recorded_candidate_digest):
            errors.append(
                f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}."
                "discovered_candidate_presentation_sha256 is required"
            )
        elif recorded_candidate_digest != candidate_digest:
            errors.append(
                f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}."
                "discovered_candidate_presentation_sha256 does not match the "
                "current source-only candidate index"
            )
    return errors


def source_named_result_presentation_kinds(
    payload: object,
) -> tuple[object | None, object | None]:
    """Return explicit source-presentation classification tables from the receipt.

    The table is deliberately attached to the source-pinned inventory receipt,
    rather than to a Lean route or a source-map item.  They are only needed
    when a document class, macro package, or PDF transcript uses visible
    theorem-like presentations that cannot be classified from canonical text
    alone.  The source-only extractor performs value-level validation.
    """

    if not isinstance(payload, dict):
        return None, None
    review = payload.get(SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY)
    if not isinstance(review, dict):
        return None, None
    return review.get("environment_kinds"), review.get("heading_kinds")


_RENUMBERED_RESTATEMENT_TEXT_RE = re.compile(
    r"\bre(?:state|stated|statement)\b", re.IGNORECASE
)


def renumbered_presentation_alias_evidence_error(
    relation: object,
    *,
    folder: Path,
    artifact_path: Path,
    source_lines: list[str],
    alias_label: str,
    canonical_label: str,
) -> str:
    """Validate source content that expressly relates two differently labelled results.

    A map key, a Lean declaration, or two superficially similar statements do
    not establish that different visible labels designate one result. The
    narrow exception exists only where the current source itself says it is
    restating the two independently discovered presentations.
    """

    if not isinstance(relation, dict):
        return "has no readable repeated-presentation relation metadata"
    evidence = relation.get(SOURCE_PRESENTATION_ALIAS_RENUMBERED_EVIDENCE_FIELD)
    if not isinstance(evidence, dict):
        return "has no byte-pinned source relation evidence"

    required = {
        "path",
        "line_start",
        "line_end",
        "quoted_text",
        "quoted_text_sha256",
    }
    missing = sorted(required - set(evidence))
    if missing:
        return "source relation evidence is missing " + ", ".join(missing)

    candidate, path_error = resolve_paper_source_path(folder, evidence.get("path"))
    if candidate is None or candidate != artifact_path:
        return "source relation evidence does not identify the current pinned source artifact" + (
            f" ({path_error})" if path_error else ""
        )
    line_start = evidence.get("line_start")
    line_end = evidence.get("line_end")
    if (
        not isinstance(line_start, int)
        or isinstance(line_start, bool)
        or not isinstance(line_end, int)
        or isinstance(line_end, bool)
    ):
        return "source relation evidence has non-integer line bounds"
    expected = normalized_source_line_excerpt(source_lines, line_start, line_end)
    if expected is None:
        return "source relation evidence has out-of-range line bounds"
    quote = evidence.get("quoted_text")
    digest = evidence.get("quoted_text_sha256")
    if not isinstance(quote, str) or not quote:
        return "source relation evidence has no quoted source text"
    normalized_quote = quote.replace("\r\n", "\n").replace("\r", "\n")
    if normalized_quote != expected:
        return "source relation evidence is not the exact current source excerpt"
    if (
        not isinstance(digest, str)
        or not SHA256_RE.fullmatch(digest.strip())
        or hashlib.sha256(normalized_quote.encode("utf-8")).hexdigest()
        != digest.strip().lower()
    ):
        return "source relation evidence has an invalid current quote digest"
    if not _RENUMBERED_RESTATEMENT_TEXT_RE.search(normalized_quote):
        return "source relation evidence does not materially state a restatement"

    def mentions_visible_label(label: str) -> bool:
        return bool(
            re.search(
                r"(?<![A-Za-z0-9])" + re.escape(label) + r"(?![A-Za-z0-9])",
                normalized_quote,
                flags=re.IGNORECASE,
            )
        )

    if not mentions_visible_label(alias_label) or not mentions_visible_label(
        canonical_label
    ):
        return (
            "source relation evidence must name both independently discovered visible labels"
        )
    return ""


def source_named_result_inventory_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Reconcile independently discovered named source results to map spans.

    This is intentionally a source-only completeness check.  It does not read
    source-map keys, ``source_kind``, Lean declarations, or review-row names to
    decide whether a source result exists.  The selector is used only after a
    result is discovered, so a deep-only map row cannot absorb a named theorem
    outside the ordinary coverage surface.
    """

    explicit_file_bytes_override = file_bytes_override is not None
    if file_bytes_override is None and context is not None:
        file_bytes_override = context.file_bytes_override()

    # A named-result receipt certifies the *complete* ordinary source surface.
    # A partially formalized or conditional paper can still use this validator
    # when it has supplied a receipt, but must not be treated as having made
    # that full-closeout claim merely by publishing an intermediate status.
    require_receipt = status in FULL_CLOSEOUT_STATUSES
    review_present = SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY in payload
    inventory_items = payload.get("items")
    resolved_item_ids = {
        item_id
        for item_id, item in (
            inventory_items.items() if isinstance(inventory_items, dict) else []
        )
        if source_item_effective_route_policy(item)["is_source_resolved_within_paper"]
    }
    if not require_receipt and not review_present and not resolved_item_ids:
        return []

    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(manifest_path), message))

    def add_receipt_errors(
        presentation_digest: str | None = None,
        candidate_digest: str | None = None,
    ) -> None:
        for error in source_named_result_inventory_review_errors(
            payload,
            require_explicit=require_receipt,
            presentation_digest=presentation_digest,
            candidate_digest=candidate_digest,
        ):
            add(error)
        for error in current_closeout_review_policy_errors(
            folder,
            payload,
            file_bytes_override=file_bytes_override,
        ):
            add(error)

    if require_receipt and payload.get(SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY) is not True:
        add(
            "named-result inventory closeout requires "
            f"{SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY}: true so source-span coverage is byte-verified"
        )

    pin_findings = source_artifact_pin_findings(
        folder,
        status,
        manifest_path,
        payload,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    )
    if pin_findings:
        # Without current source bytes there is no source-only presentation
        # digest to validate.  Still report the basic receipt contract once,
        # rather than duplicating it before and after the failed read.
        add_receipt_errors()
        return findings + pin_findings

    artifact_path, artifact_path_error = resolve_paper_source_path(
        folder, payload.get("source_artifact_path")
    )
    if artifact_path is None:
        add(
            "cannot resolve canonical source artifact for named-result inventory: "
            + artifact_path_error
        )
        add_receipt_errors()
        return findings
    if artifact_path.suffix.lower() not in TEXT_SOURCE_SUFFIXES:
        add(
            "named-result inventory reconciliation requires a UTF-8 text or TeX canonical "
            "source artifact, not only a binary/PDF pin"
        )
        add_receipt_errors()
        return findings
    try:
        source_text = normalized_source_text(
            _exact_file_bytes(artifact_path, file_bytes_override)
        )
    except UnicodeDecodeError:
        add(
            "named-result inventory reconciliation requires a UTF-8 text or TeX canonical source artifact"
        )
        add_receipt_errors()
        return findings
    except (OSError, RuntimeError) as error:
        add(f"cannot read canonical source artifact for named-result inventory: {error}")
        add_receipt_errors()
        return findings

    prose_definition_ids, prose_definition_errors = (
        source_vocabulary_definition_binding_item_ids(
            folder,
            payload,
            repository_root=ROOT,
            file_bytes_override=file_bytes_override,
        )
    )
    for error in prose_definition_errors:
        add("source prose-definition inventory: " + error)

    source_format = "tex" if artifact_path.suffix.lower() == ".tex" else "text"
    environment_kinds, heading_kinds = source_named_result_presentation_kinds(payload)
    review = payload.get(SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY)
    candidate_dispositions = (
        review.get("candidate_presentations")
        if isinstance(review, Mapping) and "candidate_presentations" in review
        else None
    )
    try:
        presentation_inventory = reviewed_source_presentation_inventory(
            source_text,
            source_path=str(payload.get("source_artifact_path") or ""),
            source_format=source_format,
            environment_kinds=environment_kinds,
            heading_kinds=heading_kinds,
            candidate_dispositions=candidate_dispositions,
        )
        presentations = list(presentation_inventory.classified)
    except (TypeError, ValueError) as error:
        add(
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY} presentation classification is invalid: {error}"
        )
        add_receipt_errors()
        return findings
    source_coverage_mode, _mode_error = source_coverage_mode_from_map(payload)
    replaced_definition_spans = source_prose_definition_replaced_named_presentation_spans(
        folder,
        payload,
        presentations,
        repository_root=ROOT,
        file_bytes_override=file_bytes_override,
    )
    # The receipt covers the semantic source surface selected by the active
    # policy, not every mechanically recognized display. In normal mode this
    # omits standalone Formula/Equation/Algorithm presentations;
    # unclassified named presentations remain included so they still block a
    # closeout until the source receipt classifies them.
    receipt_presentations = [
        presentation
        for presentation in presentations
        if source_named_presentation_in_coverage_scope(
            presentation.kind, source_coverage_mode
        )
        and not (
            presentation.kind == "definition"
            and (presentation.line_start, presentation.line_end)
            in replaced_definition_spans
        )
    ]
    presentation_digest = named_result_presentations_sha256(receipt_presentations)
    candidate_digest = (
        presentation_inventory.candidate_sha256
        if candidate_dispositions is not None
        else None
    )
    add_receipt_errors(presentation_digest, candidate_digest)

    for presentation in presentations:
        if presentation.kind != UNCLASSIFIED_NAMED_PRESENTATION_KIND:
            continue
        add(
            "independent source named-result index found an unclassified named "
            f"presentation `{presentation.label}` at "
            f"{payload.get('source_artifact_path')}:{presentation.line_start}-{presentation.line_end}; "
            "classify its visible source environment or heading in "
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.environment_kinds or "
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.heading_kinds before closeout"
        )

    scoped_payload, _scoped_items = scoped_source_map_payload(
        payload,
        source_coverage_mode,
        folder=folder,
        repository_root=ROOT,
        context=context,
    )
    # ``scoped_payload`` retains legacy and explicit obligation rows for their
    # own validators. The source-heading coverage decision below is stricter:
    # it can use only rows independently reconciled to current bytes through
    # exact anchors, never a legacy source_kind/text selector or source_location.
    del scoped_payload
    raw_items = payload.get("items")
    if isinstance(raw_items, dict):
        for raw_item in raw_items.values():
            for error in source_presentation_reconciliation_errors(
                raw_item,
                presentations,
                source_text=source_text,
                source_path=str(payload.get("source_artifact_path") or ""),
            ):
                add(error)
    strict_items = (
        {
            # Keep only exact anchors for the second reconciliation. This
            # prevents a broad source_location or any map metadata from
            # absorbing a different result after strict selection.
            item_id: {
                "source_anchor_evidence": raw_items[item_id].get(
                    "source_anchor_evidence"
                ),
                **(
                    {
                        SOURCE_PRESENTATION_RECONCILIATION_FIELD: raw_items[
                            item_id
                        ].get(SOURCE_PRESENTATION_RECONCILIATION_FIELD)
                    }
                    if SOURCE_PRESENTATION_RECONCILIATION_FIELD in raw_items[item_id]
                    else {}
                ),
            }
            for item_id in source_index_byte_pinned_anchor_item_ids(
                folder,
                payload,
                source_coverage_mode,
                context=context,
                file_bytes_override=(
                    file_bytes_override if explicit_file_bytes_override else None
                ),
            )
            if isinstance(raw_items, dict) and isinstance(raw_items.get(item_id), dict)
        }
        if isinstance(raw_items, dict)
        else {}
    )
    in_scope_presentations = [
        presentation
        for presentation in presentations
        if source_named_presentation_in_coverage_scope(
            presentation.kind, source_coverage_mode
        )
        and not (
            presentation.kind == "definition"
            and (presentation.line_start, presentation.line_end)
            in replaced_definition_spans
        )
        and presentation.kind
        not in {
            UNCLASSIFIED_NAMED_PRESENTATION_KIND,
            OPEN_NAMED_PRESENTATION_KIND,
        }
    ]
    reconciliations = reconcile_named_result_presentations(
        in_scope_presentations,
        strict_items,
        source_text=source_text,
        source_path=str(payload.get("source_artifact_path") or ""),
    )
    presentations_by_item: dict[str, set[tuple[str, int, int]]] = {}
    presentation_details_by_item: dict[
        str, set[tuple[str, str, int, int, str]]
    ] = {}
    for reconciliation in reconciliations:
        presentation = reconciliation.presentation
        presentation_identity = (
            presentation.kind,
            presentation.line_start,
            presentation.line_end,
        )
        presentation_details = (
            presentation.kind,
            presentation.label,
            presentation.line_start,
            presentation.line_end,
            presentation.presentation,
        )
        for match in reconciliation.matches:
            presentations_by_item.setdefault(match.item_id, set()).add(
                presentation_identity
            )
            presentation_details_by_item.setdefault(match.item_id, set()).add(
                presentation_details
            )
    for item_id, matched_presentations in sorted(presentations_by_item.items()):
        if len(matched_presentations) > 1:
            add(
                "in-scope source-map item `"
                + item_id
                + "` spans multiple independent discovered named results; split it into "
                "one tightly anchored source item per named presentation"
            )
    # A proof appendix may visibly restate an earlier numbered theorem.  The
    # source-only alias relation keeps both independently discovered spans in
    # the inventory, while requiring byte-pinned evidence that they present
    # the same visible source result.  The human semantic basis in the map
    # covers hypotheses/scope/conclusion; this check verifies that it is tied
    # to two distinct current source presentations rather than a map or Lean
    # naming convention.
    presentation_aliases, _presentation_alias_errors = source_presentation_aliases(
        raw_items
    )
    prose_aliases = source_prose_definition_alias_pairs(
        folder, payload, repository_root=ROOT,
        file_bytes_override=(
            file_bytes_override if explicit_file_bytes_override else None
        ),
    )
    for alias_item, canonical_item in sorted(presentation_aliases.items()):
        if prose_aliases.get(alias_item) == canonical_item:
            continue
        alias_presentations = presentation_details_by_item.get(alias_item, set())
        canonical_presentations = presentation_details_by_item.get(
            canonical_item, set()
        )
        if len(alias_presentations) != 1 or len(canonical_presentations) != 1:
            add(
                "repeated-source-presentation alias `"
                + alias_item
                + "` and canonical item `"
                + canonical_item
                + "` must each have exactly one byte-pinned in-scope source presentation"
            )
            continue
        alias_presentation = next(iter(alias_presentations))
        canonical_presentation = next(iter(canonical_presentations))
        if alias_presentation[0] != canonical_presentation[0]:
            add(
                "repeated-source-presentation alias `"
                + alias_item
                + "` does not preserve the canonical visible source result kind"
            )
        elif alias_presentation[1] != canonical_presentation[1]:
            alias_map_item = raw_items.get(alias_item)
            relation = (
                alias_map_item.get("source_presentation_alias")
                if isinstance(alias_map_item, dict)
                else None
            )
            label_relation = (
                relation.get(SOURCE_PRESENTATION_ALIAS_LABEL_RELATION_FIELD)
                if isinstance(relation, dict)
                else None
            )
            if (
                label_relation
                != SOURCE_PRESENTATION_ALIAS_EXPLICIT_RENUMBERED_RESTATEMENT
            ):
                add(
                    "repeated-source-presentation alias `"
                    + alias_item
                    + "` does not preserve the canonical visible source result label; "
                    "a differently labelled presentation requires explicit current source "
                    "renumbered-restatement evidence"
                )
            else:
                relation_error = renumbered_presentation_alias_evidence_error(
                    relation,
                    folder=folder,
                    artifact_path=artifact_path,
                    source_lines=normalized_source_lines(source_text),
                    alias_label=alias_presentation[1],
                    canonical_label=canonical_presentation[1],
                )
                if relation_error:
                    add(
                        "repeated-source-presentation alias `"
                        + alias_item
                        + "` has invalid explicit renumbered-restatement evidence: "
                        + relation_error
                    )
        if alias_presentation[2:4] == canonical_presentation[2:4]:
            add(
                "repeated-source-presentation alias `"
                + alias_item
                + "` must anchor a distinct source presentation from canonical item `"
                + canonical_item
                + "`"
            )
    for presentation in uncovered_named_result_presentations(reconciliations):
        add(
            "independent source named-result index found an uncovered "
            f"{presentation.kind} presentation `{presentation.label}` at "
            f"{payload.get('source_artifact_path')}:{presentation.line_start}-{presentation.line_end}; "
            "add an in-scope source-map item anchored to this source span"
        )

    # A named conjecture/open question is not a theorem-proof target, but it
    # is still part of the source inventory.  Reconcile it to the raw map so
    # normal named-theory scope cannot silently erase it, then require an
    # explicit open/resolved disposition and an exact anchor. A conjecture
    # resolved in this paper must point directly to a selected, independently
    # source-pinned result, not to another nonresult inventory disposition.
    all_items = raw_items if isinstance(raw_items, dict) else {}
    open_presentations = [
        presentation
        for presentation in presentations
        if presentation.kind == OPEN_NAMED_PRESENTATION_KIND
    ]
    open_reconciliations = reconcile_named_result_presentations(
        open_presentations,
        all_items,
        source_text=source_text,
        source_path=str(payload.get("source_artifact_path") or ""),
    )
    validated_resolved_item_ids: set[str] = set()
    for reconciliation in open_reconciliations:
        presentation = reconciliation.presentation
        if not reconciliation.matches:
            add(
                "independent source named-result index found an uncatalogued named "
                f"open presentation `{presentation.label}` at "
                f"{payload.get('source_artifact_path')}:{presentation.line_start}-{presentation.line_end}; "
                "add a byte-pinned source-map item with an explicit source-declared-open "
                "or source-resolved-within-paper disposition"
            )
            continue
        valid_open_disposition = False
        for match in reconciliation.matches:
            raw_item = all_items.get(match.item_id)
            if not isinstance(raw_item, dict):
                continue
            has_exact_anchor = any(
                evidence.startswith("source_anchor_evidence[")
                for evidence in match.evidence
            )
            route_policy = source_item_effective_route_policy(raw_item)
            valid_disposition = route_policy["is_source_declared_open_nonresult"]
            if route_policy["is_source_resolved_within_paper"]:
                target_id = str(raw_item.get("subsumed_by_source_item") or "").strip()
                target = all_items.get(target_id)
                target_contract = (
                    target.get("semantic_contract")
                    if isinstance(target, dict)
                    else None
                )
                target_presentations = presentations_by_item.get(target_id, set())
                valid_disposition = bool(
                    target_id != match.item_id
                    and isinstance(target, dict)
                    and target.get("claim_bearing") is True
                    and source_item_effective_route_policy(target)["allows_direct_route"]
                    and not str(target.get("subsumed_by_source_item") or "").strip()
                    and isinstance(target_contract, dict)
                    and all(
                        isinstance(target_contract.get(field), str)
                        and target_contract[field].strip()
                        for field in ("spec_declaration", "evidence_declaration")
                    )
                    and len(target_presentations) == 1
                    and next(iter(target_presentations))[0]
                    in THEOREM_REALIZATION_SOURCE_KINDS
                )
            if (
                has_exact_anchor
                and valid_disposition
                and str(raw_item.get("scope_reason") or "").strip()
                and str(raw_item.get("source_evidence") or "").strip()
            ):
                valid_open_disposition = True
                if route_policy["is_source_resolved_within_paper"]:
                    validated_resolved_item_ids.add(match.item_id)
        if not valid_open_disposition:
            add(
                "named open presentation `"
                + presentation.label
                + "` must be anchored by a source-map item with source_kind "
                "`open_problem`, claim_bearing: false, "
                "source_scope_classification: "
                "`source_declared_open_nonresult_observation`, and "
                "coverage_status/protocol_role: `source_declared_open`; or "
                "`source_resolved_within_paper_observation` with "
                "coverage_status/protocol_role: `subsumed_by_selected_result` and "
                "subsumed_by_source_item naming a distinct selected result with a "
                "semantic contract and exactly one byte-pinned named-result presentation. "
                "Both dispositions require source-facing reason/evidence"
            )
    # This inventory also owns the semantic-contract nonclaim exemption.
    # Every resolved row must therefore have passed the exact presentation and
    # selected-target checks, even when another row covers the same heading.
    for item_id in sorted(resolved_item_ids - validated_resolved_item_ids):
        add(
            f"source-resolved item `{item_id}` lacks a byte-pinned named open "
            "presentation with a valid distinct selected-result subsumption"
        )
    return findings


def check_source_manifest(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    file_bytes_override = (
        context.file_bytes_override() if context is not None else None
    )
    path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(path, context)
    if payload is None:
        return [
            Finding(
                finding_severity(status),
                folder.name,
                rel(path),
                "source statement inventory is missing or invalid; add "
                "audit/paper_statement_map.json with top-level "
                "source_artifact_path and source_artifact_sha256",
            )
        ]
    if not isinstance(payload, dict):
        return source_map_scope_integrity_findings(folder, status, path, payload)

    findings = source_map_scope_integrity_findings(folder, status, path, payload)
    source_coverage_mode, mode_findings = source_coverage_mode_findings(
        folder, status, path, payload
    )
    findings.extend(mode_findings)
    pin_findings = source_artifact_pin_findings(
        folder,
        status,
        path,
        payload,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    )
    if pin_findings:
        return findings + pin_findings
    findings.extend(
        source_named_result_inventory_findings(
            folder,
            status,
            path,
            payload,
            require_source_bytes=require_source_bytes,
            context=context,
        )
    )
    scoped_payload, _coverage_items = scoped_source_map_payload(
        payload,
        source_coverage_mode,
        folder=folder,
        repository_root=ROOT,
        context=context,
    )
    findings.extend(
        source_anchor_evidence_findings(
            folder,
            status,
            path,
            scoped_payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        semantic_context_requirement_findings(
            folder,
            status,
            path,
            # Source-only context records govern how every selected Lean
            # statement is interpreted.  They are not themselves claim
            # coverage rows, so normal named-theory scoping must not make an
            # invalid convention/domain anchor disappear from the manifest
            # gate merely because its host item is otherwise out of scope.
            payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        user_approved_scope_exclusion_map_findings(
            folder,
            status,
            path,
            # Exclusions are deliberately removed from the ordinary coverage
            # projection.  Their authorization and exact source pin must
            # nevertheless be checked on the raw map, or a malformed
            # exclusion could disappear before its dedicated validator runs.
            payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    # Corrected targets are explicit governing-source repairs and retain their
    # all-map validation lane even under ordinary named-theory coverage.
    findings.extend(
        corrected_source_statement_map_findings(
            folder,
            status,
            payload,
            context=context,
        )
    )
    findings.extend(
        semantic_surface_inventory_findings(
            folder,
            status,
            # This validator owns its own active-surface projection.  Give it
            # the exact transaction snapshot, not the already projected copy,
            # so its source-index lookup reuses the transaction's authenticated
            # projection instead of reconciling the same source bytes again.
            payload,
            context=context,
        )
    )
    return findings


def _semantic_contract_scope_item_context(
    payload: dict[str, Any], raw_item: dict[str, Any]
) -> dict[str, Any]:
    """Attach canonical source-pin context needed by the source classifier.

    Statement-map rows inherit the canonical artifact pin from the map.  The
    dashboard validator expects that context directly on an item, so preserve
    any row-level pin (to detect a mismatch) and supply the canonical values as
    a comparison target.  No Lean or map-key data participates.
    """

    item = dict(raw_item)
    canonical_path = payload.get("source_artifact_path")
    canonical_digest = payload.get("source_artifact_sha256")
    if "source_artifact_path" not in item:
        item["source_artifact_path"] = canonical_path
    if "source_artifact_sha256" not in item:
        item["source_artifact_sha256"] = canonical_digest
    item["canonical_source_artifact_path"] = canonical_path
    item["canonical_source_artifact_sha256"] = canonical_digest
    return item


def _semantic_surface_string_list(
    raw_surface: dict[str, Any], field: str, errors: list[str], *, required: bool
) -> list[str]:
    """Read one literal-token list from a semantic-surface contract."""

    value = raw_surface.get(field)
    if value is None:
        if required:
            errors.append(f"semantic_surface.{field} must be a nonempty string list")
        return []
    if not isinstance(value, list) or not value:
        errors.append(f"semantic_surface.{field} must be a nonempty string list")
        return []
    if any(not isinstance(token, str) or not token.strip() for token in value):
        errors.append(f"semantic_surface.{field} must contain only nonempty strings")
        return []
    tokens = [token.strip() for token in value]
    if len(set(tokens)) != len(tokens):
        errors.append(f"semantic_surface.{field} must not repeat a token")
    return tokens


def _semantic_surface_pattern_string_list(
    raw_pattern: dict[str, Any], field: str, prefix: str, errors: list[str]
) -> list[str]:
    """Read one optional nonempty string-list from a schema-3 pattern."""

    value = raw_pattern.get(field)
    if value is None:
        return []
    if not isinstance(value, list) or not value:
        errors.append(f"{prefix}.{field} must be a nonempty string list when present")
        return []
    if any(not isinstance(item, str) or not item.strip() for item in value):
        errors.append(f"{prefix}.{field} must contain only nonempty strings")
        return []
    normalized = [item.strip() for item in value]
    if len(normalized) != len(set(normalized)):
        errors.append(f"{prefix}.{field} must not repeat a value")
    return normalized



def _semantic_surface_result_schema_errors(
    raw_surface: dict[str, Any], errors: list[str]
) -> None:
    """Validate schema-3 result-only pattern contracts.

    This validator does not accept source tokens or suffixes.  The live gate
    resolves the fixed feature vocabulary against Lean's canonical result tree.
    """

    outer_binder_sha256 = raw_surface.get("outer_binder_sha256")
    if (
        not isinstance(outer_binder_sha256, str)
        or not SHA256_RE.fullmatch(outer_binder_sha256)
        or outer_binder_sha256 != outer_binder_sha256.lower()
    ):
        errors.append(
            "semantic_surface.outer_binder_sha256 must be a lowercase 64-hex "
            "digest of the elaborated outer binder interface"
        )

    raw_patterns = raw_surface.get("required_result_patterns")
    if not isinstance(raw_patterns, list) or not raw_patterns:
        errors.append(
            "semantic_surface.required_result_patterns must be a nonempty list"
        )
        return

    ids: set[str] = set()
    captures: set[str] = set()
    equality_alias_captures: set[str] = set()
    equality_alias_capture_indices: dict[str, int] = {}
    equality_alias_consumers: dict[str, list[int]] = {}
    for index, raw_pattern in enumerate(raw_patterns):
        prefix = f"semantic_surface.required_result_patterns[{index}]"
        earlier_captures = set(captures)
        earlier_equality_alias_captures = set(equality_alias_captures)
        if not isinstance(raw_pattern, dict):
            errors.append(f"{prefix} must be an object")
            continue
        unknown_fields = sorted(
            set(raw_pattern) - SEMANTIC_SURFACE_RESULT_PATTERN_FIELDS
        )
        if unknown_fields:
            errors.append(
                f"{prefix} has unknown field(s): " + ", ".join(unknown_fields)
            )

        pattern_id = raw_pattern.get("id")
        if not isinstance(pattern_id, str) or not pattern_id.strip():
            errors.append(f"{prefix}.id must be a nonempty string")
        elif pattern_id in ids:
            errors.append(f"{prefix}.id must not repeat `{pattern_id}`")
        else:
            ids.add(pattern_id)

        relation = raw_pattern.get("relation")
        if relation not in SEMANTIC_SURFACE_RESULT_RELATIONS:
            errors.append(
                f"{prefix}.relation must be one of "
                + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_RELATIONS))
            )

        features = _semantic_surface_pattern_string_list(
            raw_pattern, "all_features", prefix, errors
        )
        invalid_features = sorted(
            set(features) - SEMANTIC_SURFACE_RESULT_FEATURES
        )
        if invalid_features:
            errors.append(
                f"{prefix}.all_features contains unsupported feature(s): "
                + ", ".join(invalid_features)
            )

        raw_feature_counts = raw_pattern.get("minimum_feature_counts")
        feature_counts: dict[str, Any] = {}
        if raw_feature_counts is not None:
            if not isinstance(raw_feature_counts, dict) or not raw_feature_counts:
                errors.append(
                    f"{prefix}.minimum_feature_counts must be a nonempty object when present"
                )
            else:
                feature_counts = raw_feature_counts
                for feature, count in feature_counts.items():
                    if not isinstance(feature, str) or feature not in SEMANTIC_SURFACE_RESULT_FEATURES:
                        errors.append(
                            f"{prefix}.minimum_feature_counts has unsupported feature `{feature}`"
                        )
                    if (
                        not isinstance(count, int)
                        or isinstance(count, bool)
                        or count < 1
                    ):
                        errors.append(
                            f"{prefix}.minimum_feature_counts values must be positive integers"
                        )

        canonical_sha256 = raw_pattern.get("canonical_sha256")
        if canonical_sha256 is not None and (
            not isinstance(canonical_sha256, str)
            or not SHA256_RE.fullmatch(canonical_sha256)
            or canonical_sha256 != canonical_sha256.lower()
        ):
            errors.append(
                f"{prefix}.canonical_sha256 must be a lowercase 64-hex digest "
                "of the scope-normalized canonical result formula"
            )
        pattern_has_feature_constraint = bool(features or feature_counts)
        pattern_required_equality_aliases: set[str] = set()

        raw_operand_patterns = raw_pattern.get("operand_patterns")
        operand_patterns: list[Any] = []
        if raw_operand_patterns is not None:
            if relation == "any":
                errors.append(f"{prefix}.operand_patterns requires a relation with operands")
            if not isinstance(raw_operand_patterns, list) or not raw_operand_patterns:
                errors.append(
                    f"{prefix}.operand_patterns must be a nonempty list when present"
                )
            else:
                operand_patterns = raw_operand_patterns
                seen_sides: set[str] = set()
                allowed_sides = (
                    {"left", "right"}
                    if relation in {"eq", "iff", "lt", "le"}
                    else ({"argument"} if relation == "not" else set())
                )
                for operand_index, raw_operand in enumerate(operand_patterns):
                    operand_prefix = f"{prefix}.operand_patterns[{operand_index}]"
                    if not isinstance(raw_operand, dict):
                        errors.append(f"{operand_prefix} must be an object")
                        continue
                    unknown_operand = sorted(
                        set(raw_operand) - SEMANTIC_SURFACE_RESULT_OPERAND_PATTERN_FIELDS
                    )
                    if unknown_operand:
                        errors.append(
                            f"{operand_prefix} has unknown field(s): "
                            + ", ".join(unknown_operand)
                        )
                    side = raw_operand.get("side")
                    if side not in SEMANTIC_SURFACE_RESULT_OPERAND_SIDES:
                        errors.append(
                            f"{operand_prefix}.side must be one of "
                            + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_OPERAND_SIDES))
                        )
                    elif side not in allowed_sides:
                        errors.append(
                            f"{operand_prefix}.side is not valid for relation `{relation}`"
                        )
                    elif side in seen_sides:
                        errors.append(f"{operand_prefix}.side must not repeat `{side}`")
                    else:
                        seen_sides.add(side)
                    operand_features = _semantic_surface_pattern_string_list(
                        raw_operand, "all_features", operand_prefix, errors
                    )
                    invalid_operand_features = sorted(
                        set(operand_features) - SEMANTIC_SURFACE_RESULT_FEATURES
                    )
                    if invalid_operand_features:
                        errors.append(
                            f"{operand_prefix}.all_features contains unsupported feature(s): "
                            + ", ".join(invalid_operand_features)
                        )
                    raw_operand_counts = raw_operand.get("minimum_feature_counts")
                    operand_counts: dict[str, Any] = {}
                    if raw_operand_counts is not None:
                        if not isinstance(raw_operand_counts, dict) or not raw_operand_counts:
                            errors.append(
                                f"{operand_prefix}.minimum_feature_counts must be a nonempty object when present"
                            )
                        else:
                            operand_counts = raw_operand_counts
                            for feature, count in operand_counts.items():
                                if (
                                    not isinstance(feature, str)
                                    or feature not in SEMANTIC_SURFACE_RESULT_FEATURES
                                ):
                                    errors.append(
                                        f"{operand_prefix}.minimum_feature_counts has unsupported feature `{feature}`"
                                    )
                                if (
                                    not isinstance(count, int)
                                    or isinstance(count, bool)
                                    or count < 1
                                ):
                                    errors.append(
                                        f"{operand_prefix}.minimum_feature_counts values must be positive integers"
                                    )
                    operand_captures = _semantic_surface_pattern_string_list(
                        raw_operand, "requires_captures", operand_prefix, errors
                    )
                    unknown_operand_captures = sorted(
                        set(operand_captures) - earlier_captures
                    )
                    if unknown_operand_captures:
                        errors.append(
                            f"{operand_prefix}.requires_captures must refer only to captures from earlier "
                            "patterns: " + ", ".join(unknown_operand_captures)
                        )
                    operand_equality_aliases = _semantic_surface_pattern_string_list(
                        raw_operand,
                        "requires_equality_aliases",
                        operand_prefix,
                        errors,
                    )
                    pattern_required_equality_aliases.update(
                        operand_equality_aliases
                    )
                    if operand_features or operand_counts:
                        pattern_has_feature_constraint = True
                    unknown_operand_equality_aliases = sorted(
                        set(operand_equality_aliases)
                        - earlier_equality_alias_captures
                    )
                    if unknown_operand_equality_aliases:
                        errors.append(
                            f"{operand_prefix}.requires_equality_aliases must refer only "
                            "to equality aliases from earlier patterns: "
                            + ", ".join(unknown_operand_equality_aliases)
                        )
                    if (
                        not operand_features
                        and not operand_counts
                        and not operand_captures
                        and not operand_equality_aliases
                    ):
                        errors.append(
                            f"{operand_prefix} must constrain a feature or earlier capture"
                        )

        require_distinct_operands = raw_pattern.get("require_distinct_operands")
        if require_distinct_operands is not None and not isinstance(
            require_distinct_operands, bool
        ):
            errors.append(f"{prefix}.require_distinct_operands must be boolean when present")
        elif require_distinct_operands is True and relation not in {"eq", "iff", "lt", "le"}:
            errors.append(
                f"{prefix}.require_distinct_operands requires eq, iff, lt, or le"
            )

        raw_guard_patterns = raw_pattern.get("guard_patterns")
        if raw_guard_patterns is not None:
            if not isinstance(raw_guard_patterns, list) or not raw_guard_patterns:
                errors.append(
                    f"{prefix}.guard_patterns must be a nonempty list when present"
                )
            else:
                for guard_index, raw_guard in enumerate(raw_guard_patterns):
                    guard_prefix = f"{prefix}.guard_patterns[{guard_index}]"
                    if not isinstance(raw_guard, dict):
                        errors.append(f"{guard_prefix} must be an object")
                        continue
                    unknown_guard = sorted(
                        set(raw_guard) - SEMANTIC_SURFACE_RESULT_GUARD_PATTERN_FIELDS
                    )
                    if unknown_guard:
                        errors.append(
                            f"{guard_prefix} has unknown field(s): "
                            + ", ".join(unknown_guard)
                        )
                    guard_relation = raw_guard.get("relation")
                    if guard_relation not in SEMANTIC_SURFACE_RESULT_RELATIONS:
                        errors.append(
                            f"{guard_prefix}.relation must be one of "
                            + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_RELATIONS))
                        )
                    guard_features = _semantic_surface_pattern_string_list(
                        raw_guard, "all_features", guard_prefix, errors
                    )
                    invalid_guard_features = sorted(
                        set(guard_features) - SEMANTIC_SURFACE_RESULT_FEATURES
                    )
                    if invalid_guard_features:
                        errors.append(
                            f"{guard_prefix}.all_features contains unsupported feature(s): "
                            + ", ".join(invalid_guard_features)
                        )
                    raw_guard_counts = raw_guard.get("minimum_feature_counts")
                    guard_counts: dict[str, Any] = {}
                    if raw_guard_counts is not None:
                        if not isinstance(raw_guard_counts, dict) or not raw_guard_counts:
                            errors.append(
                                f"{guard_prefix}.minimum_feature_counts must be a nonempty object when present"
                            )
                        else:
                            guard_counts = raw_guard_counts
                            for feature, count in guard_counts.items():
                                if (
                                    not isinstance(feature, str)
                                    or feature not in SEMANTIC_SURFACE_RESULT_FEATURES
                                ):
                                    errors.append(
                                        f"{guard_prefix}.minimum_feature_counts has unsupported feature `{feature}`"
                                    )
                                if (
                                    not isinstance(count, int)
                                    or isinstance(count, bool)
                                    or count < 1
                                ):
                                    errors.append(
                                        f"{guard_prefix}.minimum_feature_counts values must be positive integers"
                                    )
                    canonical_sha256 = raw_guard.get("canonical_sha256")
                    if canonical_sha256 is not None and (
                        not isinstance(canonical_sha256, str)
                        or not SHA256_RE.fullmatch(canonical_sha256)
                        or canonical_sha256 != canonical_sha256.lower()
                    ):
                        errors.append(
                            f"{guard_prefix}.canonical_sha256 must be a lowercase "
                            "64-hex digest of the scope-normalized canonical guard"
                        )
                    if (
                        guard_relation == "any"
                        and not guard_features
                        and not guard_counts
                        and canonical_sha256 is None
                    ):
                        errors.append(
                            f"{guard_prefix} must constrain a relation or exact feature"
                        )

        quantifier_shape = raw_pattern.get("quantifier_shape")
        if not isinstance(quantifier_shape, dict):
            errors.append(
                f"{prefix}.quantifier_shape must be an object with forall and exists counts"
            )
        else:
            unknown_quantifiers = sorted(
                set(quantifier_shape) - SEMANTIC_SURFACE_RESULT_QUANTIFIER_FIELDS
            )
            missing_quantifiers = sorted(
                SEMANTIC_SURFACE_RESULT_QUANTIFIER_FIELDS - set(quantifier_shape)
            )
            if unknown_quantifiers:
                errors.append(
                    f"{prefix}.quantifier_shape has unknown field(s): "
                    + ", ".join(unknown_quantifiers)
                )
            if missing_quantifiers:
                errors.append(
                    f"{prefix}.quantifier_shape is missing field(s): "
                    + ", ".join(missing_quantifiers)
                )
            for quantifier in SEMANTIC_SURFACE_RESULT_QUANTIFIER_FIELDS:
                count = quantifier_shape.get(quantifier)
                if (
                    not isinstance(count, int)
                    or isinstance(count, bool)
                    or count < 0
                ):
                    errors.append(
                        f"{prefix}.quantifier_shape.{quantifier} must be a nonnegative integer"
                    )

        capture = raw_pattern.get("capture")
        if capture is not None:
            if not isinstance(capture, dict):
                errors.append(f"{prefix}.capture must be an object when present")
            else:
                unknown_capture = sorted(
                    set(capture) - SEMANTIC_SURFACE_RESULT_CAPTURE_FIELDS
                )
                if unknown_capture:
                    errors.append(
                        f"{prefix}.capture has unknown field(s): "
                        + ", ".join(unknown_capture)
                    )
                feature = capture.get("feature")
                if feature not in SEMANTIC_SURFACE_RESULT_CAPTURE_FEATURES:
                    errors.append(
                        f"{prefix}.capture.feature must be one of "
                        + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_CAPTURE_FEATURES))
                    )
                mode = capture.get("mode", "root")
                if mode not in SEMANTIC_SURFACE_RESULT_CAPTURE_MODES:
                    errors.append(
                        f"{prefix}.capture.mode must be one of "
                        + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_CAPTURE_MODES))
                    )
                capture_name = capture.get("as")
                if not isinstance(capture_name, str) or not capture_name.strip():
                    errors.append(f"{prefix}.capture.as must be a nonempty string")
                elif (
                    capture_name in captures
                    or capture_name in equality_alias_captures
                ):
                    errors.append(
                        f"{prefix}.capture.as must not repeat a capture or equality alias "
                        f"name `{capture_name}`"
                    )
                else:
                    captures.add(capture_name)
                distinct_from = _semantic_surface_pattern_string_list(
                    capture, "distinct_from", f"{prefix}.capture", errors
                )
                unknown_distinct = sorted(set(distinct_from) - earlier_captures)
                if unknown_distinct:
                    errors.append(
                        f"{prefix}.capture.distinct_from must refer only to captures from "
                        "earlier patterns: " + ", ".join(unknown_distinct)
                    )

        equality_alias_capture = raw_pattern.get("equality_alias_capture")
        if equality_alias_capture is not None:
            if not isinstance(equality_alias_capture, dict):
                errors.append(
                    f"{prefix}.equality_alias_capture must be an object when present"
                )
            else:
                unknown_alias_fields = sorted(
                    set(equality_alias_capture)
                    - SEMANTIC_SURFACE_RESULT_EQUALITY_ALIAS_CAPTURE_FIELDS
                )
                if unknown_alias_fields:
                    errors.append(
                        f"{prefix}.equality_alias_capture has unknown field(s): "
                        + ", ".join(unknown_alias_fields)
                    )
                if relation != "eq":
                    errors.append(
                        f"{prefix}.equality_alias_capture requires relation `eq`"
                    )
                if capture is not None:
                    errors.append(
                        f"{prefix} may not combine capture and equality_alias_capture"
                    )
                alias_side = equality_alias_capture.get("alias_side")
                if alias_side not in {"left", "right"}:
                    errors.append(
                        f"{prefix}.equality_alias_capture.alias_side must be `left` or `right`"
                    )
                construction_feature = equality_alias_capture.get(
                    "construction_feature"
                )
                if construction_feature not in SEMANTIC_SURFACE_RESULT_FEATURES:
                    errors.append(
                        f"{prefix}.equality_alias_capture.construction_feature must be one "
                        "of "
                        + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_FEATURES))
                    )
                alias_name = equality_alias_capture.get("as")
                if not isinstance(alias_name, str) or not alias_name.strip():
                    errors.append(
                        f"{prefix}.equality_alias_capture.as must be a nonempty string"
                    )
                elif (
                    alias_name in equality_alias_captures
                    or alias_name in captures
                ):
                    errors.append(
                        f"{prefix}.equality_alias_capture.as must not repeat a capture name "
                        f"`{alias_name}`"
                    )
                else:
                    equality_alias_captures.add(alias_name)
                    equality_alias_capture_indices[alias_name] = index

        allow_leaf_reuse = raw_pattern.get("allow_leaf_reuse")
        if allow_leaf_reuse is not None and not isinstance(allow_leaf_reuse, bool):
            errors.append(f"{prefix}.allow_leaf_reuse must be boolean when present")
        elif equality_alias_capture is not None and allow_leaf_reuse is True:
            errors.append(
                f"{prefix}.equality_alias_capture forbids allow_leaf_reuse so a later "
                "result leaf must consume the alias"
            )

        required_captures = _semantic_surface_pattern_string_list(
            raw_pattern, "requires_captures", prefix, errors
        )
        unknown_captures = sorted(set(required_captures) - earlier_captures)
        if unknown_captures:
            errors.append(
                f"{prefix}.requires_captures must refer only to captures from earlier "
                "patterns: " + ", ".join(unknown_captures)
            )
        if required_captures and relation in {"eq", "iff", "lt", "le"}:
            if not operand_patterns:
                errors.append(
                    f"{prefix}.requires_captures on a binary relation requires "
                    "operand_patterns that place every capture"
                )
            else:
                placed_captures: set[str] = set()
                for raw_operand in operand_patterns:
                    if isinstance(raw_operand, dict):
                        placed_captures.update(
                            _semantic_surface_pattern_string_list(
                                raw_operand,
                                "requires_captures",
                                prefix,
                                errors,
                            )
                        )
                missing_placed_captures = sorted(
                    set(required_captures) - placed_captures
                )
                if missing_placed_captures:
                    errors.append(
                        f"{prefix}.operand_patterns must place required capture(s): "
                        + ", ".join(missing_placed_captures)
                    )
        if required_captures and relation == "any":
            errors.append(
                f"{prefix}.requires_captures requires an asserted relation, not `any`"
            )
        required_equality_aliases = _semantic_surface_pattern_string_list(
            raw_pattern, "requires_equality_aliases", prefix, errors
        )
        pattern_required_equality_aliases.update(required_equality_aliases)
        unknown_equality_aliases = sorted(
            set(required_equality_aliases) - earlier_equality_alias_captures
        )
        if unknown_equality_aliases:
            errors.append(
                f"{prefix}.requires_equality_aliases must refer only to equality aliases "
                "from earlier patterns: " + ", ".join(unknown_equality_aliases)
            )
        if required_equality_aliases and relation in {"eq", "iff", "lt", "le"}:
            if not operand_patterns:
                errors.append(
                    f"{prefix}.requires_equality_aliases on a binary relation requires "
                    "operand_patterns that place every alias"
                )
            else:
                placed_equality_aliases: set[str] = set()
                for raw_operand in operand_patterns:
                    if isinstance(raw_operand, dict):
                        placed_equality_aliases.update(
                            _semantic_surface_pattern_string_list(
                                raw_operand,
                                "requires_equality_aliases",
                                prefix,
                                errors,
                            )
                        )
                missing_placed_equality_aliases = sorted(
                    set(required_equality_aliases) - placed_equality_aliases
                )
                if missing_placed_equality_aliases:
                    errors.append(
                        f"{prefix}.operand_patterns must place required equality alias(es): "
                        + ", ".join(missing_placed_equality_aliases)
                    )
        if required_equality_aliases and relation not in {"eq", "iff", "lt", "le"}:
            errors.append(
                f"{prefix}.requires_equality_aliases requires a binary asserted relation"
            )
        if pattern_required_equality_aliases:
            if allow_leaf_reuse is True:
                errors.append(
                    f"{prefix}.requires_equality_aliases forbids allow_leaf_reuse so "
                    "an alias is consumed by a distinct result leaf"
                )
            if not pattern_has_feature_constraint:
                errors.append(
                    f"{prefix}.requires_equality_aliases requires independent "
                    "semantic feature content outside the alias"
                )
            for alias_name in pattern_required_equality_aliases:
                equality_alias_consumers.setdefault(alias_name, []).append(index)
        if relation == "any" and capture is not None:
            errors.append(
                f"{prefix}.capture requires an asserted relation, not `any`"
            )

        minimum = raw_pattern.get("min_matches", 1)
        if (
            not isinstance(minimum, int)
            or isinstance(minimum, bool)
            or minimum < 1
        ):
            errors.append(f"{prefix}.min_matches must be a positive integer")
        elif (capture is not None or equality_alias_capture is not None) and minimum != 1:
            errors.append(
                f"{prefix}.capture and equality_alias_capture require min_matches to be 1"
            )
        if (
            relation == "any"
            and not features
            and not feature_counts
            and not operand_patterns
            and capture is None
            and equality_alias_capture is None
            and not required_captures
            and not required_equality_aliases
            and canonical_sha256 is None
        ):
            errors.append(
                f"{prefix} must constrain a result relation, exact feature, or capture"
            )

    for alias_name, capture_index in equality_alias_capture_indices.items():
        if not any(
            consumer_index > capture_index
            for consumer_index in equality_alias_consumers.get(alias_name, [])
        ):
            errors.append(
                "semantic_surface.required_result_patterns["
                f"{capture_index}].equality_alias_capture.as `{alias_name}` must be "
                "required by a later distinct result pattern"
            )


def _semantic_surface_assumption_schema_errors(
    raw_surface: dict[str, Any], errors: list[str]
) -> None:
    """Validate optional schema-3 patterns over explicit theorem assumptions."""

    raw_patterns = raw_surface.get("required_assumption_patterns")
    if raw_patterns is None:
        return
    if not isinstance(raw_patterns, list) or not raw_patterns:
        errors.append(
            "semantic_surface.required_assumption_patterns must be a nonempty list when present"
        )
        return
    ids: set[str] = set()
    for index, raw_pattern in enumerate(raw_patterns):
        prefix = f"semantic_surface.required_assumption_patterns[{index}]"
        if not isinstance(raw_pattern, dict):
            errors.append(f"{prefix} must be an object")
            continue
        unknown_fields = sorted(
            set(raw_pattern) - SEMANTIC_SURFACE_ASSUMPTION_PATTERN_FIELDS
        )
        if unknown_fields:
            errors.append(
                f"{prefix} has unknown field(s): " + ", ".join(unknown_fields)
            )
        pattern_id = raw_pattern.get("id")
        if not isinstance(pattern_id, str) or not pattern_id.strip():
            errors.append(f"{prefix}.id must be a nonempty string")
        elif pattern_id in ids:
            errors.append(f"{prefix}.id must not repeat `{pattern_id}`")
        else:
            ids.add(pattern_id)
        relation = raw_pattern.get("relation")
        if relation not in SEMANTIC_SURFACE_RESULT_RELATIONS:
            errors.append(
                f"{prefix}.relation must be one of "
                + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_RELATIONS))
            )
        features = _semantic_surface_pattern_string_list(
            raw_pattern, "all_features", prefix, errors
        )
        invalid_features = sorted(
            set(features) - SEMANTIC_SURFACE_RESULT_FEATURES
        )
        if invalid_features:
            errors.append(
                f"{prefix}.all_features contains unsupported feature(s): "
                + ", ".join(invalid_features)
            )
        raw_feature_counts = raw_pattern.get("minimum_feature_counts")
        if raw_feature_counts is not None:
            if not isinstance(raw_feature_counts, dict) or not raw_feature_counts:
                errors.append(
                    f"{prefix}.minimum_feature_counts must be a nonempty object when present"
                )
            else:
                for feature, count in raw_feature_counts.items():
                    if (
                        not isinstance(feature, str)
                        or feature not in SEMANTIC_SURFACE_RESULT_FEATURES
                    ):
                        errors.append(
                            f"{prefix}.minimum_feature_counts has unsupported feature `{feature}`"
                        )
                    if (
                        not isinstance(count, int)
                        or isinstance(count, bool)
                        or count < 1
                    ):
                        errors.append(
                            f"{prefix}.minimum_feature_counts values must be positive integers"
                        )
        minimum = raw_pattern.get("min_matches", 1)
        if (
            not isinstance(minimum, int)
            or isinstance(minimum, bool)
            or minimum < 1
        ):
            errors.append(f"{prefix}.min_matches must be a positive integer")


def semantic_surface_validation_errors(raw_surface: object) -> list[str]:
    """Validate a declaration-signature semantic-surface contract.

    The required structural operators are mandatory.  That keeps the contract
    from becoming a second declaration-name convention: exact helper terms may
    refine a source model, but they cannot be the only evidence that a direct
    route exposes its quantifiers, conditionals, integrations, or comparison.
    """

    if not isinstance(raw_surface, dict):
        return ["semantic_surface must be an object"]

    errors: list[str] = []
    schema = raw_surface.get("schema")
    allowed_fields = (
        SEMANTIC_SURFACE_V1_FIELDS
        if schema_version_is_exact(schema, SEMANTIC_SURFACE_LEGACY_SCHEMA)
        else (
            SEMANTIC_SURFACE_V2_FIELDS
            if schema_version_is_exact(schema, SEMANTIC_SURFACE_SCHEMA)
            else SEMANTIC_SURFACE_V3_FIELDS
        )
    )
    unknown_fields = sorted(set(raw_surface) - allowed_fields)
    if unknown_fields:
        errors.append(
            "semantic_surface has unknown field(s): " + ", ".join(unknown_fields)
        )
    if not schema_version_is_supported(schema, SEMANTIC_SURFACE_SCHEMAS):
        errors.append(
            "semantic_surface.schema must be one of "
            + ", ".join(str(value) for value in sorted(SEMANTIC_SURFACE_SCHEMAS))
        )

    if schema_version_is_exact(schema, SEMANTIC_SURFACE_RESULT_SCHEMA):
        _semantic_surface_result_schema_errors(raw_surface, errors)
        _semantic_surface_assumption_schema_errors(raw_surface, errors)
        return errors

    structural_tokens = _semantic_surface_string_list(
        raw_surface, "required_structural_tokens", errors, required=True
    )
    invalid_structural = sorted(
        set(structural_tokens) - SEMANTIC_SURFACE_STRUCTURAL_TOKENS
    )
    if invalid_structural:
        errors.append(
            "semantic_surface.required_structural_tokens contains unsupported "
            "non-structural token(s): "
            + ", ".join(invalid_structural)
        )

    _semantic_surface_string_list(raw_surface, "required_terms", errors, required=False)
    _semantic_surface_string_list(
        raw_surface, "forbidden_opaque_terms", errors, required=False
    )

    if not schema_version_is_exact(schema, SEMANTIC_SURFACE_SCHEMA):
        return errors

    raw_components = raw_surface.get("required_conclusion_components")
    if not isinstance(raw_components, list) or not raw_components:
        errors.append(
            "semantic_surface.required_conclusion_components must be a nonempty list"
        )
        return errors

    for index, raw_component in enumerate(raw_components):
        prefix = f"semantic_surface.required_conclusion_components[{index}]"
        if not isinstance(raw_component, dict):
            errors.append(f"{prefix} must be an object")
            continue
        unknown_component_fields = sorted(
            set(raw_component) - SEMANTIC_SURFACE_CONCLUSION_COMPONENT_FIELDS
        )
        if unknown_component_fields:
            errors.append(
                f"{prefix} has unknown field(s): "
                + ", ".join(unknown_component_fields)
            )

        selector = raw_component.get("selector")
        if selector not in SEMANTIC_SURFACE_CONCLUSION_SELECTORS:
            errors.append(
                f"{prefix}.selector must be one of "
                + ", ".join(sorted(SEMANTIC_SURFACE_CONCLUSION_SELECTORS))
            )
        relation = raw_component.get("relation")
        if relation not in SEMANTIC_SURFACE_CONCLUSION_RELATIONS:
            errors.append(
                f"{prefix}.relation must be one of "
                + ", ".join(sorted(SEMANTIC_SURFACE_CONCLUSION_RELATIONS))
            )

        left_operand = raw_component.get("left_operand")
        if left_operand is not None and left_operand not in (
            SEMANTIC_SURFACE_CONCLUSION_LEFT_OPERANDS
        ):
            errors.append(
                f"{prefix}.left_operand must be one of "
                + ", ".join(sorted(SEMANTIC_SURFACE_CONCLUSION_LEFT_OPERANDS))
            )

        def component_string_list(field: str) -> list[str]:
            value = raw_component.get(field)
            if value is None:
                return []
            if not isinstance(value, list) or not value:
                errors.append(f"{prefix}.{field} must be a nonempty string list when present")
                return []
            if any(not isinstance(item, str) or not item.strip() for item in value):
                errors.append(f"{prefix}.{field} must contain only nonempty strings")
                return []
            normalized = [item.strip() for item in value]
            if len(normalized) != len(set(normalized)):
                errors.append(f"{prefix}.{field} must not repeat a value")
            return normalized

        features = component_string_list("required_semantic_features")
        invalid_features = sorted(set(features) - SEMANTIC_SURFACE_CONCLUSION_FEATURES)
        if invalid_features:
            errors.append(
                f"{prefix}.required_semantic_features contains unsupported feature(s): "
                + ", ".join(invalid_features)
            )
        constants = component_string_list("required_constant_suffixes")
        if any(" " in constant for constant in constants):
            errors.append(
                f"{prefix}.required_constant_suffixes may not contain whitespace"
            )
        if left_operand is None and not features and not constants:
            errors.append(
                f"{prefix} must constrain a relation operand, semantic feature, or source primitive"
            )

        min_matches = raw_component.get("min_matches", 1)
        if not isinstance(min_matches, int) or isinstance(min_matches, bool) or min_matches < 1:
            errors.append(f"{prefix}.min_matches must be a positive integer")
        elif selector == "rightmost_top_level_conjunct" and min_matches != 1:
            errors.append(
                f"{prefix}.min_matches must be 1 for rightmost_top_level_conjunct"
            )
    return errors



def semantic_surface_inventory_findings(
    folder: Path,
    status: str,
    payload: dict[str, Any] | None = None,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate opt-in signature-surface contracts in a source map.

    This fast lane deliberately validates only JSON shape.  The repository
    audit resolves each direct declaration and checks its comment-free type
    signature against these tokens, so neither lane needs to infer semantics
    from source-item or Lean declaration names.
    """

    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    if payload is None:
        payload = load_json(map_path)
    if not isinstance(payload, dict):
        return []
    source_coverage_mode, _mode_error = source_coverage_mode_from_map(payload)
    _scoped_payload, raw_items = scoped_source_map_payload(
        payload,
        source_coverage_mode,
        folder=folder,
        repository_root=ROOT,
        context=context,
    )

    findings: list[Finding] = []
    severity = finding_severity(status)
    schema3_items: list[tuple[str, dict[str, Any]]] = []
    for source_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict) or "semantic_surface" not in raw_item:
            continue
        raw_surface = raw_item.get("semantic_surface")
        for error in semantic_surface_validation_errors(raw_surface):
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(map_path),
                    f"items.{source_key}: {error}",
                )
            )
        if isinstance(raw_surface, dict) and schema_version_is_exact(
            raw_surface.get("schema"), SEMANTIC_SURFACE_RESULT_SCHEMA
        ):
            schema3_items.append((str(source_key), raw_item))

    # Schema 3 intentionally recognizes only a small set of foundational
    # operators.  That is a useful anti-drift check, but no finite operator
    # vocabulary can establish that a source theorem was faithfully stated.
    # A completed paper therefore needs an independently source-anchored,
    # exact Prop specification and Lean-Meta proof/refutation route for every
    # schema-3 *result* claim. A role-typed source semantic declaration is
    # deliberately different: its exact declaration is the explicit
    # source-mapped prerequisite review target, rather than a second theorem
    # contract. This prevents a familiar collection of symbols from becoming
    # a substitute for the paper's actual formula without forcing a model or
    # definition into a synthetic theorem-shaped row.
    if schema3_items and status in CLOSEOUT_STATUSES:
        if not schema_version_is_supported(
            payload.get("semantic_contract_schema"), SEMANTIC_CONTRACT_SCHEMAS
        ):
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(map_path),
                    "schema-3 semantic surfaces require top-level "
                    "semantic_contract_schema 1 or 2 at closeout; "
                    "operator-pattern matches are supplementary evidence only",
                )
            )
        if payload.get(SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY) is not True:
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(map_path),
                    "schema-3 semantic surfaces require "
                    f"{SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY}: true at closeout",
                )
            )
        for source_key, raw_item in schema3_items:
            if raw_item.get("claim_bearing") is not True:
                findings.append(
                    Finding(
                        severity,
                        folder.name,
                        rel(map_path),
                        f"items.{source_key}: schema-3 source claim must set "
                        "claim_bearing: true at closeout",
                    )
                )
            source_semantic_declaration = (
                payload.get("semantic_route_schema") == 2
                and raw_item.get("inventory_role")
                == "source_semantic_declaration"
            )
            if source_semantic_declaration:
                roots = raw_item.get("lean_declarations")
                if (
                    not isinstance(roots, list)
                    or not roots
                    or any(not isinstance(root, str) or not root.strip() for root in roots)
                    or len({root.strip() for root in roots}) != len(roots)
                ):
                    findings.append(
                        Finding(
                            severity,
                            folder.name,
                            rel(map_path),
                            f"items.{source_key}: role-typed source semantic declaration "
                            "needs nonempty unique lean_declarations at closeout",
                        )
                    )
                continue
            if not isinstance(raw_item.get("semantic_contract"), dict):
                findings.append(
                    Finding(
                        severity,
                        folder.name,
                        rel(map_path),
                        f"items.{source_key}: schema-3 source claim needs an exact "
                        "semantic_contract at closeout",
                    )
                )
    return findings


def source_proof_fidelity_ledger_path(
    folder: Path, status_payload: dict[str, Any]
) -> tuple[Path | None, str]:
    """Compatibility export of the shared frozen-status path selector."""

    return configured_source_proof_fidelity_ledger_path(
        folder,
        status_payload,
        repository_root=ROOT,
    )


def meaningful_semantic_text(value: object) -> bool:
    """Require source-facing mathematical text rather than a blank/name-only token."""

    if not isinstance(value, str):
        return False
    text = value.strip()
    return len(text) >= 8 and not PLACEHOLDER_SOURCE_RE.search(text)


def concrete_source_locator(value: object) -> bool:
    """Require a source anchor that can be checked without a Lean identifier."""

    return isinstance(value, str) and bool(
        meaningful_semantic_text(value) and SOURCE_PROOF_LOCATOR_RE.search(value)
    )


def user_approved_scope_exclusion_errors(
    folder: Path,
    raw_approval: object,
    *,
    expected_source_locator: object | None = None,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[str]:
    """Validate an explicit user exclusion against its ordered source slices.

    This is a scope record, never a proof or a claim that the source material is
    non-mathematical.  It is intentionally expressed only in source-facing
    fields: an explicit user reference, date, reason, source locator, evidence,
    and the digest of that exact source slice.  No Lean declaration or map key
    is used as evidence.
    """

    if not isinstance(raw_approval, dict):
        return ["user_approved_scope_exclusion must be an object"]
    errors: list[str] = []

    def add(message: str) -> None:
        errors.append(f"user_approved_scope_exclusion.{message}")

    if not schema_version_is_exact(
        raw_approval.get("schema"), USER_APPROVED_SCOPE_EXCLUSION_SCHEMA
    ):
        add(f"schema must be {USER_APPROVED_SCOPE_EXCLUSION_SCHEMA}")
    if (
        str(raw_approval.get("approval_kind") or "").strip()
        != USER_APPROVED_SCOPE_EXCLUSION_APPROVAL_KIND
    ):
        add(
            "approval_kind must be "
            f"`{USER_APPROVED_SCOPE_EXCLUSION_APPROVAL_KIND}`"
        )
    approval_reference = str(raw_approval.get("approval_reference") or "").strip()
    if not meaningful_semantic_text(approval_reference):
        add("approval_reference must identify the explicit user instruction")
    approved_at = str(raw_approval.get("approved_at") or "").strip()
    if not USER_APPROVED_SCOPE_EXCLUSION_TIMESTAMP_RE.fullmatch(approved_at):
        add("approved_at must be an ISO-like date or timestamp")
    for field in ("reason", "source_evidence"):
        if not meaningful_semantic_text(raw_approval.get(field)):
            add(f"{field} must contain source-facing scope text")

    source_locator = str(raw_approval.get("source_locator") or "").strip()
    if not concrete_source_locator(source_locator):
        add("source_locator must be a concrete source anchor")
        return errors
    if expected_source_locator is not None and source_locator != str(
        expected_source_locator or ""
    ).strip():
        add("source_locator must exactly match the defect's source_locator")
    matches = list(SOURCE_FILE_LINE_RE.finditer(source_locator))
    if not matches:
        add("source_locator must contain a file:line anchor")
        return errors
    quote_digest = str(
        raw_approval.get("source_anchor_quote_sha256") or ""
    ).strip().lower()
    if not SHA256_RE.fullmatch(quote_digest):
        add("source_anchor_quote_sha256 must be a SHA-256 digest")
    for error in source_file_line_anchor_errors(
        folder,
        source_locator,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    ):
        add(f"source_locator {error}")
    quotes: list[str] = []
    for match in matches:
        path, path_error = resolve_paper_source_path(folder, match.group("path"))
        if path is None:
            add(f"source_locator {path_error}")
            return errors
        source_bytes_missing = (
            file_bytes_override is not None
            and path in file_bytes_override
            and file_bytes_override[path] is None
        ) or (file_bytes_override is None and not path.exists())
        if not require_source_bytes and source_bytes_missing:
            return errors
        try:
            source_text = normalized_source_text(
                _exact_file_bytes(path, file_bytes_override)
            )
        except (OSError, RuntimeError, UnicodeDecodeError) as error:
            add(f"source_locator source text cannot be read: {error}")
            return errors
        quote = normalized_source_line_excerpt(
            normalized_source_lines(source_text),
            int(match.group("start")),
            int(match.group("end") or match.group("start")),
        )
        if quote is None:
            add("source_locator cannot produce an exact source quote")
            return errors
        quotes.append(quote)
    # Match source_inventory_anchor_quote_text: every declared anchor, in
    # order, contributes to one approval pin. No excerpt may be dropped just
    # because the source presentation also cites a supporting proof.
    quote = "\n".join(quotes)
    if SHA256_RE.fullmatch(quote_digest) and quote_digest != hashlib.sha256(
        quote.encode("utf-8")
    ).hexdigest():
        add("source_anchor_quote_sha256 must match the exact source quote")
    return errors


def source_file_line_anchor_errors(
    folder: Path,
    value: object,
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[str]:
    """Check file-and-line anchors against the locally pinned source cache.

    The semantic ledger may also use page/theorem references, especially for a
    PDF-only source.  Whenever it supplies a concrete `file:line` anchor,
    however, that anchor must resolve inside the paper folder and refer to an
    existing line range.  This prevents an audit from becoming name-based prose
    that cites a nonexistent source location.
    """

    if not isinstance(value, str):
        return []
    errors: list[str] = []
    for match in SOURCE_FILE_LINE_RE.finditer(value):
        raw_path = Path(match.group("path"))
        try:
            candidate = (folder / raw_path).resolve()
            candidate.relative_to(folder.resolve())
        except (OSError, RuntimeError, ValueError):
            errors.append(f"source anchor `{raw_path}` escapes the paper folder")
            continue
        if file_bytes_override is not None and candidate not in file_bytes_override:
            errors.append(f"frozen input bundle omits source anchor `{raw_path}`")
            continue
        if (
            file_bytes_override is not None
            and file_bytes_override[candidate] is None
        ) or (file_bytes_override is None and not candidate.is_file()):
            if require_source_bytes:
                errors.append(
                    f"source anchor `{raw_path}` does not name a local source file"
                )
            continue
        if candidate.suffix.lower() not in TEXT_SOURCE_SUFFIXES:
            continue
        start = int(match.group("start"))
        end = int(match.group("end") or start)
        try:
            line_count = len(
                _exact_file_bytes(candidate, file_bytes_override)
                .decode("utf-8")
                .splitlines()
            )
        except (OSError, RuntimeError, UnicodeDecodeError):
            errors.append(f"source anchor `{raw_path}` could not be read")
            continue
        if start < 1 or end < start or end > line_count:
            errors.append(
                f"source anchor `{raw_path}:{start}-{end}` is outside its {line_count}-line source"
            )
    return errors


def corrected_target_record_digest(raw: object) -> str:
    """Return the stable digest used by local corrected-target routes.

    Keep this deliberately independent of source-map keys and Lean names.  The
    record itself contains the archival baseline, corrected mathematical text,
    governing defect ids, and approval pin that a reviewer inspected.
    """

    return _shared_corrected_target_record_digest(raw)


def corrected_target_primary_declaration(item: object) -> str | None:
    """Return the unique complete endpoint allowed to carry a repaired target."""

    if not isinstance(item, dict):
        return None
    declarations = item.get("lean_declarations")
    if not isinstance(declarations, list) or len(declarations) != 1:
        return None
    declaration = declarations[0]
    if not isinstance(declaration, str) or not declaration.strip():
        return None
    return declaration.strip()


def corrected_target_semantic_bundle_declarations(item: object) -> list[str] | None:
    """Return a bounded corrected source-semantic declaration bundle.

    A corrected named result receives one proof-credit endpoint. A corrected
    source algorithm or model may instead supply a small explicit set of
    source-semantic declarations that are reviewed under the same approved
    target but receive no independent theorem credit.
    """

    if not isinstance(item, dict):
        return None
    if str(item.get("inventory_role") or "").strip() != "source_semantic_declaration":
        return None
    if isinstance(item.get("semantic_contract"), Mapping):
        return None
    declarations = item.get("lean_declarations")
    if not isinstance(declarations, list) or not declarations:
        return None
    normalized = [
        value.strip()
        for value in declarations
        if isinstance(value, str) and value.strip()
    ]
    if len(normalized) != len(declarations) or len(set(normalized)) != len(normalized):
        return None
    return normalized


def corrected_source_statement_map_findings(
    folder: Path,
    status: str,
    payload: dict[str, Any],
    *,
    context: EvidenceRunContext | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Validate local, explicit replacements for false source statements.

    An archival statement remains the map item's ``statement``.  A separate
    ``corrected_target`` is permitted only through this narrow record, never by
    relabelling a false theorem as ordinary ``covered``.  The validation uses
    source text, hashes, and the source-proof ledger; Lean declaration names
    play no role in deciding whether a correction is authorized.
    """

    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return []
    presentation_aliases, _presentation_alias_errors = source_presentation_aliases(
        raw_items
    )
    subsumed_target_exemptions = validated_subsumed_result_contract_exemptions(
        folder, payload, context=context
    )
    has_corrected_rows = any(
        str(key).strip() not in presentation_aliases
        and isinstance(item, dict)
        and (
            str(item.get("coverage_status") or "").strip().lower()
            == CORRECTED_SOURCE_STATEMENT_STATUS
            or str(item.get("source_status") or "").strip().lower()
            == "quarantined_source_defect"
        )
        for key, item in raw_items.items()
    )
    if not has_corrected_rows and not any(
        str(key).strip() not in presentation_aliases
        and isinstance(item, dict)
        and "corrected_target" in item
        for key, item in raw_items.items()
    ):
        return []

    if file_bytes_override is None and context is not None:
        file_bytes_override = context.file_bytes_override()
    severity = finding_severity(status)
    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(map_path), message))

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    ledger_path, ledger_path_error = source_proof_fidelity_ledger_path(
        folder, status_payload
    )
    ledger = (
        transaction_json(ledger_path, context)
        if ledger_path is not None
        else None
    )
    defects_by_id: dict[str, dict[str, Any]] = {}
    if ledger_path_error:
        add(ledger_path_error)
    elif not isinstance(ledger, dict):
        add("corrected source targets require a readable configured source-proof fidelity ledger")
    else:
        raw_defects = ledger.get("defects")
        if isinstance(raw_defects, list):
            for defect in raw_defects:
                if not isinstance(defect, dict):
                    continue
                defect_id = str(defect.get("id") or "").strip()
                if defect_id:
                    defects_by_id[defect_id] = defect

    governed_defect_ids: set[str] = set()
    for raw_key, raw_item in raw_items.items():
        key = str(raw_key or "").strip() or "<unnamed>"
        if not isinstance(raw_item, dict):
            continue
        # A repeated presentation remains source-visible, including any
        # archival correction context, but its canonical item owns the one
        # corrected-target endpoint and coverage verdict.  Requiring a second
        # endpoint here would reintroduce the duplicate route the alias schema
        # prohibits.
        if key in presentation_aliases:
            continue
        raw_routed = raw_item.get("source_defect_ids")
        routed_ids = {
            value.strip()
            for value in (raw_routed if isinstance(raw_routed, list) else [])
            if isinstance(value, str) and value.strip()
        }
        if (
            str(raw_item.get("source_status") or "").strip().lower()
            == "quarantined_source_defect"
        ):
            if not routed_ids:
                add(
                    f"items.{key} quarantined_source_defect requires one or more "
                    "source_defect_ids"
                )
            for defect_id in sorted(routed_ids):
                defect = defects_by_id.get(defect_id)
                if defect is None:
                    add(
                        f"items.{key}.source_defect_ids cites unknown "
                        f"fidelity-ledger defect `{defect_id}`"
                    )
                    continue
                if str(defect.get("statement_impact") or "").strip() != "source_statement":
                    add(
                        f"items.{key}.source_defect_ids defect `{defect_id}` "
                        "is not a source-statement defect"
                    )
                if (
                    str(defect.get("resolution") or "").strip()
                    != "quarantined_source_defect"
                ):
                    add(
                        f"items.{key}.source_defect_ids defect `{defect_id}` "
                        "must resolve as quarantined_source_defect"
                    )
        excluded_target = (
            raw_item.get("inventory_role") == "source_scope_exclusion"
            and raw_item.get("scope_disposition") == USER_APPROVED_SCOPE_EXCLUSION
            and raw_item.get("coverage_status") == USER_APPROVED_SCOPE_EXCLUSION
            and isinstance(raw_item.get(USER_APPROVED_SCOPE_EXCLUSION), dict)
            and not any(
                raw_item.get(field)
                for field in (
                    "semantic_contract", "lean_declarations", "proof_lean_declarations",
                    "support_lean_declarations", "support_declarations",
                    "source_spec_correspondence",
                )
            )
            and not source_inventory_item_user_approved_scope_exclusion_error(raw_item)
            and not user_approved_scope_exclusion_errors(
                folder,
                raw_item[USER_APPROVED_SCOPE_EXCLUSION],
                expected_source_locator=raw_item.get("source_location"),
                file_bytes_override=file_bytes_override,
            )
        )
        corrected_status = (
            str(raw_item.get("coverage_status") or "").strip().lower()
            == CORRECTED_SOURCE_STATEMENT_STATUS
        )
        subsumed_target = key in subsumed_target_exemptions
        target = raw_item.get("corrected_target")
        if (
            corrected_status
            or ((excluded_target or subsumed_target) and target is not None)
        ) and not isinstance(target, dict):
            add(f"items.{key} corrected_source_statement requires a structured corrected_target")
            continue
        if not corrected_status and not excluded_target and not subsumed_target and target is not None:
            add(f"items.{key} has corrected_target without coverage_status corrected_source_statement")
            continue
        if not corrected_status and not (
            (excluded_target or subsumed_target) and target is not None
        ):
            continue
        assert isinstance(target, dict)
        prefix = f"items.{key}.corrected_target"
        primary_declaration = corrected_target_primary_declaration(raw_item)
        semantic_bundle = corrected_target_semantic_bundle_declarations(raw_item)
        # Exclusion or validated result subsumption retires the endpoint, not
        # the correction's source, approval, or fidelity-ledger provenance.
        # Validate those records below too.
        if (
            not excluded_target
            and not subsumed_target
            and primary_declaration is None
            and semantic_bundle is None
        ):
            add(
                f"items.{key}.lean_declarations must name either one complete "
                "corrected-target endpoint or a bounded source-semantic declaration bundle"
            )
        raw_proof_declarations = raw_item.get("proof_lean_declarations")
        if (
            isinstance(raw_proof_declarations, (list, tuple, set))
            and raw_proof_declarations
        ) or (
            not isinstance(raw_proof_declarations, (list, tuple, set, type(None)))
            and str(raw_proof_declarations).strip()
        ):
            add(
                f"items.{key}.proof_lean_declarations is prohibited for "
                "corrected_source_statement; move helper proofs to "
                "support_lean_declarations"
            )
        if not schema_version_is_exact(
            target.get("schema"), CORRECTED_TARGET_SCHEMA
        ):
            add(f"{prefix}.schema must be {CORRECTED_TARGET_SCHEMA}")
        archival_statement = str(raw_item.get("statement") or "").strip()
        target_statement = str(target.get("statement") or "").strip()
        if not meaningful_semantic_text(archival_statement):
            add(f"items.{key}.statement must retain a nonempty archival source statement")
        if not meaningful_semantic_text(target_statement):
            add(f"{prefix}.statement must state the corrected mathematical target")
        target_digest = hashlib.sha256(
            re.sub(r"\s+", " ", target_statement).strip().encode("utf-8")
        ).hexdigest()
        if archival_statement and target_statement and re.sub(r"\s+", " ", archival_statement).strip() == re.sub(r"\s+", " ", target_statement).strip():
            add(f"{prefix}.statement must differ from the archival source statement")
        if target.get("archival_equivalence_claimed") is not False:
            add(f"{prefix}.archival_equivalence_claimed must be false")

        raw_governing = target.get("governing_defect_ids")
        if (
            not isinstance(raw_governing, list)
            or not raw_governing
            or any(not isinstance(value, str) or not value.strip() for value in raw_governing)
            or len({value.strip() for value in raw_governing}) != len(raw_governing)
        ):
            add(f"{prefix}.governing_defect_ids must be a nonempty unique string list")
            governing_ids: set[str] = set()
        else:
            governing_ids = {value.strip() for value in raw_governing}
            governed_defect_ids.update(governing_ids)
        if governing_ids and not governing_ids.issubset(routed_ids):
            add(f"{prefix}.governing_defect_ids must be a subset of source_defect_ids")
        for defect_id in sorted(governing_ids):
            defect = defects_by_id.get(defect_id)
            if defect is None:
                add(f"{prefix}.governing_defect_ids cites unknown fidelity-ledger defect `{defect_id}`")
                continue
            if str(defect.get("statement_impact") or "").strip() != "source_statement":
                add(f"{prefix} governing defect `{defect_id}` is not a source-statement defect")
            if str(defect.get("resolution") or "").strip() != "corrected_source_statement":
                add(f"{prefix} governing defect `{defect_id}` is not resolved as corrected_source_statement")

        locator = str(target.get("archival_source_locator") or "").strip()
        if not concrete_source_locator(locator):
            add(f"{prefix}.archival_source_locator must be one concrete source anchor")
        else:
            locator_matches = list(SOURCE_FILE_LINE_RE.finditer(locator))
            if len(locator_matches) != 1:
                add(f"{prefix}.archival_source_locator must contain exactly one file:line anchor")
            for error in source_file_line_anchor_errors(
                folder, locator, file_bytes_override=file_bytes_override
            ):
                add(f"{prefix}.archival_source_locator {error}")
            if len(locator_matches) == 1:
                match = locator_matches[0]
                path, path_error = resolve_paper_source_path(folder, match.group("path"))
                if path is None:
                    add(f"{prefix}.archival_source_locator {path_error}")
                else:
                    try:
                        source_text = normalized_source_text(
                            _exact_file_bytes(path, file_bytes_override)
                        )
                        quote = normalized_source_line_excerpt(
                            normalized_source_lines(source_text),
                            int(match.group("start")),
                            int(match.group("end") or match.group("start")),
                        )
                    except (OSError, RuntimeError, UnicodeDecodeError) as error:
                        quote = None
                        add(f"{prefix}.archival_source_locator cannot be read: {error}")
                    quote_digest = str(
                        target.get("archival_source_quote_sha256") or ""
                    ).strip().lower()
                    if not SHA256_RE.fullmatch(quote_digest):
                        add(f"{prefix}.archival_source_quote_sha256 must be a SHA-256 digest")
                    elif quote is None or quote_digest != hashlib.sha256(
                        quote.encode("utf-8")
                    ).hexdigest():
                        add(f"{prefix}.archival_source_quote_sha256 must pin the exact archival source anchor")

        approval = target.get("approval")
        if not isinstance(approval, dict):
            add(f"{prefix}.approval must be an object")
            continue
        if str(approval.get("kind") or "").strip() not in CORRECTED_TARGET_APPROVAL_KINDS:
            add(f"{prefix}.approval.kind must identify an approved corrected-target disposition")
        if not USER_APPROVED_SCOPE_EXCLUSION_TIMESTAMP_RE.fullmatch(
            str(approval.get("recorded_at") or "").strip()
        ):
            add(f"{prefix}.approval.recorded_at must be an ISO-like date or timestamp")
        if not meaningful_semantic_text(approval.get("reference")):
            add(f"{prefix}.approval.reference must identify the recorded approval")
        if str(approval.get("target_statement_sha256") or "").strip().lower() != target_digest:
            add(f"{prefix}.approval.target_statement_sha256 must pin the corrected target text")
        original_artifact_path_error = (
            corrected_target_original_artifact_path_error(approval)
        )
        if original_artifact_path_error:
            add(f"{prefix}.approval {original_artifact_path_error}")
        approval_path = _paper_local_artifact_path(folder, approval.get("artifact_path"))
        approval_snapshot = (
            context.json_snapshot(approval_path)
            if context is not None and approval_path is not None
            else None
        )
        approval_raw = (
            approval_snapshot.raw_bytes
            if approval_snapshot is not None
            else _exact_file_bytes(approval_path, file_bytes_override)
            if file_bytes_override is not None and approval_path is not None
            else approval_path.read_bytes()
            if context is None and approval_path is not None and approval_path.is_file()
            else None
        )
        if approval_path is None or approval_raw is None:
            add(f"{prefix}.approval.artifact_path must name a paper-local approval artifact")
        elif str(approval.get("artifact_protocol") or "").strip() == (
            CORRECTED_TARGET_APPROVAL_PROTOCOL
        ):
            try:
                approval_text = approval_raw.decode("utf-8")
            except UnicodeDecodeError:
                add(f"{prefix}.approval artifact must be UTF-8 text")
            else:
                approval_error = corrected_target_approval_artifact_error(
                    approval, approval_text
                )
                if approval_error:
                    add(f"{prefix}.approval {approval_error}")
            if corrected_target_approval_excerpt_material(approval) is None:
                add(f"{prefix}.approval excerpt authority is malformed")
        else:
            approval_digest = str(
                approval.get("artifact_sha256") or ""
            ).strip().lower()
            approval_actual_digest = hashlib.sha256(approval_raw).hexdigest()
            if not SHA256_RE.fullmatch(approval_digest):
                add(f"{prefix}.approval.artifact_sha256 must be a SHA-256 digest")
            elif approval_actual_digest != approval_digest:
                add(
                    f"{prefix}.approval.artifact_sha256 does not match its "
                    "approval artifact"
                )
        recorded_digest = str(target.get("corrected_target_sha256") or "").strip().lower()
        if not SHA256_RE.fullmatch(recorded_digest):
            add(f"{prefix}.corrected_target_sha256 must be a SHA-256 digest")
        elif recorded_digest != corrected_target_record_digest(target):
            add(f"{prefix}.corrected_target_sha256 is stale")
        recorded_review_digest = str(
            target.get("corrected_target_review_sha256") or ""
        ).strip().lower()
        if recorded_review_digest and recorded_review_digest != corrected_target_review_digest(
            target
        ):
            add(f"{prefix}.corrected_target_review_sha256 is stale")

    if isinstance(ledger, dict):
        unresolved = sorted(
            str(defect.get("id") or "").strip()
            for defect in ledger.get("defects", [])
            if isinstance(defect, dict)
            and str(defect.get("resolution") or "").strip()
            == "corrected_source_statement"
            and str(defect.get("statement_impact") or "").strip()
            == "source_statement"
            and str(defect.get("id") or "").strip() not in governed_defect_ids
        )
        if unresolved:
            add(
                "source-statement corrections lack an explicit corrected_target map record: "
                + ", ".join(unresolved)
            )
    return findings



PLAIN_FORMALIZED = "formalized"


AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE = "author_approved_corrected_model"


WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE = "whole_paper_closeout"


COMPONENT_LEVEL_EVIDENCE_ONLY_SCOPE_ROLE = "component_level_evidence_only"


CORRECTED_MODEL_SCOPE_ROLES = {
    WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE,
    COMPONENT_LEVEL_EVIDENCE_ONLY_SCOPE_ROLE,
}


CORRECTED_MODEL_GOVERNING_DISPOSITIONS = {
    "repaired_in_governing_proof",
    "replaced_by_authorized_correction",
}


CORRECTED_MODEL_CONCLUSION_RELATIONS = {
    "same",
    "restricted_domain",
    "corrected_codomain",
    "replaced",
}


SOURCE_PROOF_DEFECT_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")


SOURCE_PROOF_FIDELITY_REVIEW_STATUSES = {
    "not_started",
    "reviewed_no_defects",
    "defects_recorded",
}


SOURCE_PROOF_FIDELITY_SCHEMAS = {1, 2}


SOURCE_PROOF_FIDELITY_SCOPE_OUTCOMES = {"no_defect", "defect_recorded"}


SOURCE_PROOF_FIDELITY_DEFECT_KINDS = {
    "algebra_or_sign",
    "inequality_direction",
    "quantifier_or_uniformity",
    "domain_or_endpoint",
    "index_or_integrality",
    "event_or_measure",
    "normalization_or_scaling",
    "logical_dependency",
    "model_semantics",
    "other",
}


SOURCE_PROOF_FIDELITY_STATEMENT_IMPACTS = {
    "proof_only",
    "source_statement",
    "uncertain",
}


SOURCE_PROOF_FIDELITY_STATUS_IMPACTS = {
    "formalized_note",
    "formalized_with_caveat",
    "partially_formalized",
}


SOURCE_PROOF_FIDELITY_RESOLUTIONS = {
    "repaired_in_lean",
    "open_proof_obligation",
    "corrected_source_statement",
    "quarantined_source_defect",
    "resolved_in_current_source",
    "user_approved_scope_exclusion",
}


DEEP_AUDIT_OBSERVATION_LINK_FIELD = "deep_audit_observation_ids"


DEEP_AUDIT_OBSERVATION_NORMAL_SCOPE_DISPOSITION = (
    "unnumbered_prose_outside_named_theory"
)


DEEP_AUDIT_OBSERVATION_REQUIRED_FIELDS = (
    "id",
    "source_locator",
    "affected_source_locators",
    "source_claim",
    "finding",
    "repair_handoff",
    "normal_scope_disposition",
)


SOURCE_PROOF_MODEL_CONVENTION_REQUIRED_FIELDS = (
    "id",
    "source_locator",
    "classification",
    "formal_meaning",
    "why_needed",
    "checked_scope",
)


SOURCE_PROOF_CHECKED_STEP_REQUIRED_FIELDS = (
    "id",
    "source_locator",
    "source_step",
    "checked_conclusion",
    "scope",
)


SOURCE_CLAIM_ATOMS_SCHEMA_KEY = "source_claim_atoms_schema"


SOURCE_CLAIM_ATOMS_SCHEMA = source_claim_atom_schema.SOURCE_CLAIM_ATOMS_SCHEMA


SOURCE_CLAIM_ATOMS_KEY = "source_claim_atoms"


SOURCE_CLAIM_ATOM_SOURCE_QUOTE_SHA256_FIELD = (
    source_claim_atom_schema.SOURCE_QUOTE_SHA256_FIELD
)


SOURCE_CLAIM_ATOM_VERBATIM_CLAUSE_FIELD = (
    source_claim_atom_schema.VERBATIM_CLAUSE_FIELD
)


SOURCE_CLAIM_ATOM_IDENTITY_SCHEMA_FIELD = (
    source_claim_atom_schema.IDENTITY_SCHEMA_FIELD
)


LEGACY_SOURCE_CLAIM_ATOM_IDENTITY_SCHEMA = (
    source_claim_atom_schema.LEGACY_IDENTITY_SCHEMA
)


SOURCE_CLAIM_ATOM_CLAUSE_IDENTITY_SCHEMA = (
    source_claim_atom_schema.EXACT_CLAUSE_IDENTITY_SCHEMA
)


SOURCE_SPEC_CORRESPONDENCE_SOURCE_KINDS = THEOREM_REALIZATION_SOURCE_KINDS


SOURCE_SPEC_CORRESPONDENCE_NONCLAIM_STATUSES = (
    THEOREM_REALIZATION_NONCLAIM_STATUSES
)


SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY = "source_spec_correspondence_schema"


SOURCE_SPEC_CORRESPONDENCE_SCHEMA = 1


SOURCE_SPEC_CORRESPONDENCE_KEY = "source_spec_correspondence"


SUBSUMED_BY_SELECTED_RESULT = "subsumed_by_selected_result"


SUBSUMED_RESULT_SUPPORT_ROUTE_FIELDS = (
    "semantic_contract",
    "lean_declarations",
    "proof_lean_declarations",
    "spec_lean_declarations",
    "support_lean_declarations",
    "support_declarations",
    SOURCE_SPEC_CORRESPONDENCE_KEY,
    "evidence_declaration",
    "spec_declaration",
    "source_routes",
    "review_rows",
)


SEMANTIC_CONTRACT_EVIDENCE_MODES = {
    "proves",
    "refutes",
    "definitionally_realizes",
}


SEMANTIC_CONTRACT_SHAPES = {"plain"}


CONDITIONAL_PROBABILITY_COMPOSITION_SEMANTIC_SHAPE = (
    "conditional_probability_composition"
)


SEMANTIC_CONTRACT_SCHEMA_2_SHAPES = {
    *SEMANTIC_CONTRACT_SHAPES,
    CONDITIONAL_PROBABILITY_COMPOSITION_SEMANTIC_SHAPE,
}


CONDITIONAL_PROBABILITY_COMPOSITION_FIELD = "conditional_probability_composition"


CONDITIONAL_PROBABILITY_COMPOSITION_CLAUSES = (
    "selector_law",
    "conditional_outcome_law",
    "composed_objective_or_expectation",
)


CONDITIONAL_PROBABILITY_COMPOSITION_CLAUSE_FIELDS = {
    "source_location",
    "source_anchor_evidence",
    "semantic_statement",
}


def canonical_json_payload(payload: Any) -> Any:
    """Canonicalize JSON data exactly like the source-record scope helper."""

    if isinstance(payload, dict):
        return {
            key: canonical_json_payload(value)
            for key, value in sorted(payload.items())
        }
    if isinstance(payload, list):
        return sorted(
            (canonical_json_payload(value) for value in payload),
            key=lambda value: json.dumps(value, sort_keys=True, separators=(",", ":")),
        )
    return payload


def canonical_json_digest(payload: Any) -> str:
    """Hash JSON data after recursively sorting maps and correction lists.

    Corrected-model approval is about the content of every recorded correction,
    not about the incidental order in which the status file lists them.
    """

    encoded = json.dumps(
        canonical_json_payload(payload), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def author_approved_corrected_scope(
    status_payload: dict[str, Any] | None,
) -> dict[str, Any] | None:
    """Return the explicit corrected target, never inferred from a status word."""

    if not isinstance(status_payload, dict):
        return None
    scope = status_payload.get("formalization_scope")
    if not isinstance(scope, dict):
        return None
    if str(scope.get("kind") or "").strip() != AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE:
        return None
    return scope


def corrected_model_scope_role(scope: object) -> tuple[str | None, str]:
    """Return one explicit corrected-scope role without a status-name fallback.

    Both fields are mandatory.  Corrected-target metadata may grant a
    whole-paper waiver only when that authority is explicitly declared; old or
    partially migrated records fail closed instead of inheriting it.
    """

    if not isinstance(scope, dict):
        return None, "formalization_scope must be an object"
    raw_role = scope.get("scope_role")
    raw_claim = scope.get("whole_paper_closeout_claimed")
    if raw_role is None and raw_claim is None:
        return (
            None,
            "formalization_scope must explicitly declare scope_role and "
            "whole_paper_closeout_claimed",
        )
    if not isinstance(raw_role, str) or not raw_role.strip():
        return None, "formalization_scope.scope_role must be a nonempty string"
    role = raw_role.strip()
    if role not in CORRECTED_MODEL_SCOPE_ROLES:
        return (
            None,
            "formalization_scope.scope_role must be one of: "
            + ", ".join(sorted(CORRECTED_MODEL_SCOPE_ROLES)),
        )
    if not isinstance(raw_claim, bool):
        return (
            None,
            "formalization_scope.whole_paper_closeout_claimed must be Boolean "
            "when scope_role is declared",
        )
    expected_claim = role == WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE
    if raw_claim is not expected_claim:
        return (
            None,
            "formalization_scope.scope_role `"
            + role
            + "` conflicts with whole_paper_closeout_claimed="
            + str(raw_claim).lower(),
        )
    return role, ""


def item_entries(payload: dict[str, Any]) -> list[tuple[str, dict[str, Any]]]:
    raw = payload.get("items") or payload.get("judgments") or {}
    if isinstance(raw, dict):
        return [
            (str(key), item)
            for key, item in raw.items()
            if isinstance(item, dict)
        ]
    if isinstance(raw, list):
        return [
            (str(index), item)
            for index, item in enumerate(raw)
            if isinstance(item, dict)
        ]
    return []


source_claim_atoms_validation_errors = (
    source_claim_atom_schema.source_claim_atoms_validation_errors
)


def _source_claim_atoms_current_quote_binding_errors(
    folder: Path,
    raw_atoms: object,
    *,
    source_artifact_path: object,
    source_artifact_sha256: object,
    alternate_source_artifact_path: object = "",
    alternate_source_artifact_sha256: object = "",
) -> list[str]:
    """Verify strict atom receipts against selected source bytes.

    This intentionally derives the expected quote from the locator's exact
    ``file:line[-line]`` range.  It never accepts supplied prose as the quote,
    so changing an atom's paraphrase, identifier, or Lean route cannot mask a
    stale source slice.  The raw artifact digest is checked first; the stored
    quote digest then binds one semantic atom to the current normalized line
    excerpt of that already byte-pinned artifact.  Exact-clause atoms also
    require their verbatim clause to occur exactly once in that excerpt, so two
    independently reviewed clauses in one presentation cannot collapse to the
    same semantic identity.

    Shape errors (missing locator / digest, malformed ranges) belong to
    :func:`source_claim_atoms_validation_errors`; this helper avoids repeating
    them and only resolves atom fields that are syntactically usable. A visual
    semantic transcription may be selected for readable source-to-Spec review
    while the canonical raw transcript remains the claimed-result identity. In
    that situation the caller supplies the canonical transcript as the
    alternate exact source artifact; an atom may bind either pinned surface,
    but never an unrelated source file.
    """

    def load_artifact(
        path_value: object,
        digest_value: object,
        *,
        label: str,
    ) -> tuple[Path, list[str]] | str:
        artifact_path, artifact_path_error = resolve_paper_source_path(
            folder, path_value
        )
        if artifact_path is None:
            return (
                f"cannot resolve the {label} source artifact for source-claim atom "
                "quote validation: "
                + artifact_path_error
            )
        if not artifact_path.is_file():
            return (
                f"{label.capitalize()} source artifact is not a readable regular file "
                "for source-claim atom quote validation"
            )
        expected_digest = str(digest_value or "").strip().lower()
        if not SHA256_RE.fullmatch(expected_digest):
            return (
                f"{label.capitalize()} source artifact SHA-256 must be a SHA-256 digest "
                "before source-claim atom quote validation"
            )
        try:
            source_bytes = artifact_path.read_bytes()
        except OSError as error:
            return (
                f"cannot read {label} source artifact for source-claim atom quote "
                f"validation: {error}"
            )
        if hashlib.sha256(source_bytes).hexdigest() != expected_digest:
            return (
                f"{label.capitalize()} source artifact SHA-256 does not match the current "
                "artifact; source-claim atom quotes are stale"
            )
        try:
            source_lines = normalized_source_lines(normalized_source_text(source_bytes))
        except UnicodeDecodeError:
            return (
                f"{label.capitalize()} source artifact must be UTF-8 text for exact "
                "source-claim atom quote validation"
            )
        return artifact_path, source_lines

    selected_artifact = load_artifact(
        source_artifact_path,
        source_artifact_sha256,
        label="selected semantic",
    )
    if isinstance(selected_artifact, str):
        return [selected_artifact]
    artifacts = [selected_artifact]
    alternate_path = str(alternate_source_artifact_path or "").strip()
    alternate_digest = str(alternate_source_artifact_sha256 or "").strip()
    if alternate_path or alternate_digest:
        alternate_artifact = load_artifact(
            alternate_source_artifact_path,
            alternate_source_artifact_sha256,
            label="canonical alternate",
        )
        if isinstance(alternate_artifact, str):
            return [alternate_artifact]
        if alternate_artifact[0] != selected_artifact[0]:
            artifacts.append(alternate_artifact)

    if not isinstance(raw_atoms, list):
        return []

    errors: list[str] = []
    for index, raw_atom in enumerate(raw_atoms):
        if not isinstance(raw_atom, dict):
            continue
        prefix = f"source_claim_atoms[{index}]"
        locator = raw_atom.get("source_locator")
        matches = (
            list(SOURCE_FILE_LINE_RE.finditer(locator))
            if isinstance(locator, str)
            else []
        )
        if len(matches) != 1:
            continue
        quote_digest = raw_atom.get(SOURCE_CLAIM_ATOM_SOURCE_QUOTE_SHA256_FIELD)
        if not isinstance(quote_digest, str) or not SHA256_RE.fullmatch(
            quote_digest.strip()
        ):
            continue

        match = matches[0]
        candidate, path_error = resolve_paper_source_path(folder, match.group("path"))
        start = int(match.group("start"))
        end = int(match.group("end") or start)
        if candidate is None:
            errors.append(
                f"{prefix}.source_locator source span `{match.group('path')}:"
                f"{start}-{end}` {path_error}"
            )
            continue
        artifact_lines = next(
            (lines for path, lines in artifacts if candidate == path), None
        )
        if artifact_lines is None:
            errors.append(
                f"{prefix}.source_locator must identify the canonical pinned source "
                "artifact or its selected semantic transcription for source-spec correspondence"
            )
            continue
        quote = normalized_source_line_excerpt(artifact_lines, start, end)
        if quote is None:
            errors.append(
                f"{prefix}.source_locator line range {start}-{end} is outside the "
                "current selected source artifact"
            )
            continue
        current_quote_digest = hashlib.sha256(quote.encode("utf-8")).hexdigest()
        if quote_digest.strip().lower() != current_quote_digest:
            errors.append(
                f"{prefix}.{SOURCE_CLAIM_ATOM_SOURCE_QUOTE_SHA256_FIELD} does not "
                "match the exact current canonical source line slice"
            )
            continue
        raw_identity_schema = raw_atom.get(
            SOURCE_CLAIM_ATOM_IDENTITY_SCHEMA_FIELD,
            LEGACY_SOURCE_CLAIM_ATOM_IDENTITY_SCHEMA,
        )
        if raw_identity_schema == SOURCE_CLAIM_ATOM_CLAUSE_IDENTITY_SCHEMA:
            verbatim_clause = raw_atom.get(
                SOURCE_CLAIM_ATOM_VERBATIM_CLAUSE_FIELD
            )
            if not isinstance(verbatim_clause, str) or not verbatim_clause.strip():
                continue
            occurrence_count = quote.count(verbatim_clause)
            if occurrence_count != 1:
                errors.append(
                    f"{prefix}.{SOURCE_CLAIM_ATOM_VERBATIM_CLAUSE_FIELD} must "
                    "occur exactly once in the exact current selected semantic source "
                    f"line slice; found {occurrence_count} occurrence(s)"
                )
    return errors


def _initial_source_map_proof_obligation_items(
    folder: Path,
    payload: object,
    *,
    context: EvidenceRunContext | None = None,
) -> tuple[dict[str, dict[str, Any]], str]:
    """Return the active selector before validated support-row subsumption."""

    if not isinstance(payload, dict):
        return {}, ""
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return {}, ""

    mode, mode_error = source_coverage_mode_from_map(payload)
    source_index_ids = source_index_byte_pinned_anchor_item_ids(
        folder,
        payload,
        mode,
        context=context,
    )
    selected = filter_source_map_items_for_proof_obligations(
        raw_items,
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            payload
        ),
        additional_selected_item_ids=source_index_ids,
    )
    # The ordinary denominator follows named source presentations, but a
    # paper may deliberately put an unnumbered prose consequence on its
    # one-claim-per-Spec PaperInterface surface.  The explicit
    # ``review_surface.include_names`` choice is the routing selector: the claim must
    # receive the same atom, source-to-Spec, and proof-realization checks as
    # a numbered theorem.  Otherwise the dashboard can display and review
    # a claim that the accepting v11 audit silently omits.  This step does
    # not infer declaration existence or kind from source text; the later
    # Lean environment inventory owns those facts.
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    review_surface = status_payload.get("review_surface")
    raw_include_names = (
        review_surface.get("include_names")
        if isinstance(review_surface, Mapping)
        else None
    )
    interface_specs = {
        str(name).strip()
        for name in raw_include_names
        if isinstance(name, str) and str(name).strip()
    } if isinstance(raw_include_names, list) else set()
    for raw_key, raw_item in raw_items.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_item, dict):
            continue
        contract = raw_item.get("semantic_contract")
        specification = (
            str(contract.get("spec_declaration") or "").strip()
            if isinstance(contract, Mapping)
            else ""
        )
        source_status = str(raw_item.get("source_status") or "").strip().lower()
        if (
            raw_item.get("claim_bearing") is True
            and (
                specification in interface_specs
                or specification.rsplit(".", 1)[-1] in interface_specs
            )
            and raw_item.get("presentation_alias") is None
            and raw_item.get("user_approved_scope_exclusion") is None
            and source_status
            not in {"support_only", "quarantined_source_defect"}
        ):
            selected[key] = raw_item
    return selected, mode_error


def _subsumed_by_selected_result_classification(
    folder: Path,
    payload: object,
    *,
    context: EvidenceRunContext | None = None,
    initially_selected: Mapping[str, dict[str, Any]] | None = None,
) -> tuple[dict[str, str], list[str]]:
    """Validate inactive source presentations routed to one selected result.

    These rows remain source-visible and may retain a corrected-target record,
    but the selected canonical item owns the sole semantic contract and proof
    route. Partial or cyclic subsumption stays in the active denominator and
    emits a structural error instead of becoming an exemption.
    """

    if not isinstance(payload, dict):
        return {}, []
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return {}, []
    if initially_selected is None:
        initially_selected, _mode_error = _initial_source_map_proof_obligation_items(
            folder, payload, context=context
        )
    marker = payload.get("semantic_contract_schema")
    marker_supported = schema_version_is_supported(marker, SEMANTIC_CONTRACT_SCHEMAS)
    validated: dict[str, str] = {}
    errors: list[str] = []
    required_values = {
        "coverage_status": SUBSUMED_BY_SELECTED_RESULT,
        "inventory_role": SUBSUMED_BY_SELECTED_RESULT,
        "protocol_role": SUBSUMED_BY_SELECTED_RESULT,
        "source_status": SUBSUMED_BY_SELECTED_RESULT,
        "source_scope_classification": "source_resolved_within_paper_observation",
        "scope_disposition": "supporting_context_for_selected_result",
    }
    for raw_key, raw_item in raw_items.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_item, dict):
            continue
        # Named open problems have a stricter source-presentation validator and
        # a different nonclaim shape. This relation covers retained theorem,
        # lemma, and proof-conclusion presentations.
        if str(raw_item.get("source_kind") or "").strip().lower() == "open_problem":
            continue
        declares_subsumption = bool(
            str(raw_item.get("subsumed_by_source_item") or "").strip()
            or any(
                str(raw_item.get(field) or "").strip().lower()
                == SUBSUMED_BY_SELECTED_RESULT
                for field in (
                    "coverage_status",
                    "inventory_role",
                    "protocol_role",
                    "source_status",
                )
            )
        )
        if not declares_subsumption:
            continue
        prefix = f"items.{key}"
        item_errors: list[str] = []
        for field, expected in required_values.items():
            if str(raw_item.get(field) or "").strip().lower() != expected:
                item_errors.append(f"{prefix}.{field} must be `{expected}`")
        if raw_item.get("claim_bearing") is not True:
            item_errors.append(
                f"{prefix}.claim_bearing must remain true for a subsumed source claim"
            )
        active_fields = [
            field
            for field in SUBSUMED_RESULT_SUPPORT_ROUTE_FIELDS
            if raw_item.get(field) not in (None, [], {})
        ]
        if active_fields:
            item_errors.append(
                f"{prefix} subsumed support item must not own active source route field(s): "
                + ", ".join(active_fields)
            )
        target_id = str(raw_item.get("subsumed_by_source_item") or "").strip()
        target = raw_items.get(target_id)
        if not target_id:
            item_errors.append(f"{prefix}.subsumed_by_source_item is required")
        elif target_id == key:
            item_errors.append(f"{prefix}.subsumed_by_source_item cannot refer to itself")
        elif not isinstance(target, dict):
            item_errors.append(
                f"{prefix}.subsumed_by_source_item `{target_id}` is not a source-map item"
            )
        else:
            if target_id not in initially_selected:
                item_errors.append(
                    f"{prefix}.subsumed_by_source_item `{target_id}` is not selected by the active semantic proof scope"
                )
            if str(target.get("subsumed_by_source_item") or "").strip() or any(
                str(target.get(field) or "").strip().lower()
                == SUBSUMED_BY_SELECTED_RESULT
                for field in (
                    "coverage_status",
                    "inventory_role",
                    "protocol_role",
                    "source_status",
                )
            ):
                item_errors.append(
                    f"{prefix}.subsumed_by_source_item `{target_id}` cannot itself be subsumed"
                )
            if target.get("claim_bearing") is not True:
                item_errors.append(
                    f"{prefix}.subsumed_by_source_item `{target_id}` must be claim-bearing"
                )
            if target.get("source_presentation_alias") is not None:
                item_errors.append(
                    f"{prefix}.subsumed_by_source_item `{target_id}` cannot be a presentation alias"
                )
            if not source_item_effective_route_policy(target)["allows_direct_route"]:
                item_errors.append(
                    f"{prefix}.subsumed_by_source_item `{target_id}` must own an active direct result route"
                )
            contract = target.get("semantic_contract")
            if (
                not marker_supported
                or semantic_contract_validation_errors(
                    contract,
                    schema=marker if marker_supported else SEMANTIC_CONTRACT_SCHEMA,
                )
            ):
                item_errors.append(
                    f"{prefix}.subsumed_by_source_item `{target_id}` must own a valid current semantic_contract"
                )
        if item_errors:
            errors.extend(item_errors)
        else:
            validated[key] = target_id
    return validated, sorted(set(errors))


def validated_subsumed_result_contract_exemptions(
    folder: Path,
    payload: object,
    *,
    context: EvidenceRunContext | None = None,
) -> dict[str, str]:
    """Return inactive support items inheriting one selected result contract."""

    validated, _errors = _subsumed_by_selected_result_classification(
        folder, payload, context=context
    )
    return validated


def _source_map_proof_obligation_items(
    folder: Path,
    payload: object,
    *,
    context: EvidenceRunContext | None = None,
) -> tuple[dict[str, dict[str, Any]], str]:
    """Project one map onto its name-independent direct-proof obligations.

    Source-index extraction is deterministic but comparatively expensive.
    Within one exact evidence transaction, cache the projection by the full
    canonical map identity. Callers without builder-issued authority still
    execute the ordinary selector, and no selected item or validation rule is
    omitted.
    """

    if not isinstance(payload, dict):
        return {}, ""

    def compute() -> tuple[dict[str, dict[str, Any]], str]:
        selected, mode_error = _initial_source_map_proof_obligation_items(
            folder, payload, context=context
        )
        validated, _errors = _subsumed_by_selected_result_classification(
            folder,
            payload,
            context=context,
            initially_selected=selected,
        )
        for support_item in validated:
            selected.pop(support_item, None)
        return selected, mode_error

    value = _run_scoped_cached_value(
        context,
        folder=folder,
        key=("projection", "source_map_proof_obligation_items", canonical_json_digest(payload)),
        compute=compute,
    )
    if (
        not isinstance(value, tuple)
        or len(value) != 2
        or not isinstance(value[0], dict)
        or not isinstance(value[1], str)
    ):
        raise TypeError("source-map proof-obligation cache contains a foreign value")
    return value


def validated_presentation_alias_contract_exemptions(
    folder: Path,
    payload: object,
    *,
    context: EvidenceRunContext | None = None,
) -> dict[str, str]:
    """Return aliases that may inherit, but never own, a semantic contract.

    A repeated source presentation can be claim-bearing while its alias schema
    correctly forbids a second direct Lean route.  It can omit a duplicate
    contract only after three independent source checks: the alias metadata is
    valid, its canonical presentation owns the active proof obligation, and
    both presentations have distinct current byte-pinned source anchors.  A
    canonical compound theorem may legitimately be split into separate
    source-atom claims; in that case the canonical atom's exact current quote
    is the source anchor even when the broad named-result index assigns the
    presentation to a sibling clause.
    """

    if not isinstance(payload, dict):
        return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return {}
    mode, mode_error = source_coverage_mode_from_map(payload)
    if mode_error:
        return {}
    aliases, _alias_errors = source_presentation_aliases(raw_items)
    if not aliases:
        return {}
    current_anchor_items = source_index_byte_pinned_anchor_item_ids(
        folder,
        payload,
        mode,
        context=context,
    )
    selected_items = filter_source_map_items_for_proof_obligations(
        raw_items,
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            payload
        ),
        additional_selected_item_ids=current_anchor_items,
    )
    def canonical_has_current_atom_anchor(item: object) -> bool:
        if not isinstance(item, Mapping):
            return False
        atoms = item.get(SOURCE_CLAIM_ATOMS_KEY)
        if source_claim_atoms_validation_errors(atoms, require_source_quote=True):
            return False
        return not _source_claim_atoms_current_quote_binding_errors(
            folder,
            atoms,
            source_artifact_path=payload.get("source_artifact_path"),
            source_artifact_sha256=payload.get("source_artifact_sha256"),
        )

    return {
        alias: canonical
        for alias, canonical in aliases.items()
        if alias in current_anchor_items
        and (
            canonical in selected_items
            or canonical_has_current_atom_anchor(raw_items.get(canonical))
        )
        and (
            canonical in current_anchor_items
            or canonical_has_current_atom_anchor(raw_items.get(canonical))
        )
    }


def source_spec_correspondence_requirement_errors(
    status_payload: object,
) -> list[str]:
    """Validate the explicit future/reissue requirement switch, if present."""

    if not isinstance(status_payload, dict):
        return []
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return []
    value = review_surface.get("require_source_spec_correspondence")
    if value is None:
        return []
    if not isinstance(value, bool):
        return [
            "review_surface.require_source_spec_correspondence must be Boolean when declared"
        ]
    return []


def source_spec_correspondence_required(status_payload: object) -> bool:
    """Whether a paper declares that v11 realization evidence is mandatory."""

    if not isinstance(status_payload, dict):
        return False
    review_surface = status_payload.get("review_surface")
    return (
        isinstance(review_surface, dict)
        and review_surface.get("require_source_spec_correspondence") is True
    )


def semantic_contract_validation_errors(
    raw_contract: object,
    *,
    schema: int = SEMANTIC_CONTRACT_SCHEMA,
) -> list[str]:
    """Validate an opt-in source-map contract without trusting Lean names.

    Schema 2 deliberately adds only one specialized source-model shape.  Its
    three clauses are source text, not Lean navigation: a selector law, the
    conditional outcome law, and their composed objective/expectation must
    each carry an independently byte-verifiable source anchor.  The actual
    Lean bridge is generated later from the exact explicit contract route.
    """

    if not isinstance(raw_contract, dict):
        return ["semantic_contract must be an object"]
    errors: list[str] = []
    if not schema_version_is_supported(schema, SEMANTIC_CONTRACT_SCHEMAS):
        return [
            "semantic_contract schema must be one of: "
            + ", ".join(str(value) for value in sorted(SEMANTIC_CONTRACT_SCHEMAS))
        ]

    for field in ("spec_declaration", "evidence_declaration"):
        if not isinstance(raw_contract.get(field), str) or not str(
            raw_contract.get(field) or ""
        ).strip():
            errors.append(f"semantic_contract.{field} must be a nonempty string")
    mode = str(raw_contract.get("evidence_mode") or "").strip()
    if mode not in SEMANTIC_CONTRACT_EVIDENCE_MODES:
        errors.append(
            "semantic_contract.evidence_mode must be one of: "
            + ", ".join(sorted(SEMANTIC_CONTRACT_EVIDENCE_MODES))
        )
    shape = str(raw_contract.get("semantic_shape") or "").strip()
    allowed_shapes = (
        SEMANTIC_CONTRACT_SHAPES
        if schema_version_is_exact(schema, SEMANTIC_CONTRACT_SCHEMA)
        else SEMANTIC_CONTRACT_SCHEMA_2_SHAPES
    )
    if shape not in allowed_shapes:
        if schema_version_is_exact(schema, SEMANTIC_CONTRACT_SCHEMA):
            errors.append(
                "semantic_contract.semantic_shape must be `plain` in schema 1; "
                "specialized runtime, initial-transform, and refinement shapes are "
                "unsupported until they have role-bearing Lean Meta checks"
            )
        else:
            errors.append(
                "semantic_contract.semantic_shape must be one of: "
                + ", ".join(sorted(allowed_shapes))
            )

    allowed_fields = {
        "spec_declaration",
        "evidence_declaration",
        "evidence_mode",
        "semantic_shape",
    }
    if shape == CONDITIONAL_PROBABILITY_COMPOSITION_SEMANTIC_SHAPE:
        allowed_fields.add(CONDITIONAL_PROBABILITY_COMPOSITION_FIELD)
    unknown_fields = sorted(set(raw_contract) - allowed_fields)
    if unknown_fields:
        errors.append(
            "semantic_contract has unsupported field(s): "
            + ", ".join(unknown_fields)
        )

    composition = raw_contract.get(CONDITIONAL_PROBABILITY_COMPOSITION_FIELD)
    if shape != CONDITIONAL_PROBABILITY_COMPOSITION_SEMANTIC_SHAPE:
        if composition is not None:
            errors.append(
                "semantic_contract.conditional_probability_composition is allowed only "
                "with semantic_shape `conditional_probability_composition`"
            )
        return errors

    if not schema_version_is_exact(schema, SEMANTIC_CONTRACT_SCHEMA_2):
        errors.append(
            "semantic_contract semantic_shape `conditional_probability_composition` "
            "requires semantic_contract_schema 2"
        )
        return errors
    if not isinstance(composition, dict):
        errors.append(
            "semantic_contract.conditional_probability_composition must be an object"
        )
        return errors
    unexpected_composition_fields = sorted(
        set(composition) - set(CONDITIONAL_PROBABILITY_COMPOSITION_CLAUSES)
    )
    if unexpected_composition_fields:
        errors.append(
            "semantic_contract.conditional_probability_composition has unsupported "
            "field(s): "
            + ", ".join(unexpected_composition_fields)
        )
    for clause in CONDITIONAL_PROBABILITY_COMPOSITION_CLAUSES:
        prefix = f"semantic_contract.conditional_probability_composition.{clause}"
        raw_clause = composition.get(clause)
        if not isinstance(raw_clause, dict):
            errors.append(f"{prefix} must be an object")
            continue
        unexpected_clause_fields = sorted(
            set(raw_clause) - CONDITIONAL_PROBABILITY_COMPOSITION_CLAUSE_FIELDS
        )
        if unexpected_clause_fields:
            errors.append(
                f"{prefix} has unsupported field(s): "
                + ", ".join(unexpected_clause_fields)
            )
        location = raw_clause.get("source_location")
        if not isinstance(location, str) or not location.strip():
            errors.append(f"{prefix}.source_location must be a nonempty string")
        elif not list(SOURCE_FILE_LINE_RE.finditer(location)):
            errors.append(
                f"{prefix}.source_location must include one or more file:line anchors "
                "into the canonical pinned source artifact"
            )
        statement = raw_clause.get("semantic_statement")
        if not isinstance(statement, str) or not statement.strip():
            errors.append(f"{prefix}.semantic_statement must be a nonempty source semantic statement")
        anchors = raw_clause.get("source_anchor_evidence")
        if not isinstance(anchors, list) or not anchors:
            errors.append(
                f"{prefix}.source_anchor_evidence must be a nonempty byte-pinned "
                "source-anchor list"
            )
    return errors


def repaired_source_defect_route_findings(
    folder: Path,
    status: str,
    map_path: Path,
    items: Mapping[str, object],
    valid_contract_items: set[str],
    *,
    marker_supported: bool,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Check repaired-defect links using only frozen JSON sidecars.

    This is deliberately independent of Lean acquisition. It is used both by
    the complete evidence gate and by the cheap pre-context closeout preflight,
    so a missing routing field cannot waste an exact-context/Lean transaction.
    """

    if not marker_supported:
        return []
    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(map_path), message))

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    config = source_proof_fidelity_config(status_payload)
    if config is None:
        fidelity_path = canonical_sidecar(folder, "source_proof_fidelity.json")
    else:
        fidelity_path, path_error = source_proof_fidelity_ledger_path(
            folder, status_payload
        )
        if path_error:
            add(path_error)
            fidelity_path = None
    fidelity = (
        transaction_json(fidelity_path, context)
        if fidelity_path is not None
        else None
    ) or {}
    raw_defects = fidelity.get("defects")
    ledger_ids = {
        str(defect.get("id") or "").strip()
        for defect in (raw_defects if isinstance(raw_defects, list) else [])
        if isinstance(defect, dict) and str(defect.get("id") or "").strip()
    }
    for source_key, raw_item in items.items():
        if not isinstance(raw_item, dict):
            continue
        raw_ids = raw_item.get("source_defect_ids")
        cited_ids = {
            str(value).strip()
            for value in (raw_ids if isinstance(raw_ids, list) else [])
            if isinstance(value, str) and value.strip()
        }
        unknown_ids = sorted(cited_ids - ledger_ids)
        if unknown_ids:
            add(
                f"items.{source_key}.source_defect_ids cites id(s) absent from "
                "the configured source-proof fidelity ledger: "
                + ", ".join(unknown_ids)
            )
    repaired_ids = {
        str(defect.get("id") or "").strip()
        for defect in (raw_defects if isinstance(raw_defects, list) else [])
        if isinstance(defect, dict)
        and str(defect.get("resolution") or "").strip() == "repaired_in_lean"
        and str(defect.get("id") or "").strip()
    }
    for defect_id in sorted(repaired_ids):
        routed = any(
            str(source_key) in valid_contract_items
            and isinstance(raw_item, dict)
            and isinstance(raw_item.get("source_defect_ids"), list)
            and defect_id
            in {
                str(value).strip()
                for value in raw_item["source_defect_ids"]
                if isinstance(value, str)
            }
            for source_key, raw_item in items.items()
        )
        if not routed:
            add(
                f"source-proof defect `{defect_id}` is `repaired_in_lean` but no "
                "source-map item links it through source_defect_ids to a valid "
                "semantic_contract; the full audit must also Lean-check that contract"
            )
    return findings


def _repaired_source_defect_route_preflight_findings_uncached(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Run repaired-defect route shape before expensive Lean acquisition."""

    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(map_path, context)
    if not isinstance(payload, dict):
        return []
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return []
    marker = payload.get("semantic_contract_schema")
    marker_supported = schema_version_is_supported(
        marker, SEMANTIC_CONTRACT_SCHEMAS
    )
    valid_contract_items = {
        str(source_key)
        for source_key, raw_item in raw_items.items()
        if isinstance(raw_item, dict)
        and isinstance(raw_item.get("semantic_contract"), dict)
        and not semantic_contract_validation_errors(
            raw_item["semantic_contract"],
            schema=marker if marker_supported else SEMANTIC_CONTRACT_SCHEMA,
        )
    }
    return repaired_source_defect_route_findings(
        folder,
        status,
        map_path,
        raw_items,
        valid_contract_items,
        marker_supported=marker_supported,
        context=context,
    )


def repaired_source_defect_route_preflight_findings(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate repaired-defect routing once per exact transaction."""

    return _run_scoped_validation_findings(
        context,
        folder=folder,
        status=status,
        require_source_bytes=False,
        validator="repaired_source_defect_route_preflight_findings",
        compute=lambda: _repaired_source_defect_route_preflight_findings_uncached(
            folder,
            status,
            context=context,
        ),
    )


def source_proof_fidelity_config(status_payload: dict[str, Any]) -> dict[str, Any] | None:
    """Return the configured proof-fidelity ledger metadata, when present."""

    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return None
    config = review_surface.get("source_proof_fidelity_review")
    return config if isinstance(config, dict) else None


def explicit_source_routes_enabled(status_payload: dict[str, Any]) -> bool:
    """Return whether the status surface opts into exact v10 source routes."""

    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return False
    statement_review = review_surface.get("llm_statement_review")
    return (
        isinstance(statement_review, dict)
        and statement_review.get("require_explicit_source_routes") is True
    )


def canonical_source_map_has_source_defect_links(
    folder: Path,
    *,
    context: EvidenceRunContext | None = None,
) -> bool:
    """Detect source-defect routing structurally, not by source-row spelling."""

    path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(path, context) or {}
    return source_map_payload_has_source_defect_links(payload)


def source_map_payload_has_source_defect_links(payload: object) -> bool:
    """Detect routed source defects in an already acquired source map."""

    if not isinstance(payload, Mapping):
        return False
    for _key, item in item_entries(payload):
        raw_ids = item.get("source_defect_ids")
        if isinstance(raw_ids, list):
            if any(str(value).strip() for value in raw_ids):
                return True
        elif raw_ids:
            # A malformed nonempty value is still evidence that the paper tried
            # to route a source defect. The ledger/configuration must not become
            # optional merely because a second validator will report the shape.
            return True
    return False


def canonical_source_map_defect_ids(
    folder: Path,
    *,
    context: EvidenceRunContext | None = None,
) -> set[str]:
    """Return every nonblank source-proof defect id routed by the source map."""

    path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(path, context) or {}
    defect_ids: set[str] = set()
    for _key, item in item_entries(payload):
        raw_ids = item.get("source_defect_ids")
        values = raw_ids if isinstance(raw_ids, list) else [raw_ids]
        for value in values:
            if isinstance(value, str) and value.strip():
                defect_ids.add(value.strip())
            elif value is not None:
                # The map-schema validator reports the bad shape when opted
                # in; this full-closeout route must also fail closed rather
                # than dropping a nonblank malformed id before ledger routing.
                defect_ids.add(
                    f"<malformed-source-defect-id:{type(value).__name__}>"
                )
    return defect_ids


def canonical_source_proof_ledger_has_defects(
    folder: Path,
    *,
    context: EvidenceRunContext | None = None,
) -> bool:
    """Return whether the canonical ledger records any source-proof issue."""

    path = transaction_sidecar(folder, "source_proof_fidelity.json", context)
    payload = transaction_json(path, context)
    return bool(payload and payload.get("defects"))


def canonical_source_proof_ledger_has_deep_observations(
    folder: Path,
    *,
    context: EvidenceRunContext | None = None,
) -> bool:
    """Return whether the canonical ledger records audited deep prose findings."""

    path = transaction_sidecar(folder, "source_proof_fidelity.json", context)
    payload = transaction_json(path, context)
    return bool(payload and payload.get("deep_audit_observations"))


def deep_audit_observation_map_link_errors(
    map_payload: object,
    observation_ids: set[str],
) -> list[str]:
    """Validate the source-map links for normal-scope deep observations.

    A deep observation is documentation for an unnumbered prose finding, not a
    new route for discharging a theorem.  The decision whether its linked row
    is outside ordinary scope is therefore made from the source presentation
    via ``source_item_in_coverage_scope``.  Map keys only identify the row in
    diagnostics and are never evidence of scope or of a Lean proof.
    """

    if not isinstance(map_payload, dict):
        return [
            "deep_audit_observations require a readable canonical source map "
            "with linked source rows"
        ]

    errors: list[str] = []
    mode, mode_error = source_coverage_mode_from_map(map_payload)
    if mode_error:
        errors.append(
            "deep_audit_observations cannot establish their normal-scope "
            f"disposition: {mode_error}"
        )
    elif mode != NAMED_THEORETICAL_STATEMENTS:
        errors.append(
            "deep_audit_observations are permitted only when source_coverage_mode "
            "is named_theoretical_statements; deep all-prose review must audit "
            "the claim as an ordinary in-scope item"
        )

    raw_items = map_payload.get("items")
    if not isinstance(raw_items, dict):
        return errors + [
            "deep_audit_observations require source-map items for semantic link validation"
        ]

    linked_ids: set[str] = set()
    for raw_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict):
            continue
        raw_ids = raw_item.get(DEEP_AUDIT_OBSERVATION_LINK_FIELD)
        if raw_ids is None:
            continue
        label = f"items.{str(raw_key)}.{DEEP_AUDIT_OBSERVATION_LINK_FIELD}"
        if (
            not isinstance(raw_ids, list)
            or not raw_ids
            or any(
                not isinstance(value, str) or not value.strip() for value in raw_ids
            )
            or len({value.strip() for value in raw_ids}) != len(raw_ids)
        ):
            errors.append(f"{label} must be a nonempty list of unique observation ids")
            continue

        source_kind = str(raw_item.get("source_kind") or "").strip().lower()
        if source_kind not in DEEP_ONLY_SOURCE_KINDS:
            errors.append(
                f"{label} must use a deep-only source_kind; it is not a "
                "normal-scope exemption for a named theory presentation"
            )
        if source_item_in_coverage_scope(
            raw_item,
            NAMED_THEORETICAL_STATEMENTS,
            declared_environment_kinds=source_named_result_environment_kinds_from_map(
                map_payload
            ),
        ):
            errors.append(
                f"{label} links a source presentation selected by the normal "
                "named-theory scope and therefore cannot be a deep observation"
            )
        if not concrete_source_locator(raw_item.get("source_location")):
            errors.append(f"{label} requires the linked row to have a concrete source_location")
        anchors = raw_item.get("source_anchor_evidence")
        if not isinstance(anchors, list) or not anchors:
            errors.append(
                f"{label} requires the linked row to retain byte-pinned "
                "source_anchor_evidence"
            )

        if raw_item.get("corrected_target") is not None or (
            str(raw_item.get("coverage_status") or "").strip().lower()
            == CORRECTED_SOURCE_STATEMENT_STATUS
        ):
            errors.append(
                f"{label} cannot combine a deep observation with a corrected source target"
            )
        if raw_item.get(USER_APPROVED_SCOPE_EXCLUSION) is not None:
            errors.append(
                f"{label} cannot combine a deep observation with a user scope exclusion"
            )
        routed_defects = raw_item.get("source_defect_ids")
        if isinstance(routed_defects, list):
            has_routed_defect = any(str(value).strip() for value in routed_defects)
        else:
            has_routed_defect = bool(str(routed_defects or "").strip())
        if has_routed_defect:
            errors.append(
                f"{label} cannot route a source-proof defect through source_defect_ids; "
                "a deep observation is not a defect resolution"
            )

        for raw_id in raw_ids:
            observation_id = raw_id.strip()
            if observation_id not in observation_ids:
                errors.append(
                    f"{label} cites unknown deep audit observation `{observation_id}`"
                )
                continue
            linked_ids.add(observation_id)

    unlinked_ids = sorted(observation_ids - linked_ids)
    if unlinked_ids:
        errors.append(
            "deep_audit_observations must each link to at least one semantically "
            "outside-normal-scope source row: "
            + ", ".join(unlinked_ids)
        )
    return errors


def source_proof_fidelity_requirement_reasons(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
    *,
    context: EvidenceRunContext | None = None,
) -> tuple[str, ...]:
    """Return semantic triggers that make a full-closeout ledger mandatory.

    An uncurated historical zero-defect ledger may remain archival without a
    status configuration.  A separate migration gate upgrades that requirement
    when a full-closeout paper has both a source-first curated inventory and a
    canonical ledger.  Once the current surface uses explicit source routes,
    links a source-map item to a source defect, or has a canonical ledger with
    defects, or records a rigorously linked deep prose finding, omitting the
    configuration would hide current source-audit material. These are
    content-level checks and never inspect Lean declaration names.
    """

    if status not in FULL_CLOSEOUT_STATUSES:
        return ()
    reasons: list[str] = []
    if explicit_source_routes_enabled(status_payload):
        reasons.append("the v10 review surface requires explicit source routes")
    if canonical_source_map_has_source_defect_links(folder, context=context):
        reasons.append("the canonical source map links one or more source defects")
    if canonical_source_proof_ledger_has_defects(folder, context=context):
        reasons.append("the canonical source-proof ledger records one or more defects")
    if canonical_source_proof_ledger_has_deep_observations(
        folder, context=context
    ):
        reasons.append(
            "the canonical source-proof ledger records one or more deep audit observations"
        )
    return tuple(reasons)


def canonical_artifact_source_span_errors(
    folder: Path,
    value: object,
    *,
    source_artifact_path: object,
) -> list[str]:
    """Require file-and-line spans to identify one pinned canonical artifact.

    Ordinary fidelity defects can cite a supplementary local transcript. A
    deep prose observation, by contrast, exists only to preserve an exact
    out-of-scope source finding, so its evidence must be a concrete span of the
    ledger's own byte-pinned canonical artifact. This is source-byte identity,
    not a map key or Lean declaration heuristic.
    """

    if not isinstance(value, str):
        return ["must be a source locator string"]
    expected_path, expected_error = resolve_paper_source_path(
        folder, source_artifact_path
    )
    if expected_path is None:
        return [
            "cannot resolve the ledger's canonical source artifact: "
            + expected_error
        ]
    matches = list(SOURCE_FILE_LINE_RE.finditer(value))
    if not matches:
        return [
            "must include a file:line span into the ledger's canonical source artifact"
        ]
    errors: list[str] = []
    for match in matches:
        raw_path = match.group("path")
        candidate, path_error = resolve_paper_source_path(folder, raw_path)
        if candidate is None:
            errors.append(f"source span `{raw_path}` {path_error}")
        elif candidate != expected_path:
            errors.append(
                f"source span `{raw_path}` does not identify the ledger's canonical "
                "source artifact"
            )
    return errors

def source_spec_correspondence_inventory_inputs(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
    graph_native_selected: bool = False,
    automatic_requirement: tuple[bool, str] = (False, "explicit paper closeout requirement"),
) -> tuple[list[Finding], dict[str, Any] | None, list[tuple[str, dict[str, Any]]], bool]:
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
    requirement_errors = source_spec_correspondence_requirement_errors(status_payload)
    required_switch = source_spec_correspondence_required(status_payload)
    automatic_required, automatic_reason = automatic_requirement
    required_at_closeout = status in CLOSEOUT_STATUSES and (
        required_switch or automatic_required
    )
    requirement_prefix = (
        "review_surface.require_source_spec_correspondence: true requires "
        if required_switch
        else "automatic v11 theorem-realization reissue requires "
    )
    payload = transaction_json(map_path, context)
    if not isinstance(payload, dict):
        if not requirement_errors and not required_at_closeout:
            return [], None, [], False
        severity = finding_severity(status)
        findings: list[Finding] = []

        def add_unreadable(message: str) -> None:
            findings.append(Finding(severity, folder.name, rel(map_path), message))

        for error in requirement_errors:
            add_unreadable(error)
        if required_at_closeout:
            add_unreadable(
                requirement_prefix
                + f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY}: "
                f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA} for closeout, but the canonical "
                "source map is missing or invalid ("
                + automatic_reason
                + ")"
            )
        return findings, None, [], False
    raw_items = payload.get("items")
    has_item_record = isinstance(raw_items, dict) and any(
        isinstance(raw_item, dict)
        and SOURCE_SPEC_CORRESPONDENCE_KEY in raw_item
        for raw_item in raw_items.values()
    )
    marker_present = SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY in payload
    if (
        not marker_present
        and not has_item_record
        and not required_at_closeout
        and not requirement_errors
        and not graph_native_selected
    ):
        return [], None, [], False

    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(map_path), message))

    for error in requirement_errors:
        add(error)
    if not marker_present:
        if has_item_record:
            add(
                f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY} is required when an item uses "
                f"{SOURCE_SPEC_CORRESPONDENCE_KEY}"
            )
        if required_at_closeout and not graph_native_selected:
            add(
                requirement_prefix
                + f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY}: "
                f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA} for closeout ("
                + automatic_reason
                + ")"
            )
        if has_item_record or not graph_native_selected:
            return findings, None, [], False
    if marker_present and not schema_version_is_exact(
        payload.get(SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY),
        SOURCE_SPEC_CORRESPONDENCE_SCHEMA,
    ):
        add(
            f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY} must be "
            + str(SOURCE_SPEC_CORRESPONDENCE_SCHEMA)
        )
        return findings, None, [], False
    if not schema_version_is_exact(
        payload.get(SOURCE_CLAIM_ATOMS_SCHEMA_KEY), SOURCE_CLAIM_ATOMS_SCHEMA
    ):
        add(
            "v11 theorem realization requires "
            f"{SOURCE_CLAIM_ATOMS_SCHEMA_KEY}: {SOURCE_CLAIM_ATOMS_SCHEMA}; "
            "a whole source item cannot stand in for individually anchored clauses"
        )
    # A strict atom receipt is meaningful only relative to the current bytes
    # of the map's canonical source artifact.  This is separate from generic
    # source-anchor evidence because strict correspondence must not rely on a
    # paraphrase or a locator that merely happens to look source-like.
    file_bytes_override = (
        context.file_bytes_override() if context is not None else None
    )
    pin_findings = source_artifact_pin_findings(
        folder,
        status,
        map_path,
        payload,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    )
    findings.extend(pin_findings)
    canonical_source_is_current = not pin_findings
    if not isinstance(raw_items, dict):
        add("source-spec correspondence source map `items` must be an object")
        return findings, None, [], False

    _validated_subsumed, subsumption_errors = (
        _subsumed_by_selected_result_classification(
            folder, payload, context=context
        )
    )
    for error in subsumption_errors:
        add(error)
    validated_aliases = validated_presentation_alias_contract_exemptions(
        folder, payload, context=context
    )
    proof_obligation_items, _mode_error = _source_map_proof_obligation_items(
        folder, payload, context=context
    )
    strict_items: list[tuple[str, dict[str, Any]]] = []
    required_source_claim_keys: set[str] = set()
    for raw_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict):
            continue
        source_key = str(raw_key)
        inherited_contract_alias = source_key in validated_aliases
        if inherited_contract_alias:
            # A repeated source presentation is retained for provenance but
            # inherits the canonical claim's review and proof. It must not
            # create a second theorem-realization obligation or human-review
            # denominator row merely because the source repeats the theorem.
            if raw_item.get("claim_bearing") is not False:
                add(
                    f"items.{source_key}: v11 requires claim_bearing: false for a "
                    "repeated source presentation inheriting its canonical review"
                )
            if SOURCE_SPEC_CORRESPONDENCE_KEY in raw_item:
                add(
                    f"items.{source_key}: a presentation alias inheriting its canonical "
                    f"semantic_contract must not own {SOURCE_SPEC_CORRESPONDENCE_KEY}"
                )
            continue
        if source_key not in proof_obligation_items:
            if SOURCE_SPEC_CORRESPONDENCE_KEY in raw_item:
                add(
                    f"items.{source_key}: {SOURCE_SPEC_CORRESPONDENCE_KEY} is allowed only "
                    "on an item selected by the active semantic proof scope (or an "
                    "explicit corrected target)"
                )
            continue
        source_kind = str(raw_item.get("source_kind") or "").strip().lower()
        source_status = str(raw_item.get("source_status") or "").strip().lower()
        source_claim_is_in_scope = (
            source_kind in SOURCE_SPEC_CORRESPONDENCE_SOURCE_KINDS
            and source_status not in SOURCE_SPEC_CORRESPONDENCE_NONCLAIM_STATUSES
        )
        if source_claim_is_in_scope:
            required_source_claim_keys.add(source_key)
            if raw_item.get("claim_bearing") is not True:
                add(
                    f"items.{source_key}: v11 requires claim_bearing: true for every "
                    "in-scope named source claim; an inventory label cannot omit it from "
                    "the theorem-realization audit"
                )
            if not isinstance(raw_item.get("semantic_contract"), dict):
                add(
                    f"items.{source_key}: v11 requires an exact semantic_contract for "
                    "every in-scope named source claim"
                )
            else:
                strict_items.append((source_key, raw_item))
        elif raw_item.get("claim_bearing") is True and isinstance(
            raw_item.get("semantic_contract"), dict):
            strict_items.append((str(raw_key), raw_item))
        elif SOURCE_SPEC_CORRESPONDENCE_KEY in raw_item:
            add(
                f"items.{raw_key}: {SOURCE_SPEC_CORRESPONDENCE_KEY} is allowed only "
                "on a claim-bearing item with an exact semantic_contract"
            )
    if required_source_claim_keys and not strict_items:
        add(
            f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY} requires at least one "
            "claim-bearing exact semantic_contract; otherwise it cannot claim v11 realization coverage"
        )

    return findings, payload, strict_items, canonical_source_is_current


def source_proof_fidelity_ledger_findings(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
    migration_findings: Iterable[Finding] = (),
    corrected_scope_findings: Callable[[], Iterable[Finding]] = lambda: (),
) -> list[Finding]:
    """Validate the semantic source-proof defect ledger for configured papers.

    The ledger is intentionally keyed by source locations and mathematical
    repair obligations. It does not treat Lean declaration names as evidence,
    and its resolution enum intentionally has no source-assumption escape hatch.
    """

    if file_bytes_override is None and context is not None:
        file_bytes_override = context.file_bytes_override()

    migration_findings = list(migration_findings)
    config = source_proof_fidelity_config(status_payload)
    if config is None:
        reasons = source_proof_fidelity_requirement_reasons(
            folder, status, status_payload, context=context
        )
        if not reasons:
            return migration_findings
        return migration_findings + [
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                f"full-closeout status `{status}` requires "
                "review_surface.source_proof_fidelity_review with a ledger_file because "
                + "; ".join(reasons),
            )
        ]
    severity = finding_severity(status)
    ledger_path, path_error = source_proof_fidelity_ledger_path(folder, status_payload)
    if path_error:
        return migration_findings + [
            Finding(
                severity,
                folder.name,
                rel(folder / "status.json"),
                path_error,
            )
        ]
    assert ledger_path is not None

    # Once the paper has a canonical ledger, a full-closeout configuration may
    # not select a second, cleaner file.  The closeout triggers inspect the
    # canonical source map and ledger, so allowing a different configured file
    # here would let live defect debt disappear from the closeout path.  Keep
    # custom paths available for partial/in-progress papers and for papers that
    # have not yet established a canonical sidecar.
    canonical_ledger_path = transaction_sidecar(
        folder, "source_proof_fidelity.json", context
    )
    canonical_ledger_snapshot = (
        context.json_snapshot(canonical_ledger_path) if context is not None else None
    )
    if context is not None:
        canonical_ledger_exists = (
            canonical_ledger_snapshot is not None
            and canonical_ledger_snapshot.sha256 is not None
        )
    elif file_bytes_override is not None:
        canonical_ledger_exists = (
            canonical_ledger_path.resolve() in file_bytes_override
            and file_bytes_override[canonical_ledger_path.resolve()] is not None
        )
    else:
        canonical_ledger_exists = canonical_ledger_path.exists()
    if (
        status in FULL_CLOSEOUT_STATUSES
        and canonical_ledger_exists
        and ledger_path.resolve() != canonical_ledger_path.resolve()
    ):
        return migration_findings + [
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                "full-closeout source_proof_fidelity_review.ledger_file must resolve "
                "to the canonical source-proof fidelity ledger; a separate configured "
                "ledger could hide canonical source-proof defects",
            )
        ]
    if context is not None:
        ledger = transaction_json(ledger_path, context)
    elif file_bytes_override is not None:
        try:
            raw_ledger = json.loads(
                _exact_file_bytes(ledger_path, file_bytes_override)
            )
        except (OSError, RuntimeError, UnicodeDecodeError, json.JSONDecodeError):
            raw_ledger = None
        ledger = raw_ledger if isinstance(raw_ledger, dict) else None
    else:
        ledger = transaction_json(ledger_path, None)
    if ledger is None:
        return migration_findings + [
            Finding(
                severity,
                folder.name,
                rel(ledger_path),
                "configured source-proof fidelity ledger is missing or invalid",
            )
        ]

    findings: list[Finding] = list(migration_findings)
    corrected_scope = author_approved_corrected_scope(status_payload)
    if corrected_scope is not None:
        if context is not None:
            findings.extend(context.corrected_scope_findings)
        else:
            findings.extend(
                corrected_scope_findings()
            )
    corrected_scope_ids = {
        str(correction_id).strip()
        for correction_id in (corrected_scope or {}).get("correction_ids") or []
        if str(correction_id).strip()
    }
    corrected_scope_role: str | None = None
    if corrected_scope is not None:
        corrected_scope_role, _ = corrected_model_scope_role(corrected_scope)
    declared_governing_correction_ids = {
        str(correction.get("id") or "").strip()
        for correction in status_payload.get("governing_corrections") or []
        if isinstance(correction, dict) and str(correction.get("id") or "").strip()
    }

    def add(message: str, *, force_error: bool = False) -> None:
        findings.append(
            Finding(
                "ERROR" if force_error else severity,
                folder.name,
                rel(ledger_path),
                message,
            )
        )

    schema = ledger.get("schema")
    if not schema_version_is_supported(schema, SOURCE_PROOF_FIDELITY_SCHEMAS):
        add("source-proof fidelity ledger must use schema 1 or 2")
    paper = str(ledger.get("paper") or "").strip()
    if paper != folder.name:
        add(
            f"source-proof fidelity ledger names paper `{paper or 'missing'}`, not `{folder.name}`"
        )

    review_status = str(ledger.get("review_status") or "").strip()
    if review_status not in SOURCE_PROOF_FIDELITY_REVIEW_STATUSES:
        add(
            "source-proof fidelity review_status must be one of: "
            + ", ".join(sorted(SOURCE_PROOF_FIDELITY_REVIEW_STATUSES))
        )
        return findings

    needs_closeout_review = status in CLOSEOUT_STATUSES
    if status in FULL_CLOSEOUT_STATUSES and not schema_version_is_exact(schema, 2):
        add(
            f"full-closeout status `{status}` requires source-proof fidelity schema 2 "
            "with issue-level status impact",
            force_error=True,
        )
    review_complete = review_status in {"reviewed_no_defects", "defects_recorded"}
    if needs_closeout_review and not review_complete:
        add(
            f"closeout status `{status}` requires a completed source-proof fidelity review; "
            f"ledger remains `{review_status}`",
            force_error=True,
        )
    if review_complete:
        findings.extend(
            source_artifact_pin_findings(
                folder,
                status,
                ledger_path,
                ledger,
                require_source_bytes=require_source_bytes,
                file_bytes_override=file_bytes_override,
            )
        )

    raw_scopes = ledger.get("reviewed_proof_scopes")
    scopes = raw_scopes if isinstance(raw_scopes, list) else []
    if review_complete and not scopes:
        add("completed source-proof fidelity review has no reviewed_proof_scopes")
    for index, scope in enumerate(scopes):
        label = f"reviewed_proof_scopes[{index}]"
        if not isinstance(scope, dict):
            add(f"{label} must be an object with source locator and semantic scope")
            continue
        if not concrete_source_locator(scope.get("source_locator")):
            add(f"{label}.source_locator must be a concrete source anchor")
        else:
            if require_source_bytes:
                for error in source_file_line_anchor_errors(
                    folder,
                    scope["source_locator"],
                    file_bytes_override=file_bytes_override,
                ):
                    add(f"{label}.source_locator {error}")
        if not meaningful_semantic_text(scope.get("semantic_scope")):
            add(f"{label}.semantic_scope must describe the proof mathematics")
        outcome = str(scope.get("outcome") or "").strip()
        if outcome not in SOURCE_PROOF_FIDELITY_SCOPE_OUTCOMES:
            add(
                f"{label}.outcome must be one of: "
                + ", ".join(sorted(SOURCE_PROOF_FIDELITY_SCOPE_OUTCOMES))
            )
        if review_status == "reviewed_no_defects" and outcome == "defect_recorded":
            add(f"{label} records a defect but review_status is reviewed_no_defects")

    def check_semantic_context_entries(
        raw_entries: object,
        *,
        label: str,
        required_fields: tuple[str, ...],
    ) -> None:
        """Validate optional source-located semantic context structurally.

        These entries are deliberately independent of Lean declaration names.
        They preserve the distinction between an explicit formalization
        convention, a checked source-proof step, and a source theorem/assumption
        when the recursive provenance judge receives the ledger.
        """

        if raw_entries is None:
            return
        if not isinstance(raw_entries, list):
            add(f"{label} must be a list when present")
            return
        seen_ids: set[str] = set()
        for index, entry in enumerate(raw_entries):
            entry_label = f"{label}[{index}]"
            if not isinstance(entry, dict):
                add(f"{entry_label} must be an object")
                continue
            entry_id = str(entry.get("id") or "").strip()
            if not SOURCE_PROOF_DEFECT_ID_RE.fullmatch(entry_id):
                add(
                    f"{entry_label}.id must be a stable nonempty identifier using only "
                    "letters, digits, dot, underscore, or hyphen"
                )
            elif entry_id in seen_ids:
                add(f"{entry_label}.id duplicates {label} entry `{entry_id}`")
            else:
                seen_ids.add(entry_id)
            if not concrete_source_locator(entry.get("source_locator")):
                add(f"{entry_label}.source_locator must be a concrete source anchor")
            elif require_source_bytes:
                for error in source_file_line_anchor_errors(
                    folder,
                    entry["source_locator"],
                    file_bytes_override=file_bytes_override,
                ):
                    add(f"{entry_label}.source_locator {error}")
            for field in required_fields:
                if field in {"id", "source_locator"}:
                    continue
                if not meaningful_semantic_text(entry.get(field)):
                    add(
                        f"{entry_label}.{field} must contain a source-vs-Lean "
                        "mathematical explanation, not a declaration-name reference"
                    )

    check_semantic_context_entries(
        ledger.get("model_conventions"),
        label="model_conventions",
        required_fields=SOURCE_PROOF_MODEL_CONVENTION_REQUIRED_FIELDS,
    )
    check_semantic_context_entries(
        ledger.get("checked_proof_steps"),
        label="checked_proof_steps",
        required_fields=SOURCE_PROOF_CHECKED_STEP_REQUIRED_FIELDS,
    )

    raw_deep_observations = ledger.get("deep_audit_observations")
    deep_observations = (
        raw_deep_observations
        if isinstance(raw_deep_observations, list)
        else []
    )
    if raw_deep_observations is not None and not isinstance(
        raw_deep_observations, list
    ):
        add("deep_audit_observations must be a list when present")
    seen_deep_observation_ids: set[str] = set()
    for index, observation in enumerate(deep_observations):
        label = f"deep_audit_observations[{index}]"
        if not isinstance(observation, dict):
            add(f"{label} must be an object")
            continue
        observation_id = str(observation.get("id") or "").strip()
        if not SOURCE_PROOF_DEFECT_ID_RE.fullmatch(observation_id):
            add(
                f"{label}.id must be a stable nonempty identifier using only "
                "letters, digits, dot, underscore, or hyphen"
            )
        elif observation_id in seen_deep_observation_ids:
            add(
                f"{label}.id duplicates deep audit observation `{observation_id}`"
            )
        else:
            seen_deep_observation_ids.add(observation_id)
        for field in DEEP_AUDIT_OBSERVATION_REQUIRED_FIELDS:
            if field not in observation:
                add(f"{label} is missing required field `{field}`")
        if not concrete_source_locator(observation.get("source_locator")):
            add(f"{label}.source_locator must be a concrete source anchor")
        else:
            for error in canonical_artifact_source_span_errors(
                folder,
                observation["source_locator"],
                source_artifact_path=ledger.get("source_artifact_path"),
            ):
                add(f"{label}.source_locator {error}")
            if require_source_bytes:
                for error in source_file_line_anchor_errors(
                    folder,
                    observation["source_locator"],
                    file_bytes_override=file_bytes_override,
                ):
                    add(f"{label}.source_locator {error}")
        affected = observation.get("affected_source_locators")
        if not isinstance(affected, list) or not affected:
            add(f"{label}.affected_source_locators must list concrete source anchors")
        elif any(not concrete_source_locator(locator) for locator in affected):
            add(
                f"{label}.affected_source_locators contains a non-concrete source anchor"
            )
        else:
            for locator in affected:
                for error in canonical_artifact_source_span_errors(
                    folder,
                    locator,
                    source_artifact_path=ledger.get("source_artifact_path"),
                ):
                    add(f"{label}.affected_source_locators {error}")
                if not require_source_bytes:
                    continue
                for error in source_file_line_anchor_errors(
                    folder, locator, file_bytes_override=file_bytes_override
                ):
                    add(f"{label}.affected_source_locators {error}")
        for field in ("source_claim", "finding", "repair_handoff"):
            if not meaningful_semantic_text(observation.get(field)):
                add(f"{label}.{field} must contain a source-facing mathematical explanation")
        if (
            str(observation.get("normal_scope_disposition") or "").strip()
            != DEEP_AUDIT_OBSERVATION_NORMAL_SCOPE_DISPOSITION
        ):
            add(
                f"{label}.normal_scope_disposition must be "
                f"`{DEEP_AUDIT_OBSERVATION_NORMAL_SCOPE_DISPOSITION}`"
            )
        forbidden_fields = {
            "resolution",
            "statement_impact",
            "status_impact",
            "source_defect_ids",
            "corrected_target",
            USER_APPROVED_SCOPE_EXCLUSION,
        }
        present_forbidden = sorted(forbidden_fields & set(observation))
        if present_forbidden:
            add(
                f"{label} is a documentation-only deep observation and cannot "
                "carry source-defect resolution fields: "
                + ", ".join(present_forbidden)
            )

    if review_status == "reviewed_no_defects" and deep_observations:
        add("reviewed_no_defects ledger cannot contain deep_audit_observations")

    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    if context is not None:
        map_payload = transaction_json(map_path, context)
    elif file_bytes_override is not None:
        try:
            raw_map_payload = json.loads(
                _exact_file_bytes(map_path, file_bytes_override)
            )
        except (OSError, RuntimeError, UnicodeDecodeError, json.JSONDecodeError):
            raw_map_payload = None
        map_payload = raw_map_payload if isinstance(raw_map_payload, dict) else None
    else:
        map_payload = transaction_json(map_path, None)
    map_has_deep_links = bool(
        isinstance(map_payload, dict)
        and isinstance(map_payload.get("items"), dict)
        and any(
            isinstance(item, dict)
            and DEEP_AUDIT_OBSERVATION_LINK_FIELD in item
            for item in map_payload["items"].values()
        )
    )
    if deep_observations or map_has_deep_links:
        for error in deep_audit_observation_map_link_errors(
            map_payload, seen_deep_observation_ids
        ):
            add(error)
    if map_has_deep_links and isinstance(map_payload, dict):
        raw_items = map_payload.get("items")
        assert isinstance(raw_items, dict)
        deep_link_rows = {
            str(key): item
            for key, item in raw_items.items()
            if isinstance(item, dict)
            and DEEP_AUDIT_OBSERVATION_LINK_FIELD in item
        }
        isolated_map_payload = {
            "source_artifact_path": map_payload.get("source_artifact_path"),
            "source_artifact_sha256": map_payload.get("source_artifact_sha256"),
            SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY: True,
            "items": deep_link_rows,
        }
        findings.extend(
            source_anchor_evidence_findings(
                folder,
                status,
                map_path,
                isolated_map_payload,
                require_source_bytes=require_source_bytes,
            )
        )

    raw_defects = ledger.get("defects")
    defects = raw_defects if isinstance(raw_defects, list) else []
    if review_status == "reviewed_no_defects" and defects:
        add("reviewed_no_defects ledger cannot contain defect entries")
    if review_status == "defects_recorded" and not defects and not deep_observations:
        add(
            "defects_recorded ledger must contain at least one source-proof defect "
            "or deep audit observation"
        )
    if raw_defects is not None and not isinstance(raw_defects, list):
        add("source-proof fidelity defects must be a list")

    if status in FULL_CLOSEOUT_STATUSES:
        routed_defect_ids = canonical_source_map_defect_ids(folder)
        ledger_defect_ids = {
            str(defect.get("id") or "").strip()
            for defect in defects
            if isinstance(defect, dict) and str(defect.get("id") or "").strip()
        }
        unresolved_routed_defects = sorted(routed_defect_ids - ledger_defect_ids)
        if unresolved_routed_defects:
            add(
                "full-closeout source map references source_defect_ids absent from "
                "the configured source-proof fidelity ledger: "
                + ", ".join(unresolved_routed_defects[:8])
                + ("; ..." if len(unresolved_routed_defects) > 8 else ""),
                force_error=True,
            )

    seen_defect_ids: set[str] = set()
    status_impacts: list[str] = []
    for index, defect in enumerate(defects):
        label = f"defects[{index}]"
        if not isinstance(defect, dict):
            add(f"{label} must be an object")
            continue
        defect_id = str(defect.get("id") or "").strip()
        if not SOURCE_PROOF_DEFECT_ID_RE.fullmatch(defect_id):
            add(
                f"{label}.id must be a stable nonempty identifier using only "
                "letters, digits, dot, underscore, or hyphen"
            )
        elif defect_id in seen_defect_ids:
            add(f"{label}.id duplicates source-proof defect `{defect_id}`")
        else:
            seen_defect_ids.add(defect_id)
        if not concrete_source_locator(defect.get("source_locator")):
            add(f"{label}.source_locator must be a concrete source anchor")
        else:
            if require_source_bytes:
                for error in source_file_line_anchor_errors(
                    folder,
                    defect["source_locator"],
                    file_bytes_override=file_bytes_override,
                ):
                    add(f"{label}.source_locator {error}")
        for key in (
            "source_claim",
            "repair_obligation",
            "acceptance_condition",
            "resolution_evidence",
        ):
            if not meaningful_semantic_text(defect.get(key)):
                add(f"{label}.{key} must contain a mathematical explanation")
        kind = str(defect.get("defect_kind") or "").strip()
        if kind not in SOURCE_PROOF_FIDELITY_DEFECT_KINDS:
            add(
                f"{label}.defect_kind must be one of: "
                + ", ".join(sorted(SOURCE_PROOF_FIDELITY_DEFECT_KINDS))
            )
        impact = str(defect.get("statement_impact") or "").strip()
        if impact not in SOURCE_PROOF_FIDELITY_STATEMENT_IMPACTS:
            add(
                f"{label}.statement_impact must be one of: "
                + ", ".join(sorted(SOURCE_PROOF_FIDELITY_STATEMENT_IMPACTS))
            )
        status_impact = str(defect.get("status_impact") or "").strip()
        if schema_version_is_exact(schema, 2):
            if status_impact not in SOURCE_PROOF_FIDELITY_STATUS_IMPACTS:
                add(
                    f"{label}.status_impact must be one of: "
                    + ", ".join(sorted(SOURCE_PROOF_FIDELITY_STATUS_IMPACTS))
                )
            else:
                status_impacts.append(status_impact)
            if not meaningful_semantic_text(defect.get("status_impact_rationale")):
                add(
                    f"{label}.status_impact_rationale must explain why the issue is "
                    "note-only, a substantial paper error, or a partial-formalization boundary"
                )
        resolution = str(defect.get("resolution") or "").strip()
        if resolution not in SOURCE_PROOF_FIDELITY_RESOLUTIONS:
            add(
                f"{label}.resolution must be one of: "
                + ", ".join(sorted(SOURCE_PROOF_FIDELITY_RESOLUTIONS))
                + "; source assumptions are not a permitted source-proof-defect resolution",
            )
        is_user_approved_scope_exclusion = (
            resolution == USER_APPROVED_SCOPE_EXCLUSION
        )
        if is_user_approved_scope_exclusion:
            if impact != "source_statement":
                add(
                    f"{label}.user_approved_scope_exclusion requires "
                    "statement_impact source_statement; the source claim remains visible"
                )
            if status_impact != "formalized_note":
                add(
                    f"{label}.user_approved_scope_exclusion requires "
                    "status_impact formalized_note"
                )
            for error in user_approved_scope_exclusion_errors(
                folder,
                defect.get(USER_APPROVED_SCOPE_EXCLUSION),
                expected_source_locator=defect.get("source_locator"),
                require_source_bytes=require_source_bytes,
                file_bytes_override=file_bytes_override,
            ):
                add(f"{label}.{error}")
        affected = defect.get("affected_source_locators")
        if not isinstance(affected, list) or not affected:
            add(f"{label}.affected_source_locators must list affected source anchors")
        elif any(not concrete_source_locator(locator) for locator in affected):
            add(f"{label}.affected_source_locators contains a non-concrete source anchor")
        elif require_source_bytes:
            for locator in affected:
                for error in source_file_line_anchor_errors(
                    folder, locator, file_bytes_override=file_bytes_override
                ):
                    add(f"{label}.affected_source_locators {error}")

        if resolution == "corrected_source_statement" and impact == "proof_only":
            add(f"{label} cannot use corrected_source_statement for a proof_only defect")
        if resolution == "quarantined_source_defect":
            if impact != "source_statement":
                add(
                    f"{label}.quarantined_source_defect requires "
                    "statement_impact source_statement"
                )
            if status_impact != "formalized_note":
                add(
                    f"{label}.quarantined_source_defect requires "
                    "status_impact formalized_note"
                )
        # A paper can have one narrowly approved corrected target and separate
        # local source-proof repairs. Every explicit correction reference must
        # resolve to the paper's governing-correction registry. Only a
        # waiver-capable whole-paper scope may additionally demand that the
        # repair belong to its approved target list; component scopes cannot
        # grant source-result credit to either kind of repair.
        governing_metadata_fields = (
            "governing_disposition",
            "correction_id",
            "corrected_clause_anchor",
            "conclusion_relation",
            "does_not_claim_archive_derivation",
        )
        governed_by_corrected_scope = any(
            field in defect for field in governing_metadata_fields
        )
        if corrected_scope is not None and governed_by_corrected_scope:
            governing_disposition = str(
                defect.get("governing_disposition") or ""
            ).strip()
            correction_id = str(defect.get("correction_id") or "").strip()
            corrected_clause_anchor = str(
                defect.get("corrected_clause_anchor") or ""
            ).strip()
            conclusion_relation = str(
                defect.get("conclusion_relation") or ""
            ).strip()
            if governing_disposition not in CORRECTED_MODEL_GOVERNING_DISPOSITIONS:
                add(
                    f"{label}.governing_disposition must be one of: "
                    + ", ".join(sorted(CORRECTED_MODEL_GOVERNING_DISPOSITIONS))
                )
            if correction_id not in declared_governing_correction_ids:
                add(f"{label}.correction_id must cite a declared governing correction")
            elif (
                corrected_scope_role == WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE
                and correction_id not in corrected_scope_ids
            ):
                add(
                    f"{label}.correction_id must cite a correction included by the "
                    "whole-paper corrected scope"
                )
            if not corrected_clause_anchor:
                add(f"{label}.corrected_clause_anchor must identify the approved correction")
            if conclusion_relation not in CORRECTED_MODEL_CONCLUSION_RELATIONS:
                add(
                    f"{label}.conclusion_relation must be one of: "
                    + ", ".join(sorted(CORRECTED_MODEL_CONCLUSION_RELATIONS))
                )
            if defect.get("does_not_claim_archive_derivation") is not True:
                add(
                    f"{label}.does_not_claim_archive_derivation must be true for an "
                    "author-approved corrected target"
                )
        if schema_version_is_exact(schema, 2) and status_impact == "formalized_with_caveat":
            if impact != "source_statement":
                add(
                    f"{label}.status_impact formalized_with_caveat requires a "
                    "source_statement defect"
                )
            if resolution != "corrected_source_statement":
                add(
                    f"{label}.status_impact formalized_with_caveat requires a fully "
                    "checked corrected_source_statement resolution"
                )
            if status != "formalized with caveat":
                add(
                    f"{label}.status_impact formalized_with_caveat conflicts with paper "
                    f"status `{status}`",
                    force_error=True,
                )
        if (
            schema_version_is_exact(schema, 2)
            and status_impact == "partially_formalized"
            and status in FULL_CLOSEOUT_STATUSES
        ):
            add(
                f"full-closeout status `{status}` conflicts with {label}.status_impact "
                "partially_formalized",
                force_error=True,
            )
        if schema_version_is_exact(schema, 2) and resolution == "open_proof_obligation" and status_impact != "partially_formalized":
            add(
                f"{label}.resolution open_proof_obligation requires status_impact "
                "partially_formalized"
            )
        if schema_version_is_exact(schema, 2) and status in FULL_CLOSEOUT_STATUSES and impact == "uncertain":
            add(
                f"full-closeout status `{status}` conflicts with uncertain statement impact "
                f"in {label}",
                force_error=True,
            )
        if (
            status in FULL_CLOSEOUT_STATUSES
            and resolution == "open_proof_obligation"
        ):
            add(
                f"closed status `{status}` conflicts with {label} still marked open_proof_obligation",
                force_error=True,
            )
    overlapping_issue_ids = sorted(seen_deep_observation_ids & seen_defect_ids)
    if overlapping_issue_ids:
        add(
            "deep_audit_observations must not reuse source-proof defect ids: "
            + ", ".join(overlapping_issue_ids)
        )
    if schema_version_is_exact(schema, 2) and status == PLAIN_FORMALIZED:
        incompatible = sorted(set(status_impacts) - {"formalized_note"})
        if incompatible:
            add(
                "plain `formalized` status permits only formalized_note defects, not: "
                + ", ".join(incompatible),
                force_error=True,
            )
    if schema_version_is_exact(schema, 2) and status == "formalized with caveat" and "formalized_with_caveat" not in status_impacts:
        add(
            "`formalized with caveat` requires at least one schema-2 defect with "
            "status_impact formalized_with_caveat",
            force_error=True,
        )
    return findings

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
        return source_proof_fidelity_ledger_findings(
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
