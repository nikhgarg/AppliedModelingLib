#!/usr/bin/env python3
"""Repository hygiene audit for AppliedModelingLib.

The checks here are intentionally mechanical. They are meant to catch stale
paper-folder structure, hidden Lean proof placeholders, noisy `#check` ledgers,
and status-surface overclaims. Semantic theorem fidelity still requires the
paper-by-paper PDF/DAG audit.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
import subprocess
import sys
import tempfile
import time
import weakref
from dataclasses import dataclass, field as dataclass_field
from datetime import date
from contextlib import nullcontext
from enum import Enum
from pathlib import Path
from typing import Any, Callable, Mapping, MutableMapping

# Direct-file and package execution share one canonical import namespace. This
# replaces per-import fallback branches while preserving the issuer alias below.
if __package__ in {None, ""}:
    repository_root = str(Path(__file__).resolve().parents[1])
    if repository_root not in sys.path:
        sys.path.insert(0, repository_root)

from scripts.formalization_protocol import CURRENT_SOURCE_RECORD_PROMPT_VERSION


def _register_supported_import_aliases() -> None:
    """Keep every supported import path at one closeout-capability issuer.

    Source-record helpers lazily import this module to consume strict closeout
    runtimes.  Direct CLI, package import, and top-level import from
    ``scripts`` must all retain the same ``PaperCloseoutRunContext`` and
    strict-runtime classes.  Publish whichever supported origin loaded first
    under both module aliases, and refuse a hybrid interpreter rather than
    accepting a context issued by the wrong module object.
    """

    if __name__ not in {"__main__", "scripts.audit_repository", "audit_repository"}:
        return
    module = sys.modules.get(__name__)
    if module is None:  # pragma: no cover - Python registers an executing module.
        raise RuntimeError("repository issuer has no executing module")
    for alias in ("scripts.audit_repository", "audit_repository"):
        existing = sys.modules.get(alias)
        if existing is not None and existing is not module:
            raise RuntimeError(
                "repository issuer cannot share an interpreter with "
                f"a distinct `{alias}` issuer"
            )
        sys.modules[alias] = module
    # ``from scripts import audit_repository`` can return a pre-bound package
    # attribute without looking up the aliases above.  Validate and bind that
    # cache as well so a stale attribute cannot accept a foreign strict runtime.
    parent = sys.modules.get("scripts")
    if parent is not None:
        missing = object()
        existing_child = getattr(parent, "audit_repository", missing)
        if existing_child is not missing and existing_child is not module:
            raise RuntimeError(
                "repository issuer cannot share an interpreter with a distinct "
                "`scripts.audit_repository` package attribute"
            )
        try:
            setattr(parent, "audit_repository", module)
        except (AttributeError, TypeError) as exc:
            raise RuntimeError(
                "repository issuer cannot bind the `scripts.audit_repository` "
                "package attribute"
            ) from exc


_register_supported_import_aliases()


from scripts.final_validation_report_status import (
    FINAL_REPORT_CLOSEOUT_STATUS_RE as SHARED_FINAL_REPORT_CLOSEOUT_STATUS_RE,
    FINAL_REPORT_STATUS_LINE_RE as SHARED_FINAL_REPORT_STATUS_LINE_RE,
    final_report_declared_statuses as shared_final_report_declared_statuses,
    report_status_alignment_errors,
)

from scripts.closeout_document_gates import closeout_document_hard_errors

from scripts.lean_axiom_closure import (
    APPROVED_LEAN_AXIOMS,
    LeanAxiomClosureError,
    run_lean_axiom_closures,
)

from scripts.lean_process_diagnostics import (
    bounded_lean_diagnostic_excerpt,
    lean_diagnostic_failure_reason,
)

from scripts.current_closeout.declarations import (
    LeanDeclaration,
    declaration_key,
    declaration_index_from_inventory as lean_declaration_index_from_inventory,
    declaration_index_from_source_records as lean_declaration_index_from_source_records,
    resolve_declaration_name,
    unique_declarations,
)

from scripts.current_closeout.primary_gate import (
    CurrentV11PrimaryGateResult,
    ReviewRoutePartition,
    partition_review_routes,
)
from scripts.current_closeout.primary_gate_transaction import (
    current_v11_primary_gate_result,
    evaluate_and_accept_current_v11_primary_gate,
)

from scripts.closeout_execution_state import (
    CloseoutExecutionLease,
    default_closeout_execution_path,
)

from scripts.closeout_status_projection import (
    CloseoutStatusProjectionError,
    graph_native_human_review_total_from_payload,
)

from scripts.closeout_plan_receipt import (
    load_validated_closeout_plan_receipt,
)

from scripts.obligation_routes import (
    EvidenceRoute,
    EvidenceRouteSet,
    ObligationRouteError,
)


def _legacy_review_surface_structure_module() -> Any:
    """Load the text parser only for ordinary or historical diagnostics.

    Current v11 acceptance obtains declarations, kinds, source ranges, and
    proof relationships from Lean's typed graph. Keeping this import lazy makes
    it impossible for parser availability to become an incidental prerequisite
    of the selected closeout path.
    """

    from scripts import review_surface_structure

    return review_surface_structure


def auxiliary_names_not_exported_from_review_source(
    auxiliary_names: set[str],
    actual_review_names: list[str],
    configured_assumption_declaration_names: set[str] | None = None,
) -> list[str]:
    """Compare configured roles with an already established declaration set."""

    exported = set(actual_review_names)
    exported.update(name.rsplit(".", 1)[-1] for name in actual_review_names)
    exported.update(configured_assumption_declaration_names or set())
    return sorted(auxiliary_names - exported)


def reviewed_names_not_declared_in_review_source(
    include_names: list[str],
    declaration_blocks: Mapping[str, object],
) -> list[str]:
    """Compare configured rows with Lean-owned or legacy declaration records."""

    declared = set(declaration_blocks)
    declared.update(name.rsplit(".", 1)[-1] for name in declaration_blocks)
    return [
        name
        for name in include_names
        if name not in declared and name.rsplit(".", 1)[-1] not in declared
    ]

from scripts.check_formalization_engine_revision import (
    runtime_engine_registration_error,
)

from scripts.statement_sidecar_audit import statement_sidecar_summary_issues

from scripts.source_model_process_obligations import (
    caller_supplied_model_construction_basis,
)

from scripts.lean_signature_manifest import (
    FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_SHA256,
    FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_VERSION,
    FOUNDATION_STRUCTURAL_DATA_MODULE_BY_HEAD,
    RECURSIVE_FIELD_SAFETY_RECEIPT_SCHEMA,
    SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_RECEIPT_FIELD,
    SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_RECEIPT_SCHEMA,
    SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_SCHEMA,
    RepositoryBuildInputSnapshotProvider,
    canonical_semantic_contract_executable_terminals,
    canonical_recursive_field_safety_locator,
    semantic_contract_executable_terminal_receipt_sha256,
)

from scripts.source_record_legacy_contract import (
    EXPLICIT_DIRECT_SOURCE_ROUTE_ORIGIN,
    EXPLICIT_DIRECT_SOURCE_ROUTE_ROLE,
    SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD,
    SOURCE_CLAIM_ATOM_ROUTE_ORIGIN,
    SOURCE_CLAIM_ATOM_ROUTE_ROLE,
    SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
)
from scripts.legacy_source_record_boundary import (
    deferred_legacy_source_record_callable as _deferred_legacy_source_record_callable,
)

from scripts.configured_assumption_formalization_regularities import (
    FORMALIZATION_REGULARITY_CLASSIFICATION,
    load_configured_assumption_formalization_regularity_context,
    response_claims_configured_assumption_formalization_regularity,
)

from scripts.audit_evidence_integrity import (
    SOURCE_CLAIM_ATOMS_KEY,
    SOURCE_CLAIM_ATOMS_SCHEMA,
    SOURCE_CLAIM_ATOMS_SCHEMA_KEY,
    SOURCE_CLAIM_ATOM_THEOREM_LIKE_KINDS,
    SOURCE_SPEC_CORRESPONDENCE_KEY,
    SOURCE_SPEC_CORRESPONDENCE_SCHEMA,
    canonical_source_record_match_sidecar_path,
    canonical_source_record_sidecar_effective_coverage_error,
    corrected_model_scope_model_bindings,
    corrected_model_transitively_reachable_field_items,
    current_paper_statement_map_sha256,
    graph_native_source_spec_realization_receipts,
    graph_authority_source_spec_correspondence_errors,
    raw_source_spec_screening_requested,
    semantic_authority_source_spec_correspondence_errors,
    semantic_contract_closeout_bridge_inventory,
    schema_version_is_exact,
    schema_version_is_supported,
    source_spec_correspondence_item_identity_sha256,
    source_spec_correspondence_enabled,
    source_spec_correspondence_requested,
    source_spec_correspondence_validation_errors,
    source_claim_atoms_validation_errors,
    source_index_byte_pinned_anchor_item_ids,
    source_record_audit_identity_error,
    source_record_effective_semantic_errors,
    source_record_effective_input_judgment_keys,
    source_record_effective_semantic_surface_error,
    source_record_semantic_contract_revalidation_context,
)

from scripts.source_claim_semantic_contract import (
    RecursiveFieldExplicitParentComponentReceipt,
    SemanticContractExecutableTerminalComponentReceipt,
    StrictSourceSpecCorrespondenceReceipt,
    source_claim_component_sha256,
    theorem_realization_components,
)

from scripts.source_coverage_scope import (
    DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
    KNOWN_SOURCE_PRESENTATION_KINDS,
    NAMED_THEORETICAL_STATEMENTS,
    filter_source_map_items_for_proof_obligations,
    explicit_raw_source_spec_screening_requested,
    source_coverage_mode_from_map,
    source_record_source_item_record_sha256,
    source_record_source_item_semantic_sha256,
    source_item_effective_route_policy,
    source_named_result_environment_kinds_from_map,
    source_presentation_aliases,
)

from scripts.root_readme_policy import validate_root_readme

from scripts.repository_check_registry import (
    execute_registered_checks,
    ordinary_repository_checks,
    reusable_library_checks,
)


checked_projection_result = _deferred_legacy_source_record_callable(
    "checked_projection_result"
)
semantic_model_subanalysis_errors = _deferred_legacy_source_record_callable(
    "semantic_model_subanalysis_errors"
)
source_record_classification = _deferred_legacy_source_record_callable(
    "source_record_classification"
)
approved_source_convention_antecedent_errors = (
    _deferred_legacy_source_record_callable(
        "approved_source_convention_antecedent_errors"
    )
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
semantic_association_record_digest = _deferred_legacy_source_record_callable(
    "semantic_association_record_digest"
)
semantic_target_disposition_errors = _deferred_legacy_source_record_callable(
    "semantic_target_disposition_errors"
)
source_contract_association_record_digest = (
    _deferred_legacy_source_record_callable(
        "source_contract_association_record_digest"
    )
)
source_input_target_disposition_errors = _deferred_legacy_source_record_callable(
    "source_input_target_disposition_errors"
)
current_auxiliary_routing_context = _deferred_legacy_source_record_callable(
    "current_auxiliary_routing_context"
)
source_record_item_judgment_current = _deferred_legacy_source_record_callable(
    "source_record_item_judgment_current"
)
canonical_digest_payload = _deferred_legacy_source_record_callable(
    "canonical_digest_payload"
)
source_record_audit_receipt_error = _deferred_legacy_source_record_callable(
    "source_record_audit_receipt_error"
)
source_record_audit_surface_view = _deferred_legacy_source_record_callable(
    "source_record_audit_surface_view"
)
source_record_item_reuse_eligible = _deferred_legacy_source_record_callable(
    "source_record_item_reuse_eligible"
)
source_record_target_route_error = _deferred_legacy_source_record_callable(
    "source_record_target_route_error"
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


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
PUBLIC_RELEASE = (ROOT / "docs" / "PAPER_STATUS.md").exists()
AUDIT_CONFIG = PAPERS / "audit_config.json"


def load_audit_config() -> dict[str, object]:
    if not AUDIT_CONFIG.exists():
        return {}
    payload = json.loads(AUDIT_CONFIG.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{AUDIT_CONFIG.relative_to(ROOT)} should contain a JSON object")
    if not schema_version_is_exact(payload.get("schema"), 1):
        raise ValueError(f"{AUDIT_CONFIG.relative_to(ROOT)} should use schema 1")
    return payload


AUDIT_CONFIG_PAYLOAD = load_audit_config()


def audit_config_string_set(key: str) -> set[str]:
    raw = AUDIT_CONFIG_PAYLOAD.get(key, [])
    if not isinstance(raw, list):
        raise ValueError(f"{key} should be a list")
    return {str(item).strip() for item in raw if str(item).strip()}


ACTIVE_PAPERS = audit_config_string_set("active_papers")
GENERIC_SOURCE_HYGIENE_ALLOWED_TERMS = audit_config_string_set(
    "generic_source_hygiene_allowed_terms"
)


def paper_relative_file(folder: Path, preferred: str, legacy: str | None = None) -> Path:
    """Return the organized paper-local path, falling back to a legacy root file."""

    preferred_path = folder / preferred
    if preferred_path.exists() or legacy is None:
        return preferred_path
    legacy_path = folder / legacy
    if legacy_path.exists():
        return legacy_path
    return preferred_path


PAPER_DOCS_DIR = "docs"
PAPER_AUDIT_DIR = "audit"
FINAL_VALIDATION_REPORT_FILE = "FINAL_VALIDATION_REPORT.md"
POST_FORMALIZATION_AUDIT_FILE = f"{PAPER_DOCS_DIR}/POST_FORMALIZATION_AUDIT.md"
DEPENDENCY_DAG_TEX_FILE = f"{PAPER_DOCS_DIR}/DependencyDAG.tex"
DEPENDENCY_DAG_PDF_FILE = f"{PAPER_DOCS_DIR}/DependencyDAG.pdf"
AGENT_SOURCE_AUDIT_FILE = f"{PAPER_DOCS_DIR}/AGENT_SOURCE_AUDIT.md"
REQUIRED_PAPER_FILES = {
    ".gitignore",
    "PaperInterface.lean",
    "status.json",
}
REQUIRED_GITIGNORE_PATTERNS = {
    "*.pdf",
    "!docs/DependencyDAG.pdf",
    "*.aux",
    "*.log",
    "*.fls",
    "*.fdb_latexmk",
    "*.synctex.gz",
}
REVIEW_LAUNCHER_NAME = "review-dashboard.sh"
REVIEW_LAUNCHER_TARGET = "scripts/launch_review_dashboard.sh"
REVIEW_TRACE_CACHE = ".review_traces/paper_interface_cache.json"
DEFAULT_LLM_ASSUMPTION_JUDGE_FILE = f"{PAPER_AUDIT_DIR}/assumption_match_llm.json"
DEFAULT_ASSUMPTION_SOURCE_FILE = "Assumptions.lean"
DEFAULT_SOURCE_RECORD_AUDIT_FILE = f"{PAPER_AUDIT_DIR}/source_record_audit.json"
DEFAULT_SOURCE_RECORD_JUDGE_FILE = f"{PAPER_AUDIT_DIR}/source_record_match_llm.json"
SOURCE_RECORD_AUDIT_HELPER = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
SOURCE_RECORD_JUDGMENT_ITEM_SECTIONS = (
    "boundary_input_items",
    "theorem_facing_input_items",
    "conclusion_dependency_items",
    "recursive_field_items",
    "semantic_model_items",
    "type_valued_certificate_result_items",
    "source_premise_consistency_items",
)
REQUIRED_LLM_ASSUMPTION_PROMPT_VERSION = "assumption-provenance-v4-verbatim-source-anchor-exact-premise"
REQUIRED_LLM_STATEMENT_PROMPT_VERSION = (
    "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-claim-atoms-supporting-declarations-v4"
)
REQUIRED_SOURCE_RECORD_PROMPT_VERSION = CURRENT_SOURCE_RECORD_PROMPT_VERSION
SOURCE_RECORD_LEAN_IMPORT_CLOSURE_FIELD = "lean_import_closure"


def source_record_raw_integrity_error_if_current(payload: object) -> str:
    """Require the raw-surface receipt only for current v10 artifacts.

    Historical source-record payloads remain visible to the repository audit,
    but cannot silently masquerade as v10 evidence.  The current helper always
    emits the receipt, so a v10 result that lacks it is fail-closed here and in
    the fast evidence gate.
    """

    if not isinstance(payload, dict):
        return "source-record audit payload is not an object"
    if str(payload.get("prompt_version") or "").strip() != (
        REQUIRED_SOURCE_RECORD_PROMPT_VERSION
    ):
        return ""
    return source_record_audit_receipt_error(payload)


SOURCE_RECORD_EXACT_LOCATOR_RE = re.compile(
    r"(?:"
    r"\b(?:page|p\.?)\s*\d+|"
    r"\bappendix\s+[A-Z0-9]+|"
    r"\b(?:section|theorem|lemma|proposition|corollary|definition|equation|"
    r"remark|claim|line)s?\s+(?:[A-Z]?\d[\w.()/-]*|[A-Z](?:\.\d+)*)|"
    r"§\s*[A-Z0-9]+|"
    r"\b[\w./-]+\.(?:tex|txt|md|pdf):\d+"
    r")",
    re.I,
)
APPROVED_SOURCE_RECORD_CLASSIFICATIONS = {
    "container_recursively_audited",
    "derived_consequence_record",
    "derived_from_visible_boundary",
    "nonpropositional_witness_data",
    "proved_from_primitives",
    "validated_source_assumption",
    "approved_source_convention",
    "approved_formalization_regularity",
    "approved_corrected_condition",
    "approved_external_boundary",
    "visible_boundary_component",
}
VISIBLE_BOUNDARY_SOURCE_RECORD_CLASSIFICATIONS = {
    "derived_from_visible_boundary",
    "visible_boundary_component",
}
UNRESOLVED_SOURCE_RECORD_CLASSIFICATIONS = {
    "unresolved_assumed_math",
    "uncertain",
    "mismatch",
    "unknown",
}
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
SEMANTIC_MODEL_BRIDGE_DIMENSIONS = {
    "probability_support_endpoints",
    "joint_law_and_state_evolution",
    "conditioning_and_calibration_semantics",
    "expectation_definedness",
    "null_cell_totalization_and_partition_scope",
    "extended_rate_codomain",
}
REVIEW_ROW_WARN_THRESHOLD = 80
PAPER_STATUS_FILE = PAPERS / "status.json"
HUMAN_STATUS_FILE = PAPERS / "human_status.json"
PAPER_INTERFACE_OVERSIZED_LINE_THRESHOLD = 3000
ROOT_STATUS_VALUES = {
    "Formalized",
    "Formalized with caveat",
    "Formalized with documented caveat",
    "Main endpoints formalized",
    "Main endpoints formalized with documented deviations",
    "Partially formalized",
    "Conditional",
    "Paper draft",
    "Scaffold",
    "Not formalized",
    "Active validation",
}
FORBIDDEN_STATUS_LABEL_RE = re.compile(
    r"\bverified in Lean(?: with source OCR caveat)?\b|"
    r"\bVerified in Lean(?: with source OCR caveat)?\b|"
    r"\bVerified with OCR caveat\b|"
    r"\bVerified with caveat\b|"
    r"\b[Cc]urrent verification status\b|"
    r"\b[Vv]erification status\b|"
    r"<td>\s*Verified\s*</td>|"
    r"\|\s*Verified\s*\|"
)
PAPER_STATUS_VALUES = {
    "formalized",
    "formalized with caveat",
    "partially formalized",
    "conditional",
    "paper draft",
    "scaffold",
    "not started",
    "not formalized",
}
HUMAN_SUMMARY_REVIEW_VALUES = {
    "draft",
    "agent_draft",
    "human_written",
    "human_approved",
}
DAG_REQUIRED_PREAMBLE = "docs/tikz/dag_preamble.tex"
ALLOWED_TRACKED_PAPER_PDFS = {
    "DependencyDAG.pdf",
    "CAVEAT_ISSUES_SUMMARY.pdf",
}
DAG_STATUS_STYLES = {
    "dag_result",
    "dag_lemma",
    "dag_model",
    "dag_caveat",
    "dag_partial",
    "dag_conditional",
    "dag_scaffold",
    "dag_unformalized",
}
PAPER_FOLDER_NAME_RE = re.compile(r"^[A-Z][A-Za-z0-9]*\d{2}[A-Z][A-Za-z0-9]*$")
LEAN_DECL_RE = re.compile(r"^\s*(?:theorem|lemma|def|abbrev|structure|class|inductive|export)\s+", re.M)
SOURCE_EQUATION_WRAPPER_MARKERS = (
    "_formula",
    "_iff",
    "_fields",
    "_rule",
    "_content",
    "_matches",
    "_allocation_payment",
    "_uniform",
    "_pmf",
    "_choice_feasible",
    "_query_choice",
    "_has_",
)
NAME_ONLY_SOURCE_COVERAGE_REASON_RE = re.compile(
    r"exactly matches current dashboard row name|"
    r"exact source-key|"
    r"\bname[-_ ]?match(?:ed|es|ing)?\b|"
    r"\bmatched by name\b",
    re.I,
)
SEMANTIC_BRIDGE_DECLARATION_FIELDS = (
    "semantic_bridge_declarations",
    "paper_equivalence_declarations",
    "source_equivalence_declarations",
    "library_bridge_declarations",
)
THEOREM_LIKE_SOURCE_INVENTORY_KINDS = {
    "lemma",
    "theorem",
    "proposition",
    "corollary",
    "claim",
    "runtime_claim",
}
LEAN_PROOF_DECLARATION_KINDS = {"theorem", "lemma"}
QUARANTINED_SOURCE_DEFECT_STATUS = "quarantined_source_defect"
SOURCE_DECLARATION_ROUTING_FIELDS = (
    "aliases",
    "lean_declarations",
    "proof_lean_declarations",
    "support_lean_declarations",
    *SEMANTIC_BRIDGE_DECLARATION_FIELDS,
)
# These are the declaration routes that can claim direct source coverage.  A
# support declaration may document a defect or a partial boundary, but it must
# never convert that support into coverage of the source theorem.
SOURCE_COVERAGE_DECLARATION_ROUTING_FIELDS = (
    "lean_declarations",
    "proof_lean_declarations",
    *SEMANTIC_BRIDGE_DECLARATION_FIELDS,
)
SEMANTIC_CONTRACT_SCHEMA = 1
SEMANTIC_CONTRACT_SPEC_KINDS = {"def", "abbrev", "inductive"}
SEMANTIC_CONTRACT_EVIDENCE_KINDS = {"theorem", "lemma"}
FORMULA_SPECIFIC_NAME_RE = re.compile(
    r"(?:^|_)(?:"
    r"formula|identity|equation|eq|iff|if_and_only_if|ineq|inequality|"
    r"bound|rule|condition|criterion|definition|fields|cdf|density|pmf|"
    r"probability|expectation|variance|normalization|normalizer|integral|"
    r"derivative|limit|ratio|share|mass|threshold|cutoff|tail"
    r")(?:_|$)",
    re.I,
)
BROAD_REVIEW_ROW_NAME_RE = re.compile(
    r"(?:^|_)(?:"
    r"metrics?|surface|source_surface|core|bundle|package|summary|aggregate|"
    r"model|conditions?|certificate|rows?|fixed_policy|main_result"
    r")(?:_|$)",
    re.I,
)
NUMBERED_SOURCE_RESULT_RE = re.compile(
    r"\b(?:Definition|Lemma|Proposition|Theorem|Corollary|Claim)\s+"
    r"[A-Z]?\d+(?:\s*\([^)]+\))?",
    re.I,
)
GENERIC_SOURCE_THEOREM_LABEL_RE = re.compile(
    r"\b(?:Definition|Lemma|Proposition|Theorem|Corollary|Claim)\s+"
    # Require the numeric label to end at a token boundary.  In particular,
    # reusable Lean names such as `theorem l2Sq_add_eq` are mathematical
    # `l2` APIs, not references to a numbered source theorem.
    r"[A-Z]?\d+(?:\.\d+)*(?![A-Za-z_])(?:\s*\([^)]+\))?",
    re.I,
)
NUMBERED_SOURCE_NAME_RE = re.compile(
    r"(?:^|_)(?:def(?:inition)?|lem(?:ma)?|prop(?:osition)?|thm|theorem|cor(?:ollary)?|claim)"
    r"[A-Z]?\d+(?:_|$)",
    re.I,
)
SOURCE_FORMULA_TEXT_RE = re.compile(
    r"\\(?:frac|sum|sqrt|Phi|int|prod|Pr|mathbb|operatorname)|"
    r"[=<>≤≥↔]|"
    r"\b(?:formula|identity|equation|if and only if|iff|criterion|"
    r"definition|probability|expectation|variance|density|cdf|integral|"
    r"normalization|ratio|mass|threshold|cutoff|tail)\b",
    re.I,
)
SOURCE_STATUS_LINE_RE = re.compile(r"\bSource status\s*:", re.I)
ASSUMPTION_POLICY_STRICT_VALUES = {
    "strict",
    "source_assumptions_only",
}
ASSUMPTION_POLICY_ALLOWED_VALUES = ASSUMPTION_POLICY_STRICT_VALUES | {
    "source-plus-proof-boundary",
}
AXIOM_LIKE_DECL_NAME_RE = re.compile(
    r"^\s*(?:axiom|opaque|unsafe\s+(?:axiom|def|theorem|lemma))\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b"
)
ASSUMPTION_AUDIT_PREMISE_RE = re.compile(r"^\s*--\s*audit-premise:\s*(.+?)\s*$")
APPROVED_ASSUMPTION_JUDGMENTS = {
    "paper_assumption",
    "paper_condition",
    "documented_additional_assumption",
    "documented_caveat",
    "partial_boundary",
}
APPROVED_ASSUMPTION_PREMISE_JUDGMENTS = {
    "paper_assumption",
    "paper_condition",
    "source_text",
    "source_text_model_primitive",
    "derived_from_source_primitives",
    "documented_additional_assumption",
    "documented_caveat",
    "partial_boundary",
}
LEAN_BINDER_RE = re.compile(r"[\(\{]([^()\{\}\[\]]+?)\s*:\s*([^()\{\}\[\]]+?)[\)\}]")
HYPOTHESIS_NAME_RE = re.compile(
    r"^(?:h[A-Za-z0-9_']*|.*(?:assumption|certificate|hypothesis|premise|regularity|bridge|replay|process|row|threshold|capacity).*)$",
    re.I,
)
PROOF_BOUNDARY_TYPE_RE = re.compile(
    r"\b(?:Prop|[A-Za-z0-9_']*(?:Certificate|Assumption|Hypothesis|Witness|Boundary|"
    r"Bridge|Rows?|Table|SourceModel|SourceFamilyRows|SourceRows?|SourceTable|External|Oracle|"
    r"Window|Windows|Package|Regularity|Invariant|Replay|Process))\b",
    re.I,
)
VARIABLE_BOUNDARY_TYPE_RE = re.compile(
    r"\b[A-Za-z0-9_']*(?:Certificate|Assumption|Hypothesis|Witness|Boundary|Bridge|"
    r"Rows?|Table|SourceModel|SourceFamilyRows|SourceRows?|SourceTable|External|Oracle|Window|"
    r"Windows|Package|Regularity|Invariant|Replay|Process)\b",
    re.I,
)
LIBRARY_CERTIFICATE_BOUNDARY_RE = re.compile(
    r"(?:^|[_A-Za-z0-9'])("
    r"cert(?:ificate)?|source[-_ ]?rows?|source[-_ ]?table|row[-_ ]?package|"
    r"external|oracle|boundary|witness|bridge|replay|process|assumption|hypothesis"
    r")",
    re.I,
)
LIBRARY_BOUNDARY_TYPE_RE = re.compile(
    r"\b[A-Za-z0-9_']*(?:"
    r"Certificate|Assumption|Hypothesis|Witness|Boundary|Bridge|Rows?|"
    r"SourceModel|SourceFamilyRows|SourceRows?|SourceTable|External|Oracle|Window|Windows|Package|"
    r"Regularity|Replay|Process"
    r")\b",
    re.I,
)
LIBRARY_EXTERNAL_BOUNDARY_RE = re.compile(r"\b(?:external|oracle|npEqZPP|NP|ZPP|hardness)\b", re.I)
PREDICATE_TYPE_WORD_RE = re.compile(
    r"\b(?:Positive|Nonnegative|NonnegativeBids|Nodup|Feasible|Optimal|Measurable|"
    r"Monotone|Strict|Domain|Truthful|Calibrated|Simplex|Support|Straddles|"
    r"Bound|Bounded|MarginalBound|Invariant|Dominant|Stable|Regular|Window|Windows|"
    r"Package|"
    r"fullSupport|truthful|calibrated|measurable|optimal|feasible)\b"
)
DATA_PARAMETER_TYPE_RE = re.compile(
    r"^(?:ℝ|ℕ|ℤ|Bool|String|Type(?:\\*)?|Sort|List\b|Fin\b|Candidate\b|Seller\b|"
    r"Signal\b|Rule\b|Rating\b|Query\b|Agent\b|Pair\b|Bundle\b|Policy\b|Measure\b)"
)
ALIAS_TARGET_RE = re.compile(
    r":=\s*@?\s*((?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*)"
)
PAPER_FACING_DECL_NAME_RE = re.compile(
    r"^(?:"
    r"paper_interface_|"
    r"source_(?:theorem|lemma|proposition|corollary|definition)"
    r")",
    re.I,
)
PROPOSITION_TYPE_MARKERS = (
    " = ",
    " < ",
    " > ",
    " ≤ ",
    " ≥ ",
    " ≠ ",
    " ↔ ",
    " → ",
    "∀",
    "∃",
    "∈",
    "∉",
)
NON_ARROW_PROPOSITION_TYPE_MARKERS = tuple(
    marker for marker in PROPOSITION_TYPE_MARKERS if marker != " → "
)
LEDGER_PLACEHOLDER_RE = re.compile(
    r"\[Paper Title\]|\bnamespace TEMPLATE\b|\bpaperDefinition1\b|\bpaper_theorem_1\b|Replace before claiming progress",
)
PROOF_FACING_AUDIT_FORMULA_RE = re.compile(
    r"/--(?:(?!-/).)*\bformula\b(?:(?!-/).)*-/\s*noncomputable\s+abbrev\s+audit[A-Za-z0-9_]*",
    re.I | re.S,
)
# Lean 4 uses `axiom` for declarations without values. `constant` is an ordinary
# identifier, including in definition bodies and theorem binder continuations.
AXIOM_LIKE_DECL_RE = re.compile(r"^\s*(?:axiom|opaque|unsafe\s+(?:axiom|def|theorem|lemma))\b")
LIBRARY_STANDARD_DEFINITION_AUDIT_FILE = ROOT / "AppliedModelingLib" / "LibraryDefinitionAudit.lean"
REQUIRED_LIBRARY_STANDARD_AUDITS = {
    "jensenConvex_iff_convexOn_univ": "JensenConvex matches mathlib `ConvexOn ℝ Set.univ`",
    "jensenConcave_iff_concaveOn_univ": "JensenConcave matches mathlib `ConcaveOn ℝ Set.univ`",
    "strictQuasiConvexOnPositive_iff_expected": (
        "StrictQuasiConvexOnPositive has the expected positive-domain strict "
        "quasi-convex inequality"
    ),
    "strictQuasiConcaveOnPositive_iff_expected": (
        "StrictQuasiConcaveOnPositive has the expected positive-domain strict "
        "quasi-concave inequality"
    ),
}
LIBRARY_FORBIDDEN_SOURCE_ASSUMPTION_RE = re.compile(
    r"(?:^|_)(?:source|paper)?(?:assumption|hypothesis)(?:_|$)|"
    r"(?:Source|Paper)?(?:Assumption|Hypothesis)$"
)
REUSABLE_LIBRARY_PROVENANCE_TEXT_RE = re.compile(
    r"\b(?:"
    r"source[- ]paper|source[- ]rows?|source[- ]facing|source[- ]formula|"
    r"source[- ]threshold|displayed source[- ]threshold|displayed formula|"
    r"paper[- ]specific|paper's"
    r")\b",
    re.I,
)
SOURCE_SHAPED_LIBRARY_NAME_RE = re.compile(
    r"(?:^|_)(?:paper|displayed|appendix)(?:_|$)|"
    r"(?:^|_)source(?:[A-Z_]|$).*(?:formula|rate|threshold|row|table|surface|equation|branch|window|paper)|"
    r"^source[A-Z].*(?:Formula|Rate|Threshold|Row|Table|Surface|Equation|Branch|Window|Paper)|"
    r"(?:^|[A-Za-z0-9_'])Source(?:Formula|Rate|Threshold|Row|Rows|Table|Surface|Equation|"
    r"Branch|Window|Paper|Sorted|Critical|Objective|Score|Event)",
    re.I,
)
TUPLE_WITNESS_TARGET_RE = re.compile(r"\b(?:PProd|Prod|PSigma|Sigma)\b|×")
README_AGENT_DETAIL_RE = re.compile(
    r"Get context on this repo|source inventory first|FORMALIZATION_PLAN\.md|"
    r"PostPaperAudit\.lean|pdftotext|econcs-formalizer/SKILL\.md|"
    r"DependencyDAG\.tex|MainTheorems\.lean",
    re.I,
)
README_OLD_STATUS_TABLE_RE = re.compile(
    r"^\|\s*Paper folder\s*\|\s*Paper\s*\|\s*Overall status\s*\|",
    re.M,
)
MARKDOWN_LINK_RE = re.compile(r"\[([^\]]+)\]\([^)]+\)")
README_MAX_LINES = 140
REPORT_LEAN_LABEL_RE = re.compile(
    r"\bLean\s+(?:interface\s+statement(?:\(s\))?|declaration(?:s)?|witness(?:es)?)\s*[:.]",
    re.I,
)
REPORT_DECL_TABLE_HEADER_RE = re.compile(
    r"\bLean\s+(?:interface\s+statement(?:\(s\))?|declaration(?:s)?|witness(?:es)?)\b",
    re.I,
)
REPORT_CODE_SPAN_RE = re.compile(r"`([^`]+)`")
REPORT_DECL_NAME_RE = re.compile(
    r"(?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*"
)
REPORT_NON_DECL_CODE_SUFFIXES = (
    ".lean",
    ".md",
    ".json",
    ".tex",
    ".pdf",
    ".py",
)


@dataclass(frozen=True)
class Finding:
    severity: str
    path: Path
    message: str

    def format(self) -> str:
        rel = self.path.relative_to(ROOT) if self.path.is_absolute() else self.path
        return f"[{self.severity}] {rel}: {self.message}"


class MachinePaperStatusPhase(str, Enum):
    """Bounded validators inside the otherwise monolithic primary paper gate."""

    STATEMENT_SIDECAR = "statement_sidecar"
    INTERFACE_AXIOM_CLOSURE = "interface_axiom_closure"
    PROPOSITION_SPEC_ROUTES = "proposition_spec_routes"
    SOURCE_PROOF_FIDELITY = "source_proof_fidelity"
    EXPLICIT_SEMANTIC_MODEL = "explicit_semantic_model"
    SOURCE_RECORD = "source_record"


def run_machine_paper_status_phase(
    phase: MachinePaperStatusPhase,
    paper_id: str,
    producer: Callable[[], list[Finding]],
    *,
    timings: MutableMapping[str, float] | None = None,
    progress_callback: Callable[[Mapping[str, object]], None] | None = None,
) -> list[Finding]:
    """Run one named primary-gate validator without changing its authority."""

    started = time.perf_counter()

    def publish(status: str, *, elapsed_seconds: float | None = None) -> None:
        if progress_callback is None:
            return
        event: dict[str, object] = {
            "schema": 1,
            "paper": paper_id,
            "phase": phase.value,
            "status": status,
        }
        if elapsed_seconds is not None:
            event["elapsed_seconds"] = elapsed_seconds
        try:
            progress_callback(event)
        except Exception:  # noqa: BLE001 - progress cannot affect evidence.
            pass

    publish("started")
    try:
        findings = producer()
    except BaseException:
        publish("failed", elapsed_seconds=round(time.perf_counter() - started, 6))
        raise
    if not isinstance(findings, list) or any(
        not isinstance(finding, Finding) for finding in findings
    ):
        raise TypeError(f"machine paper-status phase `{phase.value}` returned invalid findings")
    elapsed = round(time.perf_counter() - started, 6)
    if timings is not None:
        timing_key = f"{paper_id}.{phase.value}"
        if timing_key in timings:
            raise RuntimeError(f"machine paper-status phase `{timing_key}` ran twice")
        timings[timing_key] = elapsed
    publish("finished", elapsed_seconds=elapsed)
    return findings


@dataclass(frozen=True)
class BoundaryDependency:
    """A certificate/source-boundary dependency found through declaration closure."""

    category: str
    premise: str
    declaration: LeanDeclaration
    via: str


DECLARATION_REFERENCE_RE = re.compile(
    r"\b(?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*\b"
)
REFERENCE_NAME_STOPLIST = {
    "by",
    "fun",
    "let",
    "have",
    "show",
    "exact",
    "simp",
    "simpa",
    "rw",
    "rfl",
    "from",
    "where",
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "class",
    "Prop",
    "Type",
    "Sort",
    "True",
    "False",
    "And",
    "Or",
    "Not",
    "Iff",
    "Eq",
    "HEq",
    "Nat",
    "Int",
    "Real",
    "Fin",
    "List",
    "Set",
    "Finset",
    "Option",
    "none",
    "some",
    "map",
    "id",
}


def reference_name_is_specific(name: str) -> bool:
    """Return whether a declaration name is specific enough for lexical closure.

    The closure is intentionally conservative: it should catch long paper/library
    helper names and avoid short common names such as `map`, `apply`, or `left`
    that would make static dependency propagation too noisy.
    """

    if not name or name in REFERENCE_NAME_STOPLIST:
        return False
    unqualified = name.rsplit(".", 1)[-1]
    if unqualified in REFERENCE_NAME_STOPLIST:
        return False
    if "." in name:
        return len(unqualified) >= 3
    # Avoid resolving paper-local variables or short prose-shaped identifiers
    # such as `bias`, `objective`, `model`, or `stable` against unrelated
    # reusable-library declarations.  Most cross-declaration proof/API calls in
    # this repo use underscore-heavy descriptive names; direct certificate
    # binders are still caught from declaration signatures separately.
    return "_" in unqualified or "'" in unqualified or len(unqualified) >= 16


def top_level_declaration_body_marker(source: str) -> int | None:
    """Locate the first declaration-level ``:=`` outside binder delimiters.

    Named Lean arguments such as ``(Feature := Fin m)`` can occur in binder
    types before the declaration's result.  Splitting on the first textual
    ``:=`` truncates that signature and can make an explicit ``: Prop`` look
    absent.  This scanner is intentionally small: it only separates a parsed
    declaration block's header from its body and never interprets the type.
    """

    depth = 0
    quote: str | None = None
    escaped = False
    index = 0
    while index + 1 < len(source):
        char = source[index]
        if quote is not None:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == quote:
                quote = None
            index += 1
            continue
        if char == '"':
            quote = char
            index += 1
            continue
        if char in "([{⦃":
            depth += 1
        elif char in ")]}⦄" and depth > 0:
            depth -= 1
        elif depth == 0 and source.startswith(":=", index):
            return index
        index += 1
    return None


def declaration_body(source: str) -> str:
    """Return the proof/body part of a Lean declaration for dependency scans."""

    marker = top_level_declaration_body_marker(source)
    return "" if marker is None else source[marker + 2 :]


def declaration_reference_names(source: str, *, body_only: bool = True) -> set[str]:
    """Return qualified and unqualified declaration-like names in a Lean block."""

    haystack = declaration_body(source) if body_only else source
    haystack = lean_code_text(haystack)
    names: set[str] = set()
    for match in DECLARATION_REFERENCE_RE.finditer(haystack):
        token = match.group(0)
        if not reference_name_is_specific(token):
            continue
        names.add(token)
        if "." in token:
            unqualified = token.rsplit(".", 1)[-1]
            if reference_name_is_specific(unqualified):
                names.add(unqualified)
    return names


def git_ls_files() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files"],
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return result.stdout.splitlines()


REGRESSION_FIXTURE_MODULES = frozenset({
    "AppliedModelingLib.Audit.DeclarationGraphFixture",
    "AppliedModelingLib.Audit.DeclarationGraphFixtureLibrary",
    "AppliedModelingLib.AllForSemanticInventory",
})


def is_regression_fixture(path: Path) -> bool:
    try:
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
    except ValueError:
        return False
    return module in REGRESSION_FIXTURE_MODULES


def check_test_fixture_isolation_in_files(files: Iterable[Path]) -> list[Finding]:
    """Keep deliberately invalid regression declarations out of production imports.

    The semantic-inventory aggregate also imports the regression fixtures and
    is tooling-only. Native declaration-graph tests still compile and inspect
    these modules, including their deliberately unproved boundary.
    """
    pattern = re.compile(
        r"(?<![A-Za-z0-9_'.])(?:"
        + "|".join(re.escape(name) for name in sorted(REGRESSION_FIXTURE_MODULES))
        + r")(?![A-Za-z0-9_'])"
    )
    return [
        Finding("ERROR", path, f"production Lean code references test-only module `{match.group(0)}`")
        for path in files if not is_regression_fixture(path)
        for match in pattern.finditer(lean_code_text(path.read_text(encoding="utf-8")))
    ]


def check_test_fixture_isolation(include_active: bool) -> list[Finding]:
    return check_test_fixture_isolation_in_files(lean_files(include_active))


def lean_files(include_active: bool) -> list[Path]:
    files: list[Path] = []
    try:
        tracked = git_ls_files()
    except subprocess.CalledProcessError:
        tracked = []
    if tracked:
        for rel in tracked:
            path = ROOT / rel
            if path.suffix != ".lean" or not path.exists():
                continue
            if not path.parts:
                continue
            if path.relative_to(ROOT).parts[0] not in {"AppliedModelingLib", "papers"}:
                continue
            if is_regression_fixture(path):
                continue
            if not include_active and any(part in ACTIVE_PAPERS for part in path.parts):
                continue
            files.append(path)
        return sorted(files)

    for root in [ROOT / "AppliedModelingLib", PAPERS]:
        if not root.exists():
            continue
        for path in root.rglob("*.lean"):
            if is_regression_fixture(path):
                continue
            if not include_active and any(part in ACTIVE_PAPERS for part in path.parts):
                continue
            files.append(path)
    return sorted(files)


def strip_line_comment(line: str) -> str:
    """Drop Lean line comments.

    This is deliberately conservative and does not attempt to parse nested block
    comments. It is enough for the placeholder and `#check` ledger checks.
    """

    return line.split("--", 1)[0]


def lean_code_lines_from_text(text: str) -> list[tuple[int, str]]:
    """Return Lean code lines with line and block comments removed."""

    code_lines: list[tuple[int, str]] = []
    depth = 0
    for line_no, line in enumerate(text.splitlines(), start=1):
        out: list[str] = []
        i = 0
        while i < len(line):
            if depth == 0:
                opening = line.find("/-", i)
                if opening < 0:
                    out.append(line[i:])
                    break
                out.append(line[i:opening])
                depth = 1
                i = opening + 2
                continue
            opening = line.find("/-", i)
            closing = line.find("-/", i)
            if closing < 0:
                if opening < 0:
                    break
                depth += 1
                i = opening + 2
                continue
            if 0 <= opening < closing:
                depth += 1
                i = opening + 2
                continue
            depth -= 1
            i = closing + 2
        code_lines.append((line_no, strip_line_comment("".join(out))))
    return code_lines


def lean_code_lines(path: Path) -> list[tuple[int, str]]:
    """Return Lean file lines with line and block comments removed."""

    return lean_code_lines_from_text(path.read_text(encoding="utf-8"))


def lean_code_text(text: str) -> str:
    """Return Lean source text with line and nested block comments removed."""

    return "\n".join(code for _line, code in lean_code_lines_from_text(text))


def check_sorries_in_files(files: list[Path]) -> list[Finding]:
    findings: list[Finding] = []
    sorry_re = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")
    for path in files:
        for line_no, code in lean_code_lines(path):
            if sorry_re.search(code):
                findings.append(Finding("ERROR", path, f"Lean `sorry` at line {line_no}"))
    return findings


def check_sorries(include_active: bool) -> list[Finding]:
    return check_sorries_in_files(lean_files(include_active))


def approved_paper_proof_boundary_declarations() -> dict[Path, set[str]]:
    """Return paper-local Assumptions.lean declarations approved as proof debt."""

    approved: dict[Path, set[str]] = {}
    if not PAPERS.exists():
        return approved
    for status_path in sorted(PAPERS.glob("*/status.json")):
        try:
            payload = json.loads(status_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        review_surface = payload.get("review_surface")
        if not isinstance(review_surface, dict):
            continue
        raw_names = review_surface.get("proof_boundary_names")
        if not isinstance(raw_names, list):
            continue
        names = {name for name in raw_names if isinstance(name, str) and name}
        if not names:
            continue
        raw_source = review_surface.get("assumption_source_file")
        if isinstance(raw_source, str) and raw_source:
            source_path = ROOT / raw_source
        else:
            source_path = status_path.parent / DEFAULT_ASSUMPTION_SOURCE_FILE
        approved.setdefault(source_path.resolve(), set()).update(names)
    return approved


def check_axiom_like_declarations_in_files(files: list[Path]) -> list[Finding]:
    """Reject declarations that can hide unproved premises from paper audits."""

    findings: list[Finding] = []
    approved_boundaries = approved_paper_proof_boundary_declarations()
    for path in files:
        approved_names = approved_boundaries.get(path.resolve(), set())
        for line_no, code in lean_code_lines(path):
            stripped = code.strip()
            if AXIOM_LIKE_DECL_RE.match(stripped):
                match = AXIOM_LIKE_DECL_NAME_RE.match(stripped)
                if match and match.group("name") in approved_names:
                    continue
                findings.append(
                    Finding(
                        "ERROR",
                        path,
                        f"axiom-like Lean declaration at line {line_no}; route premises through "
                        "Assumptions.lean or prove the declaration",
                    )
                )
    return findings


def check_axiom_like_declarations(include_active: bool) -> list[Finding]:
    return check_axiom_like_declarations_in_files(lean_files(include_active))


def hidden_variable_premise_binders(source: str) -> list[str]:
    """Return proof-boundary binders hidden in a Lean `variable` declaration."""

    if not source.strip().startswith("variable"):
        return []
    hidden: list[str] = []
    for match in LEAN_BINDER_RE.finditer(source):
        names = _binder_names(match.group(1))
        type_text = match.group(2).strip()
        if not names:
            continue
        has_boundary_name = any(HYPOTHESIS_NAME_RE.match(name) for name in names)
        has_boundary_type = (
            VARIABLE_BOUNDARY_TYPE_RE.search(type_text) is not None
            or LIBRARY_BOUNDARY_TYPE_RE.search(type_text) is not None
        )
        if not has_boundary_name and not has_boundary_type:
            continue
        if _is_hypothesis_binder(names, type_text):
            hidden.append(normalize_premise_text(f"{' '.join(names)} : {type_text}"))
    return hidden


def check_hidden_variable_premises_in_files(files: list[Path]) -> list[Finding]:
    """Reject section-level proof premises that Lean inserts implicitly."""

    findings: list[Finding] = []
    for path in files:
        for line_no, code in lean_code_lines(path):
            hidden = hidden_variable_premise_binders(code)
            if not hidden:
                continue
            findings.append(
                Finding(
                    "ERROR",
                    path,
                    f"proof-boundary `variable` premise at line {line_no}; make it an explicit "
                    "theorem/definition parameter: "
                    + "; ".join(hidden[:4])
                    + ("; ..." if len(hidden) > 4 else ""),
                )
            )
    return findings


def check_hidden_variable_premises(include_active: bool) -> list[Finding]:
    return check_hidden_variable_premises_in_files(lean_files(include_active))


def check_guarded_checks_in_files(files: list[Path]) -> list[Finding]:
    findings: list[Finding] = []
    for path in files:
        previous_significant = ""
        for line_no, line in lean_code_lines(path):
            code = line.strip()
            if "#check" in code:
                if previous_significant != "#guard_msgs(drop info) in":
                    findings.append(
                        Finding(
                            "ERROR",
                            path,
                            f"unguarded `#check` at line {line_no}; wrap with `#guard_msgs(drop info) in`",
                        )
                    )
            if code:
                previous_significant = code
    return findings


def check_guarded_checks(include_active: bool) -> list[Finding]:
    return check_guarded_checks_in_files(lean_files(include_active))


def paper_dirs(include_template: bool = False) -> list[Path]:
    dirs: list[Path] = []
    try:
        tracked = subprocess.run(
            ["git", "ls-files", "--", "papers/*/status.json"],
            cwd=ROOT,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        ).stdout.splitlines()
    except subprocess.CalledProcessError:
        tracked = []

    if tracked:
        for rel in tracked:
            path = ROOT / rel
            if path.name == "status.json" and path.exists() and path.parent.parent == PAPERS:
                dirs.append(path.parent)
    else:
        dirs = [p for p in PAPERS.iterdir() if p.is_dir()]
    if not include_template:
        dirs = [p for p in dirs if p.name != "TEMPLATE"]
    return sorted(set(dirs))


def is_source_pdf(path: Path) -> bool:
    return (
        path.suffix == ".pdf"
        and path.name not in ALLOWED_TRACKED_PAPER_PDFS
        and not is_declared_tracked_pdf_artifact(path)
    )


def declared_tracked_pdf_artifacts(folder: Path) -> set[Path]:
    """Return non-source PDF artifacts explicitly declared by paper status."""

    payload = load_json_object(folder / "status.json")
    artifacts = payload.get("artifacts") if payload else None
    if not isinstance(artifacts, dict):
        return set()
    declared: set[Path] = set()
    for key, raw_path in artifacts.items():
        if not isinstance(key, str) or "source" in key.lower():
            continue
        if not isinstance(raw_path, str) or not raw_path.endswith(".pdf"):
            continue
        artifact_path = ROOT / raw_path
        try:
            artifact_path.relative_to(folder)
        except ValueError:
            continue
        declared.add(artifact_path)
    return declared


def is_declared_tracked_pdf_artifact(path: Path) -> bool:
    if path.suffix != ".pdf":
        return False
    absolute = path if path.is_absolute() else ROOT / path
    try:
        rel = absolute.relative_to(PAPERS)
    except ValueError:
        return False
    if len(rel.parts) < 2:
        return False
    folder = PAPERS / rel.parts[0]
    return absolute in declared_tracked_pdf_artifacts(folder)


def has_source_pdf(folder: Path) -> bool:
    return any(is_source_pdf(path) for path in folder.rglob("*.pdf"))


def has_text_cache(folder: Path) -> bool:
    return any(path.suffix == ".txt" and path.name != "citation_source.txt" for path in folder.rglob("*.txt"))


def check_paper_contract(include_active: bool) -> list[Finding]:
    findings: list[Finding] = []
    for folder in paper_dirs():
        active = folder.name in ACTIVE_PAPERS
        if active and not include_active:
            continue

        if not PAPER_FOLDER_NAME_RE.fullmatch(folder.name):
            findings.append(
                Finding(
                    "ERROR",
                    folder,
                    "paper folder name should match `[AuthorInitials][2DigitYear][Descriptor]`",
                )
            )

        aggregator = PAPERS / f"{folder.name}.lean"
        if not aggregator.exists():
            findings.append(Finding("ERROR", folder, f"missing paper import file `{aggregator.name}`"))

        for filename in sorted(REQUIRED_PAPER_FILES):
            if not (folder / filename).exists():
                findings.append(Finding("ERROR", folder, f"missing required file `{filename}`"))

        # Migrated papers may keep their theorem endpoints in ProofInterface
        # (or another explicitly configured module) instead of MainTheorems.
        # Validate that owner; a legacy filename is not a second proof obligation.
        proof_file = folder / "MainTheorems.lean"
        try:
            status_payload = json.loads((folder / "status.json").read_text(encoding="utf-8"))
        except (OSError, ValueError):
            status_payload = {}
        review_surface = status_payload.get("review_surface") if isinstance(status_payload, dict) else None
        if isinstance(review_surface, dict):
            configured_file = review_surface.get("proof_file")
            if isinstance(configured_file, str) and configured_file.strip():
                proof_file = proof_endpoint_source_file_path(folder, review_surface)
        if not proof_file.is_file():
            findings.append(Finding("ERROR", folder, f"missing required proof file `{proof_file}`"))

        dag_pdf = paper_relative_file(folder, DEPENDENCY_DAG_PDF_FILE, "DependencyDAG.pdf")
        if not dag_pdf.exists():
            findings.append(Finding("WARN", folder, "rendered `DependencyDAG.pdf` is absent locally"))
        dag_tex = paper_relative_file(folder, DEPENDENCY_DAG_TEX_FILE, "DependencyDAG.tex")
        if dag_tex.exists():
            dag_text = dag_tex.read_text(encoding="utf-8")
            if DAG_REQUIRED_PREAMBLE not in dag_text:
                findings.append(
                    Finding(
                        "ERROR",
                        dag_tex,
                        f"DAG should input shared preamble `{DAG_REQUIRED_PREAMBLE}`",
                    )
                )

        if not has_source_pdf(folder):
            severity = "WARN" if PUBLIC_RELEASE else "ERROR"
            message = (
                "no cached source PDF found; public-release checkouts may omit source PDFs for licensing"
                if PUBLIC_RELEASE
                else "no cached source PDF found"
            )
            findings.append(Finding(severity, folder, message))
        if not PUBLIC_RELEASE and not has_text_cache(folder):
            findings.append(Finding("ERROR", folder, "no cached `pdftotext` source text found"))

        gitignore = folder / ".gitignore"
        if gitignore.exists():
            contents = gitignore.read_text(encoding="utf-8")
            for pattern in sorted(REQUIRED_GITIGNORE_PATTERNS):
                if pattern not in contents:
                    findings.append(Finding("ERROR", gitignore, f"missing ignore pattern `{pattern}`"))

    aggregate_names = re.compile(r"(aggregate|test[-_ ]?of[-_ ]?time)", re.IGNORECASE)
    for folder in paper_dirs(include_template=True):
        if aggregate_names.search(folder.name):
            findings.append(Finding("ERROR", folder, "top-level aggregate paper folder should not exist"))
    return findings


FINAL_REPORT_STATUS_LINE_RE = SHARED_FINAL_REPORT_STATUS_LINE_RE
FINAL_REPORT_HUMAN_VERDICT_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Human\s+Verdict\b"
)
FINAL_REPORT_CLOSEOUT_STATUS_RE = SHARED_FINAL_REPORT_CLOSEOUT_STATUS_RE
FINAL_REPORT_SOURCE_SCOPE_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Source\s+(?:and|And)\s+Scope\b"
)
FINAL_REPORT_RESEARCHER_SUMMARY_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Researcher\s+Summary\s+of\s+Checked\s+Results\b"
)
FINAL_REPORT_REMAINING_BOUNDARIES_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Remaining\s+Boundaries\s+and\s+Gaps\b"
)
FINAL_REPORT_ADDITIONAL_ASSUMPTIONS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Additional\s+Assumptions\s+Beyond\s+Paper\b"
)
FINAL_REPORT_PROOF_DEVIATIONS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Proof-Strategy\s+Deviations\b"
)
FINAL_REPORT_PROOF_TRICKS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Proof\s+Tricks\s+Worth\s+Reusing\b"
)
FINAL_REPORT_GENERALIZATIONS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Generalizations,\s+Conjectures,\s+and\s+Extensions\b"
)
FINAL_REPORT_SOURCE_FIXES_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Mathematical\s+Typos\s+or\s+Other\s+Fixes\s+"
    r"Suggested\s+(?:in|for)\s+the\s+Source\s+Paper\b"
)
FINAL_REPORT_SOURCE_CLARIFICATIONS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Source\s+Clarifications\s+and\s+Exact\s+Readings\b"
)
FINAL_REPORT_ISSUES_CAVEATS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Paper\s+Issues\s+or\s+Caveats\b"
)
FINAL_REPORT_DETAILED_EVIDENCE_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Detailed\s+Formalization\s+Evidence\b"
)
FINAL_REPORT_ASSUMPTION_PROVENANCE_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Paper\s+Assumption\s+Provenance\b"
)
FINAL_REPORT_FORMULA_PROVENANCE_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Displayed\s+Formula\s+Provenance\b"
)
FINAL_REPORT_LIBRARY_LIFT_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Library\s+Lift\s+Pass\b"
)
FINAL_REPORT_DAG_AUDIT_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?DAG\s+Audit\b"
)
FINAL_REPORT_VALIDATION_CHECKS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Validation\s+Checks\b"
)
FINAL_REPORT_DEFINITIONS_CHECKED_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Paper\s+Definitions\s+Checked\b"
)
FINAL_REPORT_THEOREMS_CHECKED_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Named\s+Theorem\s+Statements\s+Checked\b"
)
FINAL_REPORT_VALIDATOR_LEDGER_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Paper-Facing\s+Statement\s+Validator\s+Ledger\b"
)
FINAL_REPORT_SOURCE_COVERAGE_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Source-Coverage\s+Audit\s+Ledger\b"
)
FINAL_REPORT_TITLE_RE = re.compile(r"(?m)^# Final Validation Report:\s+\S")
FINAL_REPORT_UPDATED_RE = re.compile(
    r"(?m)\A# Final Validation Report:[^\n]*\nUpdated: \d{4}-\d{2}-\d{2}\n"
)
FINAL_REPORT_MACHINE_FRONT_MATTER_RE = re.compile(
    r"(?i)\b("
    r"python3|lake\s+build|#print|transitive-source-premise-audit|"
    r"Axiom,\s*Premise|Lean\s+Axiom|Lean\s+footprint|"
    r"LLM\s+statement-translation\s+audit|Model/agent|validator\s+rows?|"
    r"validator\s+status|audit\s+digest|source-record\s+audit|"
    r"source-record\s+sidecar|Lean\s+formalization\s+status|"
    r"Human\s+dashboard\s+review\s+status|Paper\s+interface:|Review\s+surface:"
    r")\b"
)
FINAL_REPORT_OLD_FINAL_VERDICT_RE = re.compile(
    r"(?mi)^##+\s+\d+\.\s+Final\s+Verdict\b"
)
FINAL_REPORT_OLD_ISSUES_CAVEATS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Paper\s+Issues\s+or\s+(?:Formalization\s+Caveats|Errors)\b"
)
FINAL_REPORT_OLD_WHAT_PROVEN_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?(?:What\s+Has\s+Been\s+Proven|What\s+Lean\s+Proves)\b"
)
FINAL_REPORT_CHECKLIST_HEADING_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?"
    r"(?:Paper\s+Assumption\s+Provenance|Displayed\s+Formula\s+Provenance|"
    r"Library\s+Lift\s+Pass|DAG\s+Audit|"
    r"Validation\s+Checks|Validation\s+Commands|Paper\s+Definitions\s+Checked|"
    r"Named\s+Theorem\s+Statements\s+Checked|Paper-Facing\s+Statement\s+Validator\s+Ledger|"
    r"Statement\s+Validator\s+Ledger|Statement\s+Validator\s+Findings)\b"
)
CLOSEOUT_PAPER_STATUSES = {
    "formalized",
    "formalized with caveat",
    "conditional",
}
CLOSEOUT_DAG_REPORT_HEADING_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?DAG\s+(?:Audit|Status)\b"
)
CLOSEOUT_VALIDATION_HEADING_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Validation\s+(?:Checks|Commands)\b"
)
CLOSEOUT_AUDIT_DAG_HEADING_RE = re.compile(r"(?mi)^##+\s+DAG\s+(?:Audit|Status)\b")
CLOSEOUT_AUDIT_COMMANDS_HEADING_RE = re.compile(
    r"(?mi)^##+\s+(?:Validation\s+)?Commands\b"
)
def paper_local_status(folder: Path) -> str:
    status_file = folder / "status.json"
    if not status_file.exists():
        return ""
    try:
        payload = json.loads(status_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return ""
    status = payload.get("status")
    return status.strip().lower() if isinstance(status, str) else ""


def is_closeout_status(status: str) -> bool:
    """Return whether status has one of the declared closeout contracts.

    Status strings are a finite contract shared with the evidence gates.  A
    favorable-looking unknown value must not acquire completed-paper checks
    while bypassing the exact full-closeout evidence requirements.
    """

    return status in CLOSEOUT_PAPER_STATUSES


def final_report_declared_statuses(report_text: str) -> set[str]:
    """Extract explicit whole-paper report statuses despite Markdown wrappers.

    The report's status line is human-facing prose. Read only the current
    ``Closeout Status`` section, not historical discussion, generated ledgers,
    or code examples elsewhere in the report. It accepts ordinary Markdown
    emphasis and a trailing explanatory clause, but never infers status from
    theorem text.
    """

    return shared_final_report_declared_statuses(report_text)


def check_final_report_status_alignment(
    include_active: bool,
    paper_filter: str | None = None,
) -> list[Finding]:
    findings: list[Finding] = []
    for folder in paper_dirs():
        if paper_filter is not None and folder.name != paper_filter:
            continue
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue
        status_file = folder / "status.json"
        report = paper_relative_file(
            folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md"
        )
        if not status_file.exists() or not report.exists():
            continue
        try:
            payload = json.loads(status_file.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        report_text = report.read_text(encoding="utf-8")
        for error in report_status_alignment_errors(payload, report_text):
            findings.append(
                Finding(
                    "ERROR",
                    report,
                    error,
                )
            )
    return findings


def check_final_report_human_facing_front_matter(
    include_active: bool,
    paper_filter: str | None = None,
) -> list[Finding]:
    """Keep the top of final reports useful to researchers before audit detail."""

    findings: list[Finding] = []
    for folder in paper_dirs(include_template=True):
        if paper_filter is not None and folder.name != paper_filter:
            continue
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue
        report = paper_relative_file(
            folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md"
        )
        if not report.exists():
            continue
        report_text = report.read_text(encoding="utf-8")
        if not FINAL_REPORT_TITLE_RE.search(report_text):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "final validation report should use the standard `# Final Validation Report: ...` title",
                )
            )
        template_date = (
            folder.name == "TEMPLATE"
            and report_text.startswith(
                "# Final Validation Report: [Paper Short Name]\nUpdated: YYYY-MM-DD\n"
            )
        )
        if not FINAL_REPORT_UPDATED_RE.search(report_text) and not template_date:
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "final validation report should put `Updated: YYYY-MM-DD` directly below the title",
                )
            )
        human_verdict = FINAL_REPORT_HUMAN_VERDICT_RE.search(report_text)
        if not human_verdict:
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "final validation report should start with a short `Human Verdict` section",
                )
            )
            continue
        next_heading = re.search(r"(?m)^##+\s+", report_text[human_verdict.end():])
        front_matter_end = human_verdict.end() + next_heading.start() if next_heading else min(
            len(report_text),
            human_verdict.start() + 3000,
        )
        front_matter = report_text[human_verdict.start():front_matter_end]
        verdict_body = front_matter.split("\n", 1)[1] if "\n" in front_matter else ""

        if re.search(r"(?m)^###", verdict_body):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "Human Verdict should be concise prose, not nested audit subsections",
                )
            )
        if FINAL_REPORT_MACHINE_FRONT_MATTER_RE.search(verdict_body):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "Human Verdict should avoid commands, Lean identifiers, validator ledgers, "
                    "and audit counters; move machine evidence below Source and Scope",
                )
            )
        if len(re.findall(r"\b\w+\b", verdict_body)) > 140:
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "Human Verdict is too long; keep it to a few researcher-facing sentences",
                )
            )
        if len(re.findall(r"(?m)^\s*-\s+", verdict_body)) >= 3:
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "Human Verdict looks like an audit ledger; use short prose instead",
                )
            )
        if FINAL_REPORT_OLD_FINAL_VERDICT_RE.search(report_text):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "use `Closeout Status` instead of a repetitive `Final Verdict` section",
                )
            )
        if FINAL_REPORT_OLD_ISSUES_CAVEATS_RE.search(report_text):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "use the human-facing `Paper Issues or Caveats` section title, "
                    "even when the body is `None found.`",
                )
            )
        if FINAL_REPORT_OLD_WHAT_PROVEN_RE.search(report_text):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "use `Researcher Summary of Checked Results` plus later "
                    "`Detailed Formalization Evidence`, not `What Has Been Proven`",
                )
            )

        closeout = FINAL_REPORT_CLOSEOUT_STATUS_RE.search(report_text)
        source_scope = FINAL_REPORT_SOURCE_SCOPE_RE.search(report_text, human_verdict.end())
        summary = FINAL_REPORT_RESEARCHER_SUMMARY_RE.search(report_text)
        remaining = FINAL_REPORT_REMAINING_BOUNDARIES_RE.search(report_text)
        additional = FINAL_REPORT_ADDITIONAL_ASSUMPTIONS_RE.search(report_text)
        deviations = FINAL_REPORT_PROOF_DEVIATIONS_RE.search(report_text)
        tricks = FINAL_REPORT_PROOF_TRICKS_RE.search(report_text)
        generalizations = FINAL_REPORT_GENERALIZATIONS_RE.search(report_text)
        source_fixes = FINAL_REPORT_SOURCE_FIXES_RE.search(report_text)
        source_clarifications = FINAL_REPORT_SOURCE_CLARIFICATIONS_RE.search(
            report_text
        )
        source_reading = source_clarifications or source_fixes
        issues = FINAL_REPORT_ISSUES_CAVEATS_RE.search(report_text)
        detailed = FINAL_REPORT_DETAILED_EVIDENCE_RE.search(report_text)
        required_front_sections = [
            ("Closeout Status", closeout),
            ("Source and Scope", source_scope),
            ("Researcher Summary of Checked Results", summary),
            ("Remaining Boundaries and Gaps", remaining),
            ("Additional Assumptions Beyond Paper", additional),
            ("Proof-Strategy Deviations", deviations),
            ("Proof Tricks Worth Reusing", tricks),
            ("Generalizations, Conjectures, and Extensions", generalizations),
            ("Source Clarifications and Exact Readings", source_reading),
            ("Paper Issues or Caveats", issues),
        ]
        for title, match in required_front_sections:
            if not match:
                findings.append(
                    Finding(
                        "WARN",
                        report,
                        f"final validation report should include `{title}` in the human-facing 1--11 front matter",
                    )
                )
        present_positions = [
            human_verdict.start(),
            *[
                match.start()
                for match in [
                    closeout,
                    source_scope,
                    summary,
                    remaining,
                    additional,
                    deviations,
                    tricks,
                    generalizations,
                    source_reading,
                    issues,
                ]
                if match
            ],
        ]
        if present_positions != sorted(present_positions):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "final validation report should order front sections as Human Verdict, "
                    "Closeout Status, Source and Scope, Researcher Summary, "
                    "Remaining Boundaries, Additional Assumptions, Proof-Strategy "
                    "Deviations, Proof Tricks, Generalizations/Conjectures/"
                    "Extensions, Source Clarifications and Exact Readings, and Paper "
                    "Issues or Caveats; technical appendices are optional and follow them",
                )
            )
        if detailed:
            pre_detail = report_text[human_verdict.start():detailed.start()]
            if FINAL_REPORT_CHECKLIST_HEADING_RE.search(pre_detail):
                findings.append(
                    Finding(
                        "WARN",
                        report,
                        "checklist/provenance/Lean evidence headings should appear after "
                        "`Detailed Formalization Evidence`, not in the researcher-facing front matter",
                    )
                )
    return findings


def check_dag_and_validation_report_closeout(
    include_active: bool,
    paper_filter: str | None = None,
    *,
    force_selected_closeout: bool = False,
    final_holistic_surface_sha256: str = "",
    all_selected_semantic_review_sha256: str | None = None,
    final_holistic_review_policy_assurance: Mapping[str, object] | None = None,
) -> list[Finding]:
    """Ensure completed paper closeout audits include DAG/report evidence."""

    findings: list[Finding] = []
    for folder in paper_dirs():
        if paper_filter is not None and folder.name != paper_filter:
            continue
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue
        status = paper_local_status(folder)
        if not is_closeout_status(status) and not (
            force_selected_closeout and paper_filter == folder.name
        ):
            continue
        status_payload = load_json_object(folder / "status.json") or {}

        report = paper_relative_file(
            folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md"
        )
        post_audit = paper_relative_file(
            folder, POST_FORMALIZATION_AUDIT_FILE, "POST_FORMALIZATION_AUDIT.md"
        )
        dag_tex = paper_relative_file(folder, DEPENDENCY_DAG_TEX_FILE, "DependencyDAG.tex")
        dag_pdf = paper_relative_file(folder, DEPENDENCY_DAG_PDF_FILE, "DependencyDAG.pdf")
        agent_source_audit = folder / AGENT_SOURCE_AUDIT_FILE
        corrected_scope_current = current_author_approved_corrected_scope(
            folder, status_payload
        )
        final_holistic_required = explicit_raw_source_spec_screening_requested(
            status_payload
        )
        for document_error in closeout_document_hard_errors(
            folder,
            corrected_scope_current=corrected_scope_current,
            final_holistic_required=final_holistic_required,
            require_visual_dag_inspection=True,
            final_holistic_surface_sha256=final_holistic_surface_sha256,
            all_selected_semantic_review_sha256=(
                all_selected_semantic_review_sha256
            ),
            final_holistic_review_policy_assurance=(
                final_holistic_review_policy_assurance
            ),
            post_formalization_audit=post_audit,
        ):
            findings.append(
                Finding("ERROR", document_error.path, document_error.message)
            )

        if not report.exists():
            findings.append(
                Finding(
                    "ERROR",
                    folder,
                    "completed paper is missing `FINAL_VALIDATION_REPORT.md`",
                )
            )
        else:
            try:
                report_text = report.read_text(encoding="utf-8")
            except OSError:
                # The shared hard gate emits the ERROR; warnings need readable text.
                report_text = ""
            if report_text:
                if not CLOSEOUT_DAG_REPORT_HEADING_RE.search(report_text):
                    findings.append(
                        Finding(
                            "WARN",
                            report,
                            "final validation report should include a `DAG Audit` or `DAG Status` section",
                        )
                    )
                if not CLOSEOUT_VALIDATION_HEADING_RE.search(report_text):
                    findings.append(
                        Finding(
                            "WARN",
                            report,
                            "final validation report should include a `Validation Checks` or `Validation Commands` section",
                        )
                    )
                for artifact in ("DependencyDAG.tex", "DependencyDAG.pdf"):
                    if artifact not in report_text:
                        findings.append(
                            Finding(
                                "WARN",
                                report,
                                f"final validation report should name `{artifact}` in the DAG audit evidence",
                            )
                        )
                if f"--paper {folder.name}" not in report_text or "scripts/audit_repository.py" not in report_text:
                    findings.append(
                        Finding(
                            "WARN",
                            report,
                            "final validation report should record the targeted repository audit command",
                        )
                    )
        if (
            not corrected_scope_current or final_holistic_required
        ) and agent_source_audit.exists():
            try:
                agent_audit_text = agent_source_audit.read_text(encoding="utf-8")
            except OSError:
                # The shared hard gate already reports the unreadable document.
                agent_audit_text = ""
            if agent_audit_text:
                for heading in (
                    "Source Inventory",
                    "Lean Interface Comparison",
                    "Machine Audit Results",
                    "Findings",
                ):
                    if not re.search(rf"^##\s+{re.escape(heading)}\s*$", agent_audit_text, re.M):
                        findings.append(
                            Finding(
                                "WARN",
                                agent_source_audit,
                                f"`docs/AGENT_SOURCE_AUDIT.md` should include a `{heading}` section",
                            )
                        )

        if post_audit.exists():
            try:
                audit_text = post_audit.read_text(encoding="utf-8")
            except OSError:
                # The shared hard gate emits the ERROR; warnings need readable text.
                audit_text = ""
            if audit_text and not CLOSEOUT_AUDIT_DAG_HEADING_RE.search(audit_text):
                findings.append(
                    Finding(
                        "WARN",
                        post_audit,
                        "post-formalization audit should include a `DAG Audit` section",
                    )
                )
            if audit_text and not CLOSEOUT_AUDIT_COMMANDS_HEADING_RE.search(audit_text):
                findings.append(
                    Finding(
                        "WARN",
                        post_audit,
                        "post-formalization audit should include a commands/validation commands section",
                    )
                )
            for artifact in (
                "FINAL_VALIDATION_REPORT.md",
                "DependencyDAG.tex",
                "DependencyDAG.pdf",
            ):
                if not audit_text:
                    break
                if artifact not in audit_text:
                    findings.append(
                        Finding(
                            "WARN",
                            post_audit,
                            f"post-formalization audit should name `{artifact}`",
                        )
                    )
            if audit_text and (
                f"--paper {folder.name}" not in audit_text
                or "scripts/audit_repository.py" not in audit_text
            ):
                findings.append(
                    Finding(
                        "WARN",
                        post_audit,
                        "post-formalization audit should record the targeted repository audit command",
                    )
                )
        if not dag_pdf.exists():
            findings.append(
                Finding(
                    "ERROR",
                    dag_pdf,
                    "completed paper is missing rendered `DependencyDAG.pdf`",
                )
            )
        elif dag_tex.exists() and dag_pdf.stat().st_mtime + 1 < dag_tex.stat().st_mtime:
            findings.append(
                Finding(
                    "WARN",
                    dag_pdf,
                    "`DependencyDAG.pdf` is older than `DependencyDAG.tex`; rerender and visually inspect it",
                )
            )

    return findings


def _safe_slice_id(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "-", value.strip()).strip("-") or "all"


def zero_row_review_surface_imports_paper_module(
    paper_id: str,
    review_source_text: str,
    actual_review_names: list[str],
) -> bool:
    """Return true when an empty review surface is just a paper-local import shim."""

    if actual_review_names:
        return False
    paper_local_import_re = re.compile(rf"(?m)^\s*import\s+{re.escape(paper_id)}\.")
    return paper_local_import_re.search(review_source_text) is not None


def status_allows_empty_review_surface(status_payload: dict[str, object]) -> bool:
    """Return true for draft intakes that explicitly configure no review rows."""

    if status_payload.get("status") != "paper draft":
        return False
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return False
    for key in ("include_names", "assumption_names", "auxiliary_names"):
        value = review_surface.get(key)
        if not isinstance(value, list) or value:
            return False
    quarantined = review_surface.get("quarantined_auxiliary_names", [])
    if not isinstance(quarantined, list) or quarantined:
        return False
    human_review = status_payload.get("human_review")
    if isinstance(human_review, dict) and human_review.get("total_rows") != 0:
        return False
    return True


def _leading_comment_before(lines: list[str], line_number: int) -> str:
    """Return the contiguous comment block immediately before a declaration."""

    index = line_number - 2
    while index >= 0 and not lines[index].strip():
        index -= 1
    if index < 0:
        return ""

    stripped = lines[index].strip()
    if stripped.startswith("--"):
        end = index
        while index >= 0 and lines[index].strip().startswith("--"):
            index -= 1
        return "\n".join(lines[index + 1 : end + 1]).strip()

    if "-/" in stripped:
        end = index
        while index >= 0 and "/-" not in lines[index]:
            index -= 1
        if index >= 0:
            return "\n".join(lines[index : end + 1]).strip()

    return ""


def review_declaration_comments(interface_text: str) -> dict[str, str]:
    """Return leading paper-facing comments keyed by declaration name."""

    lines = interface_text.splitlines()
    return {
        name: _leading_comment_before(lines, line_number)
        for name, (line_number, _kind, _source) in (
            _legacy_review_surface_structure_module()
            .review_declaration_blocks(interface_text)
            .items()
        )
    }


def _declaration_target_source(declaration_source: str) -> str:
    """Return the source text of a Lean declaration's result type, if visible.

    This is intentionally syntactic. The review-surface hygiene audit only
    needs to know whether the paper-facing declaration target exposes tuple
    witness data; product words in declaration names or ordinary input binders
    must not matter.
    """

    header = declaration_source.split(":=", 1)[0]
    depth = 0
    for index, char in enumerate(header):
        if char in "([{":
            depth += 1
            continue
        if char in ")]}":
            depth = max(depth - 1, 0)
            continue
        if char == ":" and depth == 0:
            return header[index + 1 :].strip()
    return ""


def interface_tuple_witness_declarations(interface_text: str) -> list[tuple[int, str]]:
    """Return review declarations whose result type exposes tuple witness data."""

    flagged: list[tuple[int, str]] = []
    declaration_blocks = (
        _legacy_review_surface_structure_module().review_declaration_blocks(
            interface_text
        )
    )
    for name, (line_number, _kind, source) in declaration_blocks.items():
        target = _declaration_target_source(source)
        if target and TUPLE_WITNESS_TARGET_RE.search(target):
            flagged.append((line_number, name))
    return sorted(flagged)


def namespace_stacks_at_lines(text: str, line_numbers: set[int]) -> dict[int, list[str]]:
    """Return simple Lean namespace stacks before selected source lines.

    Scan the file once.  Paper-level declaration inventories can contain many
    declarations in large proof files, so repeatedly rescanning from the first
    line for each declaration turns a linear namespace lookup into quadratic
    closeout work.
    """

    # Lean's anonymous `end` closes the most recent namespace *or section*.
    # Keep the two scope kinds distinct: treating `end` for a local section as
    # a namespace close silently gives later PaperInterface declarations the
    # wrong fully-qualified name.
    stack: list[str] = []
    scopes: list[tuple[str, list[str]]] = []
    stacks: dict[int, list[str]] = {}
    for current_line, code in lean_code_lines_from_text(text):
        if current_line in line_numbers:
            stacks[current_line] = list(stack)
        stripped = code.strip()
        match = re.match(r"^namespace\s+(.+)$", stripped)
        if match:
            names = [
                part
                for part in re.split(r"\s+", match.group(1).strip())
                if part
            ]
            stack.extend(names)
            scopes.append(("namespace", names))
            continue
        if re.match(r"^section(?:\s+.*)?$", stripped):
            scopes.append(("section", []))
            continue
        match = re.match(r"^end(?:\s+(.+))?$", stripped)
        if not match:
            continue
        raw_names = (match.group(1) or "").strip()
        if not raw_names:
            if not scopes:
                continue
            kind, names = scopes.pop()
            if kind == "namespace":
                del stack[len(stack) - len(names) :]
            continue

        names = [part for part in re.split(r"\s+", raw_names) if part]
        # Explicit namespace closes should match the innermost namespace
        # scope.  Be conservative if malformed source is encountered: do not
        # consume an unrelated local section or outer namespace.
        if not scopes or scopes[-1][0] != "namespace":
            continue
        _kind, namespace_names = scopes[-1]
        if names != namespace_names and names != namespace_names[-len(names) :]:
            continue
        scopes.pop()
        del stack[len(stack) - len(namespace_names) :]
    return stacks


def namespace_stack_at_line(text: str, line_number: int) -> list[str]:
    """Return the simple Lean namespace stack before `line_number`."""

    return namespace_stacks_at_lines(text, {line_number}).get(line_number, [])


def qualified_review_decl_name(interface_text: str, line_number: int, name: str) -> str:
    namespaces = namespace_stack_at_line(interface_text, line_number)
    return ".".join([*namespaces, name]) if namespaces else name


def lean_module_name(path: Path) -> str:
    """Return the Lean module name corresponding to a repository Lean file."""

    rel = path.relative_to(ROOT).with_suffix("")
    parts = list(rel.parts)
    if parts and parts[0] == "papers":
        parts = parts[1:]
    return ".".join(parts)


def check_paper_interface_axiom_closure(
    paper_id: str,
    interface_path: Path,
    interface_text: str,
    include_names: list[str],
    declaration_blocks: dict[str, tuple[int, str, str]],
    status: object,
    approved_boundary_axioms: set[str] | None = None,
) -> list[Finding]:
    """Run Lean-native `#print axioms` on paper-facing review rows.

    This is the exact transitive proof-debt check. It catches `sorryAx`,
    declared axioms/constants, and opaque unsafe foundations no matter how many
    reusable-library layers lie between the paper theorem and the dependency.
    It deliberately does not try to classify theorem parameters; visible
    premise/source-assumption checks handle those separately from the expanded
    Lean statement.
    """

    rows: list[tuple[str, str, int]] = []
    for name in include_names:
        declaration = declaration_blocks.get(name)
        if declaration is None:
            continue
        line_no, _kind, _source = declaration
        rows.append((name, qualified_review_decl_name(interface_text, line_no, name), line_no))
    if not rows:
        return []

    severity = completed_status_finding_severity(status)
    module_name = lean_module_name(interface_path)
    try:
        parsed = run_lean_axiom_closures(
            ROOT,
            module_name,
            (qualified_name for _name, qualified_name, _line_no in rows),
            timeout_seconds=180,
            build_timeout_seconds=600,
        )
    except LeanAxiomClosureError as exc:
        return [
            Finding(
                severity,
                interface_path,
                f"`{paper_id}` Lean axiom audit could not run for PaperInterface rows: {exc}",
            )
        ]
    approved_boundary_axioms = approved_boundary_axioms or set()
    approved_axioms = set(APPROVED_LEAN_AXIOMS)
    for name in approved_boundary_axioms:
        approved_axioms.add(name)
        approved_axioms.add(f"{paper_id}.{name}")
    findings: list[Finding] = []
    for name, qualified_name, line_no in rows:
        if qualified_name not in parsed:
            findings.append(
                Finding(
                    severity,
                    interface_path,
                    f"`{paper_id}` Lean axiom audit produced no `#print axioms` row for "
                    f"`{name}` at line {line_no}",
                )
            )
            continue
        unapproved = sorted(parsed[qualified_name] - approved_axioms)
        if not unapproved:
            continue
        findings.append(
            Finding(
                severity,
                interface_path,
                f"`{paper_id}` review row `{name}` at line {line_no} depends on "
                "unapproved Lean axiom(s): "
                + ", ".join(unapproved)
                + ". Only "
                + ", ".join(sorted(approved_axioms))
                + " are accepted as standard Lean/mathlib foundations or "
                "declared paper-local proof boundaries.",
            )
        )
    return findings


def paper_lean_files(folder: Path) -> list[Path]:
    """Return all paper-local Lean files, including the root import file."""

    files = [path for path in folder.rglob("*.lean") if path.is_file()]
    aggregator = PAPERS / f"{folder.name}.lean"
    if aggregator.exists():
        files.append(aggregator)
    return sorted(set(files))


def lean_declaration_index_from_source_bytes(
    source_bytes: Mapping[Path, bytes],
    *,
    library_modules: bool = False,
) -> dict[str, list[LeanDeclaration]]:
    """Index declarations from one caller-authenticated Lean source snapshot."""

    declarations: dict[str, list[LeanDeclaration]] = {}
    for path, content in sorted(source_bytes.items(), key=lambda item: str(item[0])):
        try:
            text = content.decode("utf-8")
        except UnicodeError:
            continue
        structure = _legacy_review_surface_structure_module()
        declaration_blocks = (
            structure.library_declaration_blocks(text)
            if library_modules
            else structure.review_declaration_blocks(text)
        )
        namespace_stacks = namespace_stacks_at_lines(
            text,
            {line for line, _kind, _source in declaration_blocks.values()},
        )
        for name, (line, kind, source) in declaration_blocks.items():
            declaration = LeanDeclaration(
                path=path, line=line, kind=kind, name=name, source=source
            )
            declarations.setdefault(name, []).append(declaration)
            namespaces = namespace_stacks.get(line, [])
            qualified_name = ".".join([*namespaces, name]) if namespaces else name
            if qualified_name != name:
                declarations.setdefault(qualified_name, []).append(declaration)
            if library_modules:
                try:
                    module_name = ".".join(path.relative_to(ROOT).with_suffix("").parts)
                except ValueError:
                    module_name = ""
                if module_name:
                    declarations.setdefault(f"{module_name}.{name}", []).append(
                        declaration
                    )
    return declarations


def paper_lean_declaration_index(folder: Path) -> dict[str, list[LeanDeclaration]]:
    """Index all paper-local files for non-transactional diagnostics.

    Canonical closeout does not call this ambient-folder scan. It uses
    :meth:`PaperCloseoutRunContext.paper_declaration_index`, whose source set is
    the exact Lean-owned import closure retained by the evidence transaction.
    """

    source_bytes: dict[Path, bytes] = {}
    for path in paper_lean_files(folder):
        try:
            source_bytes[path] = path.read_bytes()
        except OSError:
            continue
    return lean_declaration_index_from_source_bytes(source_bytes)


def library_lean_files() -> list[Path]:
    """Return reusable-library Lean files, excluding isolated regression modules."""

    files: set[Path] = set()
    root = ROOT / "AppliedModelingLib"
    if root.exists():
        files.update(path for path in root.rglob("*.lean") if path.is_file())
    try:
        tracked = git_ls_files()
    except subprocess.CalledProcessError:
        tracked = []
    for rel in tracked:
        path = ROOT / rel
        if path.suffix == ".lean" and path.exists() and path.relative_to(ROOT).parts[0] == "AppliedModelingLib":
            files.add(path)
    return sorted(path for path in files if not is_regression_fixture(path))


def library_lean_declaration_index() -> dict[str, list[LeanDeclaration]]:
    """Index reusable-library declarations by unqualified and module-qualified names."""

    source_bytes: dict[Path, bytes] = {}
    for path in library_lean_files():
        try:
            source_bytes[path] = path.read_bytes()
        except OSError:
            continue
    return lean_declaration_index_from_source_bytes(
        source_bytes,
        library_modules=True,
    )


def alias_target_name(source: str) -> str | None:
    """Return the first declaration name targeted by a thin `:= @foo` alias."""

    body = lean_code_text(declaration_body(source)).strip()
    match = re.fullmatch(
        r"@?\s*((?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*)",
        body,
    )
    if not match:
        return None
    return match.group(1)


def resolve_paper_local_target(
    declaration_index: dict[str, list[LeanDeclaration]], target_name: str | None
) -> list[LeanDeclaration]:
    """Resolve a possibly qualified target name against paper-local declarations."""

    if not target_name:
        return []
    unqualified = target_name.rsplit(".", 1)[-1]
    if target_name in declaration_index:
        return declaration_index[target_name]
    return declaration_index.get(unqualified, [])


def resolve_paper_local_alias_chain(
    declaration_index: dict[str, list[LeanDeclaration]], source: str, max_depth: int = 4
) -> list[LeanDeclaration]:
    """Follow thin local aliases far enough to inspect their real signatures."""

    seen: set[tuple[Path, int, str]] = set()
    resolved: list[LeanDeclaration] = []

    def visit(target_name: str | None, depth: int) -> None:
        if depth <= 0:
            return
        for declaration in resolve_paper_local_target(declaration_index, target_name):
            key = (declaration.path, declaration.line, declaration.name)
            if key in seen:
                continue
            seen.add(key)
            resolved.append(declaration)
            if declaration.kind in {"abbrev", "def"}:
                visit(alias_target_name(declaration.source), depth - 1)

    visit(alias_target_name(source), max_depth)
    return resolved


def is_thin_review_alias_to_proved_theorem(
    declaration_index: dict[str, list[LeanDeclaration]], declaration: LeanDeclaration
) -> bool:
    """Accept only a transparent review alias whose target chain reaches a proof.

    A source-facing `abbrev review_row := @proved_row` carries no new theorem
    premise or conclusion: Lean elaborates the exact target type.  Treating it
    as proof evidence is sound only when the body is the thin alias parsed by
    `alias_target_name` and its paper-local target chain reaches a theorem or
    lemma.  In particular, arbitrary Prop-valued definitions are not accepted.
    """

    if declaration.kind != "abbrev" or alias_target_name(declaration.source) is None:
        return False
    return any(
        target.kind in {"theorem", "lemma"}
        for target in resolve_paper_local_alias_chain(declaration_index, declaration.source)
    )


def assumption_finding_severity(strict_assumption_policy: bool, status: object) -> str:
    """Completed papers should not hide proof-boundary premises."""

    if status not in {"formalized", "formalized with caveat", "partially formalized", "conditional"}:
        return "WARN"
    if strict_assumption_policy:
        return "ERROR"
    return "ERROR"


def completed_status_finding_severity(status: object) -> str:
    """Completed paper claims should satisfy the strict review-surface checks."""

    if status in {"formalized", "formalized with caveat", "partially formalized", "conditional"}:
        return "ERROR"
    return "WARN"


def strict_review_items_for_paper(
    folder: Path,
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    audit_inputs: object | None = None,
    validated_configured_review_rows: tuple[Mapping[str, object], ...] | None = None,
    semantic_reuse_authority: object | None = None,
) -> tuple[Any, ...]:
    """Build one signature-current dashboard surface for an audit."""

    from scripts.review_dashboard import review_items_for_paper

    kwargs: dict[str, object] = {}
    if validated_configured_review_rows is not None:
        kwargs["validated_configured_review_rows"] = (
            validated_configured_review_rows
        )
    if semantic_reuse_authority is not None:
        kwargs["semantic_reuse_authority"] = semantic_reuse_authority
    return tuple(
        review_items_for_paper(
            folder,
            use_cache=True,
            render_images=False,
            require_current_signatures=True,
            persist_cache_rebind=False,
            build_input_provider=build_input_provider,
            audit_inputs=audit_inputs,
            **kwargs,
        )
    )


class LazyStrictReviewItems:
    """Memoize one strict dashboard extraction, including a failed attempt."""

    def __init__(
        self,
        folder: Path,
        *,
        build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
        audit_inputs: object | None = None,
        validated_configured_review_rows: (
            tuple[Mapping[str, object], ...] | None
        ) = None,
        semantic_reuse_authority: object | None = None,
    ) -> None:
        self.folder = folder
        self.build_input_provider = build_input_provider
        self.audit_inputs = audit_inputs
        self.validated_configured_review_rows = validated_configured_review_rows
        self.semantic_reuse_authority = semantic_reuse_authority
        self._attempted = False
        self._items: tuple[Any, ...] = ()
        self._error: Exception | None = None

    def __call__(self) -> tuple[Any, ...]:
        if not self._attempted:
            self._attempted = True
            try:
                kwargs: dict[str, object] = {}
                if self.validated_configured_review_rows is not None:
                    kwargs["validated_configured_review_rows"] = (
                        self.validated_configured_review_rows
                    )
                if self.semantic_reuse_authority is not None:
                    kwargs["semantic_reuse_authority"] = (
                        self.semantic_reuse_authority
                    )
                self._items = strict_review_items_for_paper(
                    self.folder,
                    build_input_provider=self.build_input_provider,
                    audit_inputs=self.audit_inputs,
                    **kwargs,
                )
            except Exception as exc:  # noqa: BLE001 - consumers report audit failures.
                self._error = exc
        if self._error is not None:
            raise self._error
        return self._items


def exact_evidence_run_context(value: object) -> bool:
    """Accept only a builder-issued context from this module's import identity."""

    from scripts.audit_evidence_integrity import EvidenceRunContext
    return isinstance(value, EvidenceRunContext) and value.issued_by_builder


def _legacy_source_record_state(value: object) -> object | None:
    """Return only the explicitly acquired legacy lane from an exact context."""

    return getattr(value, "legacy_source_record_state", None)


def _legacy_source_record_inputs(value: object) -> object | None:
    state = _legacy_source_record_state(value)
    return getattr(state, "inputs", None)


def _legacy_source_record_audit_payload(value: object) -> object | None:
    inputs = _legacy_source_record_inputs(value)
    snapshot = getattr(inputs, "audit_snapshot", None)
    return getattr(snapshot, "payload", None)


class _PaperCloseoutRunContextIssuerBinding:
    """Object-identity capability minted only by the closeout context factory."""

    __slots__ = ("context",)

    def __init__(self) -> None:
        self.context: PaperCloseoutRunContext | None = None


class _StrictV11SourceRecordJudgmentHandoffCapability:
    """Unserializable marker staged only by a successful primary source gate."""

    __slots__ = ()


class _SemanticContractExecutableTerminalReceiptIssuerCapability:
    """Private capability held only by the terminal-policy issuer."""

    __slots__ = ()


_SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_RECEIPT_ISSUER = (
    _SemanticContractExecutableTerminalReceiptIssuerCapability()
)


class _SemanticContractCloseoutBridgeIssuerCapability:
    """Private capability held only by the complete contract validator."""

    __slots__ = ()


_SEMANTIC_CONTRACT_CLOSEOUT_BRIDGE_ISSUER = (
    _SemanticContractCloseoutBridgeIssuerCapability()
)


class _RecursiveFieldExplicitParentReceiptIssuerCapability:
    """Private capability held only by the scoped-field receipt projector."""

    __slots__ = ()


_RECURSIVE_FIELD_EXPLICIT_PARENT_RECEIPT_ISSUER = (
    _RecursiveFieldExplicitParentReceiptIssuerCapability()
)


class PaperCloseoutRunContext:
    """One single-paper closeout transaction backed by exact evidence bytes.

    This object is only an in-process projection of ``EvidenceRunContext``. It
    does not mint independent authorization and it never persists a cache. The
    evidence context owns source-record currentness, immutable parsed payloads,
    and the final producer/source mutation check used by every closeout lane.
    """

    _MAX_ENTRIES = 16

    @classmethod
    def from_exact_evidence_context(
        cls,
        paper_id: str,
        folder: Path,
        *,
        evidence_context: object,
    ) -> PaperCloseoutRunContext:
        """Mint the only context form that can authorize a closeout bridge.

        A direct constructor remains available for diagnostic helpers and
        legacy callers, but it is deliberately not an authorization token.
        Requiring both this object-identity capability and the independently
        issued evidence transaction prevents a caller from wrapping a stale
        context and presenting it as a fresh terminal-policy run.
        """

        if not exact_evidence_run_context(evidence_context):
            raise ValueError(
                "paper closeout context requires a builder-issued evidence transaction"
            )
        binding = _PaperCloseoutRunContextIssuerBinding()
        context = cls(
            paper_id,
            folder,
            evidence_context=evidence_context,
        )
        context._issuer_binding = binding
        binding.context = context
        return context

    def __init__(
        self,
        paper_id: str,
        folder: Path,
        *,
        evidence_context: object | None = None,
    ) -> None:
        self.paper_id = paper_id
        self.folder = folder.resolve()
        self.evidence_context = evidence_context
        self._issuer_binding: object | None = None
        if evidence_context is not None:
            context_folder = getattr(evidence_context, "folder", None)
            if (
                not exact_evidence_run_context(evidence_context)
                or
                not isinstance(context_folder, Path)
                or context_folder != self.folder
            ):
                raise ValueError(
                    "paper closeout context does not match its evidence transaction"
                )
        self._cache: dict[tuple[object, ...], object] = {}
        # A strict source-to-Spec closure is expensive Lean evidence.  Keep
        # its successful runtime receipts inside this one exact closeout
        # transaction so the occurrence gate can consume the same evidence
        # without running a second closure extraction.
        self._strict_source_spec_correspondence_receipts: set[
            StrictSourceSpecCorrespondenceReceipt
        ] = set()
        self._strict_source_spec_correspondence_scope_keys: frozenset[str] = (
            frozenset()
        )
        # Direct formula contracts that terminate in executable model code use
        # a different, narrower route than atom-complete source-to-Spec
        # correspondence.  Retain only per-occurrence runtime receipts issued
        # by the exact terminal-policy check so the strict realization gate can
        # consume them without treating a formula as a named-source closure.
        self._semantic_contract_executable_terminal_component_receipts: set[
            SemanticContractExecutableTerminalComponentReceipt
        ] = set()
        # The statement-map declaration gate and the legacy-sidecar bridge
        # consume the same complete semantic-contract validation.  Retain its
        # successful source-item scope only inside this exact transaction so
        # the second consumer does not rerun the same Lean/source proof.
        self._semantic_contract_closeout_bridge_scope_keys: frozenset[str] = (
            frozenset()
        )
        # Explicit source-model field scopes are reviewed as direct primitives,
        # but their route metadata is not a component contract.  Store only
        # transaction-minted occurrence receipts after the exact parent
        # semantic review and field target disposition have both passed.
        self._recursive_field_explicit_parent_component_receipts: set[
            RecursiveFieldExplicitParentComponentReceipt
        ] = set()
        # A strict full-Spec source-record pass is first staged by
        # `check_source_record_audit`.  The closeout owner publishes it only
        # after every primary paper check has returned without an error.
        self._strict_v11_source_record_judgment_handoff: (
            _StrictV11SourceRecordJudgmentHandoffCapability | None
        ) = None
        legacy_state = getattr(
            evidence_context, "legacy_source_record_state", None
        )
        legacy_inputs = getattr(legacy_state, "inputs", None)
        legacy_audit_snapshot = getattr(legacy_inputs, "audit_snapshot", None)
        audit_payload = getattr(legacy_audit_snapshot, "payload", None)
        lean_import_closure_payload = (
            audit_payload.get(SOURCE_RECORD_LEAN_IMPORT_CLOSURE_FIELD)
            if isinstance(audit_payload, Mapping)
            else None
        )
        transaction_skew = (
            paper_closeout_source_record_transaction_skew_findings(
                paper_id,
                evidence_context,
            )
            if evidence_context is not None
            else []
        )
        if transaction_skew:
            self.v11_direct_semantic_review_current = False
            self.v11_direct_semantic_review_error = transaction_skew[0].message
        else:
            (
                self.v11_direct_semantic_review_current,
                self.v11_direct_semantic_review_error,
            ) = paper_closeout_v11_direct_semantic_review_state(
                paper_id,
                folder,
                evidence_context,
            )
        self.v11_lean_claim_graph_selected = bool(
            getattr(evidence_context, "v11_lean_claim_graph_selected", False)
            or self.v11_direct_semantic_review_current
        )
        self.v11_lean_review_surface: object | None = None
        if self.v11_lean_claim_graph_selected:
            # The selected v11 lane builds one exact Lean graph before it can
            # decide whether every saved semantic judgment is current.  Keep
            # that graph even when a judgment fails: downstream structural
            # checks must expose the real v11 finding, not discard Lean's
            # authenticated source ownership and fall into the retired raw
            # source-record transport.
            self.v11_lean_review_surface = paper_closeout_v11_lean_review_surface(
                folder,
                evidence_context,
            )
            if (
                self.v11_direct_semantic_review_current
                and self.v11_lean_review_surface is None
            ):
                self.v11_direct_semantic_review_current = False
                self.v11_direct_semantic_review_error = (
                    "v11 semantic gate did not retain its Lean review graph"
                )
        provider_kwargs: dict[str, object] = {}
        semantic_reuse_authority = getattr(
            legacy_state, "semantic_reuse_authority", None
        )
        if semantic_reuse_authority is not None:
            provider_kwargs["lean_import_closure_payload"] = (
                lean_import_closure_payload
            )
            provider_kwargs["semantic_reuse_authority"] = semantic_reuse_authority
        elif not self.v11_lean_claim_graph_selected:
            provider_kwargs["lean_import_closure_payload"] = (
                lean_import_closure_payload
            )
        shared_provider = getattr(
            self.v11_lean_review_surface, "build_input_provider", None
        )
        self.build_input_provider = (
            shared_provider
            if shared_provider is not None
            else (
                None
                if self.v11_lean_claim_graph_selected
                else RepositoryBuildInputSnapshotProvider(ROOT, **provider_kwargs)
            )
        )

    @property
    def issued_by_builder(self) -> bool:
        """Whether the closeout factory minted this exact transaction wrapper."""

        binding = self._issuer_binding
        return (
            isinstance(binding, _PaperCloseoutRunContextIssuerBinding)
            and binding.context is self
            and exact_evidence_run_context(self.evidence_context)
        )

    @property
    def selected_v11_closeout(self) -> bool:
        """Whether this exact closeout is owned by the retained v11 graph."""

        return self.issued_by_builder and self.v11_lean_claim_graph_selected

    @property
    def current_v11_closeout(self) -> bool:
        """Whether the selected v11 graph and all semantic leaves are current."""

        return self.selected_v11_closeout and self.v11_direct_semantic_review_current

    def record_strict_source_spec_correspondence_receipt(
        self,
        receipt: StrictSourceSpecCorrespondenceReceipt,
    ) -> None:
        """Retain one current source-to-Spec closure result for this run only."""

        if isinstance(receipt, StrictSourceSpecCorrespondenceReceipt):
            self._strict_source_spec_correspondence_receipts.add(receipt)

    def record_strict_source_spec_correspondence_scope_keys(
        self,
        source_item_keys: object,
    ) -> None:
        """Retain the inventory scope that issued this run's receipts."""

        if not isinstance(source_item_keys, (tuple, list, set, frozenset)):
            return
        keys = frozenset(
            str(value).strip()
            for value in source_item_keys
            if isinstance(value, str) and value.strip()
        )
        if keys:
            self._strict_source_spec_correspondence_scope_keys = keys

    def current_strict_source_spec_correspondence_scope_keys(self) -> tuple[str, ...]:
        """Return the exact source-inventory scope that minted these receipts."""

        return tuple(sorted(self._strict_source_spec_correspondence_scope_keys))

    def current_strict_source_spec_correspondence_receipts(
        self,
    ) -> tuple[StrictSourceSpecCorrespondenceReceipt, ...]:
        """Return deterministic current closure receipts minted in this run."""

        return tuple(
            sorted(
                self._strict_source_spec_correspondence_receipts,
                key=lambda receipt: (
                    receipt.source_item_key,
                    receipt.spec_declaration,
                    receipt.evidence_declaration,
                    receipt.item_identity_sha256,
                ),
            )
        )

    def record_semantic_contract_closeout_bridge(
        self,
        source_item_keys: object,
        *,
        _issuer: object | None = None,
    ) -> None:
        """Retain one complete contract pass for this exact transaction."""

        if (
            not self.issued_by_builder
            or _issuer is not _SEMANTIC_CONTRACT_CLOSEOUT_BRIDGE_ISSUER
            or not isinstance(source_item_keys, (tuple, list, set, frozenset))
        ):
            return
        keys = frozenset(
            str(value).strip()
            for value in source_item_keys
            if isinstance(value, str) and value.strip()
        )
        if keys:
            self._semantic_contract_closeout_bridge_scope_keys = keys

    def current_semantic_contract_closeout_bridge_scope_keys(self) -> tuple[str, ...]:
        """Return a complete contract scope proven earlier in this run."""

        if not self.issued_by_builder:
            return ()
        return tuple(sorted(self._semantic_contract_closeout_bridge_scope_keys))

    def record_semantic_contract_executable_terminal_component_receipts(
        self,
        receipts: object,
        *,
        _issuer: object | None = None,
    ) -> None:
        """Retain exact terminal-policy component receipts for this run only."""

        if (
            not self.issued_by_builder
            or _issuer is not _SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_RECEIPT_ISSUER
            or not isinstance(
                receipts, (tuple, list, set, frozenset)
            )
        ):
            return
        if not all(
            isinstance(receipt, SemanticContractExecutableTerminalComponentReceipt)
            for receipt in receipts
        ):
            return
        self._semantic_contract_executable_terminal_component_receipts.update(receipts)

    def current_semantic_contract_executable_terminal_component_receipts(
        self,
    ) -> tuple[SemanticContractExecutableTerminalComponentReceipt, ...]:
        """Return deterministic terminal-policy receipts minted in this run."""

        return tuple(
            sorted(
                self._semantic_contract_executable_terminal_component_receipts,
                key=lambda receipt: (
                    receipt.source_item_key,
                    receipt.spec_declaration,
                    receipt.component_key,
                    receipt.component_sha256,
                ),
            )
        )

    def record_recursive_field_explicit_parent_component_receipts(
        self,
        receipts: object,
        *,
        _issuer: object | None = None,
    ) -> None:
        """Retain exact scoped-field receipts issued in this transaction only."""

        if (
            not self.issued_by_builder
            or _issuer is not _RECURSIVE_FIELD_EXPLICIT_PARENT_RECEIPT_ISSUER
            or not isinstance(receipts, (tuple, list, set, frozenset))
            or not all(
                isinstance(receipt, RecursiveFieldExplicitParentComponentReceipt)
                for receipt in receipts
            )
        ):
            return
        self._recursive_field_explicit_parent_component_receipts.update(receipts)

    def current_recursive_field_explicit_parent_component_receipts(
        self,
    ) -> tuple[RecursiveFieldExplicitParentComponentReceipt, ...]:
        """Return deterministic current scoped-field receipts from this run."""

        return tuple(
            sorted(
                self._recursive_field_explicit_parent_component_receipts,
                key=lambda receipt: (
                    receipt.source_item_key,
                    receipt.parent_qualified_declaration,
                    receipt.component_key,
                    receipt.component_sha256,
                ),
            )
        )

    def stage_strict_v11_source_record_judgment_handoff(self) -> None:
        """Stage a no-argument bridge after the strict source gate succeeds."""

        if self.issued_by_builder:
            self._strict_v11_source_record_judgment_handoff = (
                _StrictV11SourceRecordJudgmentHandoffCapability()
            )

    def publish_staged_strict_v11_source_record_judgment_handoff(self) -> bool:
        """Publish the staged pass only to this exact evidence transaction."""

        capability = self._strict_v11_source_record_judgment_handoff
        self._strict_v11_source_record_judgment_handoff = None
        if (
            not isinstance(
                capability, _StrictV11SourceRecordJudgmentHandoffCapability
            )
            or not self.issued_by_builder
        ):
            return False
        from scripts.audit_evidence_integrity import (
            _issue_primary_closeout_source_record_judgment_receipt,
        )

        return _issue_primary_closeout_source_record_judgment_receipt(
            self.evidence_context
        )

    def _memoized(
        self,
        key: tuple[object, ...],
        producer: Callable[[], object],
    ) -> object:
        if self.evidence_context is None:
            # Without the exact transaction there is no complete mutation
            # boundary under which a derived authorization can be shared.
            return producer()
        if key in self._cache:
            return self._cache[key]
        value = producer()
        if len(self._cache) < self._MAX_ENTRIES:
            self._cache[key] = value
        return value

    @staticmethod
    def _payload_identity(payload: Mapping[str, object]) -> tuple[object, ...]:
        aggregate = str(payload.get("source_record_audit_sha256") or "").strip()
        integrity = str(
            payload.get("source_record_audit_integrity_sha256") or ""
        ).strip()
        if re.fullmatch(r"[0-9a-f]{64}", aggregate) and re.fullmatch(
            r"[0-9a-f]{64}", integrity
        ):
            return aggregate, integrity
        # An unpinned fixture/legacy object may be reused only by identity in
        # this process; it cannot collide with a different serialized payload.
        return ("object", id(payload))

    def corrected_scope_evaluation(
        self,
        status_payload: dict[str, object],
    ) -> tuple[bool, Exception | None]:
        status_identity = hashlib.sha256(
            json.dumps(
                status_payload,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=True,
            ).encode("utf-8")
        ).hexdigest()
        evidence_status = getattr(self.evidence_context, "status_payload", None)
        if isinstance(evidence_status, dict) and dict(evidence_status) == status_payload:
            return bool(
                getattr(self.evidence_context, "corrected_scope_current", False)
            ), None
        if self.evidence_context is not None:
            return (
                False,
                ValueError(
                    "corrected-scope request does not match the exact closeout status"
                ),
            )

        def evaluate() -> tuple[bool, Exception | None]:
            try:
                return (
                    evaluate_author_approved_corrected_scope(
                        self.folder, status_payload
                    ),
                    None,
                )
            except Exception as exc:  # noqa: BLE001 - consumers preserve failure policy.
                return False, exc

        value = self._memoized(
            ("corrected_scope_current", status_identity),
            evaluate,
        )
        assert isinstance(value, tuple) and len(value) == 2
        current, error = value
        return bool(current), error if isinstance(error, Exception) else None

    def corrected_scope_current(
        self,
        status_payload: dict[str, object],
        *,
        raise_on_error: bool = False,
    ) -> bool:
        current, error = self.corrected_scope_evaluation(status_payload)
        if error is not None and raise_on_error:
            raise error
        return current

    def current_source_record_audit(
        self,
    ) -> tuple[dict[str, object] | None, str]:
        legacy_state = getattr(
            self.evidence_context, "legacy_source_record_state", None
        )
        legacy_inputs = getattr(legacy_state, "inputs", None)
        audit_snapshot = getattr(legacy_inputs, "audit_snapshot", None)
        evidence_payload = getattr(audit_snapshot, "payload", None)
        identity_error = str(
            getattr(legacy_state, "source_record_identity_error", "") or ""
        )
        if isinstance(evidence_payload, dict) and not identity_error:
            return evidence_payload, ""
        if self.evidence_context is not None:
            return (
                None,
                "exact closeout source-record snapshot is not current"
                + (f": {identity_error}" if identity_error else ""),
            )

        def load_or_refresh() -> tuple[dict[str, object] | None, str]:
            canonical_path = self.folder / DEFAULT_SOURCE_RECORD_AUDIT_FILE
            saved = self.saved_source_record_audit(canonical_path)
            current = current_saved_source_record_audit(
                self.paper_id,
                payload=saved,
            )
            if current is not None:
                return current, ""
            return run_source_record_audit_helper(self.paper_id)

        value = self._memoized(
            ("current_source_record_audit",),
            load_or_refresh,
        )
        assert isinstance(value, tuple) and len(value) == 2
        payload, error = value
        return payload if isinstance(payload, dict) else None, str(error)

    def current_configured_review_rows_for_manifest_reuse(
        self,
    ) -> tuple[Mapping[str, object], ...] | None:
        """Return raw rows only from this exact validated closeout snapshot.

        The source-record producer cannot use its own saved rows as cache
        authority. This projection is available only after the independently
        issued evidence transaction has established the raw receipt's current
        source fingerprint, scan completeness, and serialized integrity.
        """

        if self.evidence_context is None:
            return None
        payload, error = self.current_source_record_audit()
        if payload is None or error or payload.get("paper") != self.paper_id:
            return None
        raw_rows = payload.get("configured_review_rows")
        if (
            not isinstance(raw_rows, list)
            or payload.get("configured_review_rows_count") != len(raw_rows)
            or payload.get("missing_configured_review_rows") != []
            or any(not isinstance(row, Mapping) for row in raw_rows)
        ):
            return None
        return tuple(dict(row) for row in raw_rows if isinstance(row, Mapping))

    def saved_source_record_audit(self, path: Path) -> dict[str, object] | None:
        legacy_state = getattr(
            self.evidence_context, "legacy_source_record_state", None
        )
        legacy_inputs = getattr(legacy_state, "inputs", None)
        audit_snapshot = getattr(legacy_inputs, "audit_snapshot", None)
        snapshot_path = getattr(audit_snapshot, "path", None)
        snapshot_payload = getattr(audit_snapshot, "payload", None)
        if (
            isinstance(snapshot_path, Path)
            and snapshot_path.resolve() == path.resolve()
            and isinstance(snapshot_payload, dict)
        ):
            return snapshot_payload
        if self.evidence_context is not None:
            return None
        value = self._memoized(
            ("saved_source_record_audit", str(path.resolve())),
            lambda: load_json_object(path),
        )
        return value if isinstance(value, dict) else None

    def exact_json_payload(self, path: Path) -> dict[str, object] | None:
        """Return a JSON authority input from the transaction's exact bytes.

        A closeout transaction must not re-read status, map, judgment, or
        fidelity inputs after currentness was established. Start/end hashes
        reject ordinary drift but cannot detect an ABA replacement used only
        for one intermediate live read. Only payloads parsed by the evidence
        snapshot builder are therefore available through this method.
        """

        if self.evidence_context is not None:
            snapshots = getattr(self.evidence_context, "input_snapshots", ())
            for snapshot in snapshots:
                snapshot_path = getattr(snapshot, "path", None)
                snapshot_payload = getattr(snapshot, "payload", None)
                if (
                    isinstance(snapshot_path, Path)
                    and snapshot_path.resolve() == path.resolve()
                    and isinstance(snapshot_payload, dict)
                ):
                    return snapshot_payload
            return None
        value = self._memoized(
            ("exact_json_payload", str(path.resolve())),
            lambda: load_json_object(path),
        )
        return value if isinstance(value, dict) else None

    def exact_lean_source_text(self, path: Path) -> str | None:
        """Return one Lean source from the transaction-owned import closure.

        Canonical closeout consumers must never parse a live replacement after
        the source-record receipt and Lean graph were validated.  A context
        without an evidence transaction remains a nonauthoritative diagnostic
        helper and may read the requested file directly.
        """

        resolved = path.resolve()

        def load() -> str | None:
            if self.evidence_context is not None:
                content = self.lean_owned_source_snapshots().get(resolved)
                if content is None:
                    return None
            else:
                try:
                    content = resolved.read_bytes()
                except OSError:
                    return None
            try:
                return content.decode("utf-8")
            except UnicodeError:
                return None

        value = self._memoized(("lean_source_text", str(resolved)), load)
        return value if isinstance(value, str) else None

    def exact_source_proof_fidelity_input(
        self,
    ) -> tuple[Path | None, dict[str, object] | None]:
        """Return the evidence builder's exact fidelity-ledger path and payload."""

        snapshot = getattr(
            self.evidence_context, "source_proof_fidelity_snapshot", None
        )
        if self.evidence_context is not None:
            path = getattr(snapshot, "path", None)
            payload = getattr(snapshot, "payload", None)
            return (
                path if isinstance(path, Path) else None,
                payload if isinstance(payload, dict) else None,
            )

        status_payload = self.exact_json_payload(self.folder / "status.json") or {}
        path = configured_source_proof_fidelity_path(self.folder, status_payload)
        return path, self.exact_json_payload(path) if path is not None else None

    def dashboard_audit_inputs(self) -> object | None:
        """Build the historical dashboard bundle from transaction-owned bytes.

        A selected v11 closeout is validated from its typed Lean claim graph
        and exact configured source artifacts. It must never reconstruct a
        second semantic surface from dashboard conventions or legacy aliases.
        """

        if self.evidence_context is None or self.selected_v11_closeout:
            return None

        def build() -> object:
            from scripts.dashboard_audit_inputs import DashboardAuditInputs

            snapshots: dict[Path, bytes | None] = {}
            for snapshot in getattr(self.evidence_context, "input_snapshots", ()):
                path = getattr(snapshot, "path", None)
                raw_bytes = getattr(snapshot, "raw_bytes", None)
                sha256 = getattr(snapshot, "sha256", None)
                if not isinstance(path, Path):
                    continue
                if raw_bytes is None and sha256 is not None:
                    raise ValueError(
                        f"exact dashboard input bytes are unavailable: {path}"
                    )
                if raw_bytes is not None and not isinstance(raw_bytes, bytes):
                    raise ValueError(
                        f"exact dashboard input bytes are malformed: {path}"
                    )
                snapshots[path.resolve()] = raw_bytes
            for path, content in self.lean_owned_source_snapshots().items():
                resolved = path.resolve()
                if resolved in snapshots and snapshots[resolved] != content:
                    raise ValueError(
                        f"Lean graph and evidence snapshots disagree: {resolved}"
                    )
                snapshots[resolved] = content
            return DashboardAuditInputs.from_file_snapshots(ROOT, snapshots)

        return self._memoized(("dashboard_audit_inputs",), build)

    def source_record_judgments(
        self,
        path: Path,
        payload: dict[str, object],
    ) -> Mapping[str, dict[str, object]]:
        legacy_state = getattr(
            self.evidence_context, "legacy_source_record_state", None
        )
        legacy_inputs = getattr(legacy_state, "inputs", None)
        audit_snapshot = getattr(legacy_inputs, "audit_snapshot", None)
        match_snapshot = getattr(legacy_inputs, "match_snapshot", None)
        audit_payload = getattr(audit_snapshot, "payload", None)
        match_path = getattr(match_snapshot, "path", None)
        current_judgments = getattr(
            legacy_state, "current_source_record_judgments", None
        )
        if (
            payload is audit_payload
            and isinstance(match_path, Path)
            and match_path.resolve() == path.resolve()
            and isinstance(current_judgments, Mapping)
        ):
            return current_judgments
        if self.evidence_context is not None:
            return {}
        value = self._memoized(
            (
                "source_record_judgments",
                str(path.resolve()),
                *self._payload_identity(payload),
            ),
            lambda: source_record_judgment_items(
                path,
                self.paper_id,
                current_raw_audit=payload,
                paper_dir=self.folder,
            ),
        )
        assert isinstance(value, Mapping)
        return value

    def cached_result(
        self,
        name: str,
        identity: tuple[object, ...],
        producer: Callable[[], object],
    ) -> object:
        """Memoize one derived result under an explicit structural identity."""

        return self._memoized(("derived", name, *identity), producer)

    def _lean_owned_source_snapshots(self) -> dict[Path, bytes]:
        """Return exact repository Lean bytes owned by the selected protocol.

        V11 consumes the retained Lean graph's exact module sources. The legacy
        source-record lane consumes the source set obtained from Lean's loaded
        module graph and bound into that protocol's receipt. Neither route
        widens its source set with a directory scan. The evidence transaction's
        final mutation check remains the publication boundary.
        """

        if self.evidence_context is None:
            return {
                path: path.read_bytes()
                for path in paper_lean_files(self.folder)
                if path.is_file()
            }

        # The current v11 lane already constructs one Lean-owned declaration
        # graph from the standalone import-closure receipt and retains the
        # exact module bytes used to elaborate it.  Consume those bytes
        # directly.  Falling through to the historical raw source-record
        # fingerprint would make an intentionally superseded transport a
        # prerequisite for dashboards and closeout, and would also parse a
        # second, weaker ownership description after the v11 graph passed.
        if self.v11_lean_claim_graph_selected:
            raw_module_sources = getattr(
                self.v11_lean_review_surface, "module_sources", None
            )
            if not isinstance(raw_module_sources, Mapping) or not raw_module_sources:
                raise ValueError(
                    "selected v11 Lean review graph has no exact module sources: "
                    + (
                        self.v11_direct_semantic_review_error
                        or "the exact graph was not retained"
                    )
                )
            root = ROOT.resolve()
            snapshots: dict[Path, bytes] = {}
            for module, raw_source in raw_module_sources.items():
                if (
                    not isinstance(module, str)
                    or not module.strip()
                    or not isinstance(raw_source, tuple)
                    or len(raw_source) != 2
                ):
                    raise ValueError(
                        "current v11 Lean review graph has a malformed module source"
                    )
                raw_path, content = raw_source
                if not isinstance(raw_path, Path) or not isinstance(content, bytes):
                    raise ValueError(
                        "current v11 Lean review graph has malformed source bytes"
                    )
                try:
                    path = raw_path.resolve()
                    path.relative_to(root)
                except (OSError, RuntimeError, ValueError) as exc:
                    raise ValueError(
                        "current v11 Lean review graph source escapes the repository"
                    ) from exc
                if path.suffix != ".lean":
                    raise ValueError(
                        "current v11 Lean review graph contains a non-Lean source"
                    )
                prior = snapshots.get(path)
                if prior is not None and prior != content:
                    raise ValueError(
                        "current v11 Lean review graph assigns conflicting bytes to one source"
                    )
                snapshots[path] = content
            interface = (self.folder / "PaperInterface.lean").resolve()
            if interface not in snapshots:
                raise ValueError(
                    "current v11 Lean review graph omits PaperInterface.lean"
                )
            return snapshots

        audit_payload = _legacy_source_record_audit_payload(
            self.evidence_context
        )
        closure_payload = (
            audit_payload.get(SOURCE_RECORD_LEAN_IMPORT_CLOSURE_FIELD)
            if isinstance(audit_payload, Mapping)
            else None
        )
        if isinstance(closure_payload, Mapping):
            entry_module = str(closure_payload.get("entry_module") or "").strip()
            entrypoint = str(closure_payload.get("entrypoint") or "").strip()
            source_snapshot = self.build_input_provider.repository_source_snapshot(
                entry_module
            )
            if not entry_module or not entrypoint or not source_snapshot:
                raise ValueError(
                    "exact closeout source record has no usable Lean import closure"
                )
            snapshots = {
                path.resolve(): content
                for _module, path, content, _digest in source_snapshot
            }
            interface = (ROOT / entrypoint).resolve()
            if interface not in snapshots:
                raise ValueError(
                    "Lean import closure omits its configured review interface"
                )
            return snapshots

        # Exact legacy receipts predate the top-level Lean graph handoff. They
        # retain their byte-pinned dependency list for the compatibility
        # window; current schema receipts always take the provider route above.
        fingerprint = (
            audit_payload.get("source_record_input_fingerprint")
            if isinstance(audit_payload, Mapping)
            else None
        )
        raw_identities = (
            fingerprint.get("lean_dependency_identities")
            if isinstance(fingerprint, Mapping)
            else None
        )
        if not isinstance(raw_identities, list):
            raise ValueError(
                "exact closeout source record has no Lean-owned dependency identities"
            )

        root = ROOT.resolve()
        snapshots: dict[Path, bytes] = {}
        for raw in raw_identities:
            if not isinstance(raw, Mapping) or raw.get("status") != "present":
                continue
            relative = raw.get("path")
            expected = str(raw.get("sha256") or "").strip().lower()
            if not isinstance(relative, str) or not re.fullmatch(
                r"[0-9a-f]{64}", expected
            ):
                raise ValueError("Lean-owned dependency identity is malformed")
            candidate = Path(relative)
            try:
                if candidate.is_absolute():
                    raise ValueError
                path = (root / candidate).resolve()
                path.relative_to(root)
            except (OSError, RuntimeError, ValueError) as exc:
                raise ValueError(
                    "Lean-owned dependency path escapes the repository"
                ) from exc
            if path.suffix != ".lean":
                continue
            try:
                content = path.read_bytes()
            except OSError as exc:
                raise ValueError(
                    f"Lean-owned dependency source is unavailable: {relative}"
                ) from exc
            if hashlib.sha256(content).hexdigest() != expected:
                raise ValueError(
                    f"Lean-owned dependency source changed: {relative}"
                )
            snapshots[path] = content

        interface = (self.folder / "PaperInterface.lean").resolve()
        if interface not in snapshots:
            raise ValueError(
                "Lean-owned dependency closure omits the configured PaperInterface.lean"
            )
        return snapshots

    def lean_owned_source_snapshots(self) -> dict[Path, bytes]:
        """Memoize the exact Lean-owned byte snapshot for all closeout consumers."""

        value = self._memoized(
            ("lean_owned_source_snapshots",),
            self._lean_owned_source_snapshots,
        )
        assert isinstance(value, dict)
        return value

    def paper_declaration_index(self) -> dict[str, list[LeanDeclaration]]:
        """Return one memoized paper-local index from the exact loaded closure."""

        if self.evidence_context is None:
            return paper_lean_declaration_index(self.folder)

        def build() -> dict[str, list[LeanDeclaration]]:
            snapshots = self.lean_owned_source_snapshots()
            paper_root = self.folder.resolve()
            paper_sources = {
                path: content
                for path, content in snapshots.items()
                if path == (PAPERS / f"{self.paper_id}.lean").resolve()
                or paper_root in path.parents
            }
            if self.v11_lean_claim_graph_selected:
                payload = getattr(
                    self.v11_lean_review_surface, "declaration_inventory", None
                )
                module_sources = getattr(
                    self.v11_lean_review_surface, "module_sources", None
                )
                if isinstance(payload, Mapping) and isinstance(
                    module_sources, Mapping
                ):
                    declarations = lean_declaration_index_from_inventory(
                        payload, module_sources
                    )
                    if declarations:
                        return declarations
                raise ValueError(
                    "selected v11 Lean review graph has no usable paper declaration inventory"
                )
            return lean_declaration_index_from_source_bytes(paper_sources)

        value = self._memoized(("paper_declaration_index",), build)
        assert isinstance(value, dict)
        return value

    def current_v11_primary_gate_result(self) -> CurrentV11PrimaryGateResult:
        """Return the one parser-free core gate for this exact v11 transaction."""

        if not self.selected_v11_closeout or self.evidence_context is None:
            raise ValueError(
                "current v11 primary gate requires its builder-issued transaction"
            )
        return current_v11_primary_gate_result(
            ROOT,
            self.folder,
            context=self.evidence_context,
        )

    def evaluate_and_accept_current_v11_primary_gate(self) -> tuple[object, object]:
        """Return the exact current verdict and its nominal acceptance object."""

        if not self.selected_v11_closeout or self.evidence_context is None:
            raise ValueError(
                "current v11 primary gate requires its builder-issued transaction"
            )
        return evaluate_and_accept_current_v11_primary_gate(
            ROOT,
            self.folder,
            context=self.evidence_context,
        )

    def library_declaration_index(self) -> dict[str, list[LeanDeclaration]]:
        """Return imported reusable-library declarations from the same closure."""

        if self.evidence_context is None:
            return library_lean_declaration_index()

        def build() -> dict[str, list[LeanDeclaration]]:
            if self.v11_lean_claim_graph_selected:
                records = getattr(
                    self.v11_lean_review_surface,
                    "library_source_declarations",
                    None,
                )
                if not isinstance(records, Mapping):
                    raise ValueError(
                        "selected v11 Lean review graph has no usable library declaration inventory"
                    )
                return lean_declaration_index_from_source_records(records)
            library_root = (ROOT / "AppliedModelingLib").resolve()
            library_sources = {
                path: content
                for path, content in self.lean_owned_source_snapshots().items()
                if library_root in path.parents
            }
            return lean_declaration_index_from_source_bytes(
                library_sources,
                library_modules=True,
            )

        value = self._memoized(("library_declaration_index",), build)
        assert isinstance(value, dict)
        return value

    def diagnostics(self) -> dict[str, int]:
        """Return non-authoritative transaction reuse counters for tracing."""

        source_snapshots = self._cache.get(("lean_owned_source_snapshots",))
        paper_index = self._cache.get(("paper_declaration_index",))
        library_index = self._cache.get(("library_declaration_index",))
        return {
            "memoized_entries": len(self._cache),
            "lean_owned_source_count": (
                len(source_snapshots) if isinstance(source_snapshots, dict) else 0
            ),
            "lean_owned_source_bytes": (
                sum(
                    len(content)
                    for content in source_snapshots.values()
                    if isinstance(content, bytes)
                )
                if isinstance(source_snapshots, dict)
                else 0
            ),
            "paper_declaration_count": (
                len(unique_declarations(paper_index))
                if isinstance(paper_index, dict)
                else 0
            ),
            "library_declaration_count": (
                len(unique_declarations(library_index))
                if isinstance(library_index, dict)
                else 0
            ),
        }


def paper_statement_sidecar_findings(
    paper_id: str,
    folder: Path,
    status: object,
    *,
    presentation_hygiene: bool = False,
    review_items_provider: Callable[[], tuple[Any, ...]] | None = None,
    corrected_scope_evaluation: tuple[bool, Exception | None] | None = None,
    status_payload_override: dict[str, object] | None = None,
    run_context: PaperCloseoutRunContext | None = None,
) -> list[Finding]:
    """Check current statement/review-surface LLM sidecars for one paper.

    The dashboard owns the sidecar schema and digest logic.  The repository
    audit enforces that completed papers do not pass CI with stale or missing
    statement-translation evidence.
    """

    severity = completed_status_finding_severity(status)
    selected_v11_closeout = bool(
        run_context is not None and run_context.selected_v11_closeout
    )
    findings = (
        []
        if selected_v11_closeout
        else paper_statement_map_declaration_findings(
            paper_id,
            folder,
            status,
            presentation_hygiene=presentation_hygiene,
            run_context=run_context,
            skip_semantic_contract_lean=False,
        )
    )
    status_payload = (
        status_payload_override
        if status_payload_override is not None
        else load_json_object(folder / "status.json") or {}
    )
    try:
        if corrected_scope_evaluation is None:
            corrected_scope_current = evaluate_author_approved_corrected_scope(
                folder, status_payload
            )
        else:
            corrected_scope_current, corrected_scope_error = (
                corrected_scope_evaluation
            )
            if corrected_scope_error is not None:
                raise corrected_scope_error
        if corrected_scope_current:
            # The explicit corrected-model contract is current structural
            # semantic evidence. Historical source-to-archive LLM sidecars
            # cannot certify this different target and are intentionally not
            # treated as current closeout evidence.
            return findings
    except Exception as exc:  # noqa: BLE001 - provenance checks fail closed below.
        findings.append(
            Finding(
                severity,
                folder / "status.json",
                f"`{paper_id}` corrected-model scope contract could not run: {exc}",
            )
        )
        return findings

    if selected_v11_closeout:
        # The selected v11 transaction owns the source/Spec review lane even
        # when one of its semantic leaves is stale. Its exact error is reported
        # by the primary and evidence gates. Typed map structure, source-route
        # projection, atom, defect, and source-fidelity checks are owned by the
        # later transaction-bound evidence capability; the legacy declaration
        # checker and dashboard summaries are never fallback evidence.
        return findings

    # Exact source-map contracts can replace only an absent/non-evidence
    # legacy statement or coverage lane.  They never suppress source-record,
    # model-semantic, assumption-provenance, populated-sidecar, or map-route
    # findings.  This keeps the bridge a source-item-level proof check rather
    # than a generic dashboard waiver.
    bridge_lanes = {"review_surface": False, "statement": False, "coverage": False}
    contract_bridge_current = semantic_contract_closeout_bridge_is_current(
        paper_id,
        folder,
        status,
        status_payload,
        run_context=run_context,
    )
    if contract_bridge_current:
        bridge_lanes = semantic_contract_closeout_blank_sidecar_lanes(
            folder,
            run_context=run_context,
        )
    try:
        from scripts.review_dashboard import (
            assumption_provenance_audit_summary,
            bind_current_v11_source_spec_screening,
            human_review_claim_items,
            paper_coverage_audit_summary,
            review_surface_audit_summary,
            statement_translation_audit_summary,
        )

        audit_inputs = (
            run_context.dashboard_audit_inputs()
            if run_context is not None and run_context.evidence_context is not None
            else None
        )
        dashboard_scope: Any = nullcontext()
        if audit_inputs is not None:
            from scripts.dashboard_audit_inputs import dashboard_audit_input_scope
            dashboard_scope = dashboard_audit_input_scope(audit_inputs)
        strict_semantic_kwargs: dict[str, object] = {}
        semantic_authority = (
            getattr(
                run_context.evidence_context,
                "semantic_reuse_authority",
                None,
            )
            if run_context is not None
            and run_context.evidence_context is not None
            else None
        )
        if semantic_authority is not None:
            strict_semantic_kwargs["semantic_reuse_authority"] = (
                semantic_authority
            )
        with dashboard_scope:
            items = (
                review_items_provider()
                if review_items_provider is not None
                else strict_review_items_for_paper(
                    folder,
                    build_input_provider=(
                        run_context.build_input_provider
                        if run_context is not None
                        else None
                    ),
                    audit_inputs=audit_inputs,
                    **strict_semantic_kwargs,
                )
            )
            surface = review_surface_audit_summary(folder, items)
            statements = statement_translation_audit_summary(folder, items)
            paper_coverage = paper_coverage_audit_summary(folder, items)
            assumptions = assumption_provenance_audit_summary(folder, items)
            v11_required = raw_source_spec_screening_requested(
                status_payload,
                folder=folder,
            )
            v11_screening_errors: list[str] = []
            v11_coverage_errors: list[str] = []
            if v11_required:
                # The v11 lane is deliberately raw source -> transparent Spec,
                # so it supersedes the legacy paraphrase/translation sidecars
                # only when every single human source-claim card carries a
                # current positive verdict.  The independent source-record
                # and map gates continue to prove completeness and proof
                # routing below; this code merely avoids requiring an obsolete
                # paraphrase judge in parallel.
                claim_rows = human_review_claim_items(folder, list(items))
                bind_current_v11_source_spec_screening(folder, claim_rows)
                for row in claim_rows:
                    # Source-model assumptions are audited through the
                    # independent assumption/source-record lane.  They are
                    # deliberately not transparent paper ``Spec`` claims, so
                    # requiring a raw-source-to-Spec row here would create an
                    # impossible duplicate obligation for an assumption-only
                    # declaration.
                    if row.get("is_assumption") is True:
                        continue
                    name = str(row.get("full_name") or "").strip()
                    verdict = str(row.get("llm_match_judgment") or "").strip()
                    source = str(row.get("llm_match_source") or "").strip()
                    if (
                        not name
                        or source != "v11_raw_source_spec_screening.json"
                        or verdict != "matches"
                    ):
                        v11_screening_errors.append(
                            f"{name or 'unnamed'}:{verdict or 'missing'}"
                        )
                # Coverage is checked source-first.  A larger source bundle
                # may explain one claim, but never covers a second claim that
                # happens to occur nearby.  Every selected byte-pinned source
                # item therefore has to appear exactly once as the map item
                # owning a current v11 source-to-Spec comparison.
                statement_map_path = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
                source_map = (
                    run_context.exact_json_payload(statement_map_path)
                    if run_context is not None
                    else load_json_object(statement_map_path)
                )
                source_map_items = (
                    source_map.get("items")
                    if isinstance(source_map, dict)
                    else None
                )
                if not isinstance(source_map_items, dict):
                    v11_coverage_errors.append("missing_source_inventory")
                else:
                    coverage_mode, coverage_mode_error = source_coverage_mode_from_map(
                        source_map
                    )
                    if coverage_mode_error:
                        v11_coverage_errors.append("invalid_source_coverage_mode")
                    else:
                        selected_source_ids = (
                            source_index_byte_pinned_anchor_item_ids(
                                folder,
                                source_map,
                                coverage_mode,
                                context=(
                                    run_context.evidence_context
                                    if run_context is not None
                                    else None
                                ),
                            )
                        )
                        required_items = filter_source_map_items_for_proof_obligations(
                            source_map_items,
                            coverage_mode,
                            declared_environment_kinds=(
                                source_named_result_environment_kinds_from_map(source_map)
                            ),
                            additional_selected_item_ids=selected_source_ids,
                        )
                        aliases, alias_errors = source_presentation_aliases(
                            source_map_items
                        )
                        if alias_errors:
                            v11_coverage_errors.append("invalid_presentation_aliases")
                        # This is the same source-to-Spec scope as the strict
                        # evidence gate. Selected support-only atoms are still
                        # checked by source/proof provenance, but have no
                        # transparent Spec and cannot require a v11 card.
                        required_keys = {
                            str(source_key)
                            for source_key, source_item in required_items.items()
                            if source_key not in aliases
                            and isinstance(source_item, Mapping)
                            and isinstance(source_item.get("semantic_contract"), Mapping)
                            and str(
                                source_item["semantic_contract"].get(
                                    "spec_declaration"
                                )
                                or ""
                            ).strip()
                        }
                        claims_by_source: dict[str, list[dict[str, Any]]] = {}
                        for row in claim_rows:
                            source_key = str(
                                row.get("human_claim_source_key") or ""
                            ).strip()
                            if source_key:
                                claims_by_source.setdefault(source_key, []).append(row)
                        spec_owners: dict[str, list[str]] = {}
                        for source_key in sorted(required_keys):
                            candidates = claims_by_source.get(source_key, [])
                            if len(candidates) != 1:
                                v11_coverage_errors.append(
                                    f"{source_key}:"
                                    + ("missing" if not candidates else "duplicate")
                                )
                                continue
                            source_item = required_items.get(source_key)
                            contract = (
                                source_item.get("semantic_contract")
                                if isinstance(source_item, dict)
                                else None
                            )
                            spec_name = (
                                str(contract.get("spec_declaration") or "").strip()
                                if isinstance(contract, dict)
                                else ""
                            )
                            card_name = str(
                                candidates[0].get("full_name") or ""
                            ).strip()
                            if not spec_name or card_name != spec_name:
                                v11_coverage_errors.append(
                                    f"{source_key}:wrong_spec"
                                )
                                continue
                            spec_owners.setdefault(spec_name, []).append(source_key)
                            if str(
                                candidates[0].get("llm_match_judgment") or ""
                            ).strip() != "matches":
                                v11_coverage_errors.append(
                                    f"{source_key}:not_current_v11_match"
                                )
                        # One semantic Spec has one source-claim owner.  A
                        # single expanded Lean proposition cannot silently
                        # take coverage credit for two independently anchored
                        # source presentations, even if their surrounding
                        # source bundles overlap.
                        for spec_name, owners in sorted(spec_owners.items()):
                            if len(owners) > 1:
                                v11_coverage_errors.append(
                                    f"{spec_name}:multiple_source_items"
                                )
    except Exception as exc:  # noqa: BLE001 - audit should report parser failures.
        return findings + [
            Finding(
                severity,
                folder,
                f"`{paper_id}` statement-sidecar audit could not run: {exc}",
            )
        ]

    if contract_bridge_current:
        current_semantic_reuse_lanes = (
            semantic_contract_closeout_current_semantic_reuse_lanes(
                surface,
                statements,
            )
        )
        for lane, reusable in current_semantic_reuse_lanes.items():
            if reusable:
                bridge_lanes[lane] = True

    if v11_required and not v11_screening_errors and not v11_coverage_errors:
        # A fully current v11 verdict is the source-semantic counterpart of
        # the legacy review-surface, translation, and coverage rows.  The
        # source-first coverage relation above additionally ensures that
        # context for one row cannot silently cover another source item.
        bridge_lanes.update(
            {"review_surface": True, "statement": True, "coverage": True}
        )

    for issue in statement_sidecar_summary_issues(
        paper_id,
        status,
        surface=surface,
        statements=statements,
        paper_coverage=paper_coverage,
        assumptions=assumptions,
        bridge_lanes=bridge_lanes,
        v11_required=v11_required,
        v11_screening_errors=v11_screening_errors,
        v11_coverage_errors=v11_coverage_errors,
    ):
        findings.append(
            Finding(severity, folder / issue.artifact, issue.message)
        )
    return findings


def _lower_initial(name: str) -> str:
    return name[:1].lower() + name[1:] if name else name


def source_equation_wrapper_candidates(name: str, decl_names: set[str]) -> list[str]:
    """Find likely source-equation wrappers that should replace an opaque alias row."""

    prefixes = {f"{name}_", f"{_lower_initial(name)}_"}
    candidates = []
    for candidate in decl_names:
        if candidate == name or not any(candidate.startswith(prefix) for prefix in prefixes):
            continue
        if any(marker in candidate for marker in SOURCE_EQUATION_WRAPPER_MARKERS):
            candidates.append(candidate)
    return sorted(candidates)


def _string_list_field(value: object) -> list[str] | None:
    if value is None:
        return []
    if not isinstance(value, list):
        return None
    if any(not isinstance(item, str) or not item.strip() for item in value):
        return None
    return [item.strip() for item in value]


def explicit_source_coverage_declaration_names(item: dict[str, object]) -> list[str] | None:
    """Return explicit declarations eligible to carry source coverage.

    Corrected source statements have a single complete repaired endpoint. The
    remaining declaration fields may document proof structure, but allowing
    them into source-coverage routing would let a renamed helper accumulate
    credit for a target it does not state.  This helper intentionally excludes
    aliases: a semantic-surface contract must bind to a written direct route,
    not legacy navigation metadata.
    """

    if (
        str(item.get("coverage_status") or "").strip().lower()
        == "corrected_source_statement"
    ):
        declarations = _string_list_field(item.get("lean_declarations"))
        if declarations is None or len(declarations) != 1:
            return None
        return declarations

    names: list[str] = []
    for field in SOURCE_COVERAGE_DECLARATION_ROUTING_FIELDS:
        values = _string_list_field(item.get(field))
        if values is None:
            return None
        names.extend(values)
    return list(dict.fromkeys(names))


def source_coverage_declaration_names(item: dict[str, object]) -> list[str] | None:
    """Return declarations eligible to carry source coverage for one item.

    Navigation aliases remain a narrow compatibility fallback only for legacy
    maps that have no explicit direct route.  New semantic-surface contracts
    use :func:`explicit_source_coverage_declaration_names` above and therefore
    cannot gain coverage through an alias.
    """

    names = explicit_source_coverage_declaration_names(item)
    if names is None:
        return None
    if names:
        return names

    # Legacy maps occasionally have no explicit source route at all. Preserve
    # that narrow compatibility fallback, but never let aliases supplement or
    # replace an explicit paper-facing route.
    aliases = _string_list_field(item.get("aliases"))
    if aliases is None:
        return None
    return list(dict.fromkeys(aliases))


def source_inventory_semantic_bridge_names(item: dict[str, object]) -> list[str] | None:
    """Return legacy paper-local bridge declarations for a source inventory item.

    These fields remain part of the legacy source-map contract.  Current v11
    closeout instead binds a direct reusable-library source route to the exact
    declaration through the Lean-owned graph and the current material-library
    semantic ledger.  That location-neutral route must not manufacture a
    paper-local wrapper merely because the implementation is reusable.
    """

    names: list[str] = []
    for field in SEMANTIC_BRIDGE_DECLARATION_FIELDS:
        values = _string_list_field(item.get(field))
        if values is None:
            return None
        names.extend(values)
    return list(dict.fromkeys(names))


def paper_reviewed_semantic_bridge_names(
    folder: Path,
    *,
    status_payload: Mapping[str, object] | None = None,
    source_text_by_path: Mapping[Path, str] | None = None,
    include_legacy_comment_hygiene: bool = False,
) -> tuple[set[str], dict[str, str]]:
    """Return reviewed/assumption bridge rows and leading comments for a paper.

    Source inventory entries may use reusable-library declarations only through
    paper-local bridge declarations.  Those bridges have to be part of the
    paper's audited semantic surface; otherwise a source item can be marked
    covered by a hidden helper whose only evidence is a source-looking name.
    """

    if status_payload is None:
        status_path = folder / "status.json"
        try:
            payload = json.loads(status_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return set(), {}
    else:
        payload = status_payload
    review_surface = payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return set(), {}
    reviewed_names: set[str] = set()
    for field in ("include_names", "assumption_names"):
        values = _string_list_field(review_surface.get(field))
        if values:
            for value in values:
                reviewed_names.add(value)
                reviewed_names.add(value.rsplit(".", 1)[-1])
    # Current v11 acceptance resolves every configured name through Lean's
    # elaborated declaration inventory and validates source status through the
    # typed source map. Leading Lean comments are an older, presentation-only
    # diagnostic; do not parse Lean merely to recover them on the accepting
    # path.
    comments: dict[str, str] = {}
    if not include_legacy_comment_hygiene:
        return reviewed_names, comments
    for review_path in {
        review_surface_source_file_path(folder, review_surface),
        proof_endpoint_source_file_path(folder, review_surface),
        assumption_source_file_path(folder, review_surface),
    }:
        if source_text_by_path is not None:
            text = source_text_by_path.get(review_path.resolve())
            if text is None:
                continue
        else:
            if not review_path.exists():
                continue
            try:
                text = review_path.read_text(encoding="utf-8")
            except OSError:
                continue
        comments.update(review_declaration_comments(text))
    return reviewed_names, comments


def _top_level_lean_assignment_candidates(source: str) -> list[tuple[int, int, int]]:
    """Return top-level ``:=`` positions with line/clause context.

    This is deliberately a small lexical scanner rather than a Lean parser.
    It is used only to remove a declaration's proof body before the cheap
    lexical guard runs.  In particular, a theorem result may contain
    ``let x := ...``; treating its first assignment as the proof boundary was
    both unsound and the reason C.5's actual conclusion was previously skipped.
    The Lean-elaborated schema-2 matcher below remains the authoritative check
    for conclusion shape.
    """

    candidates: list[tuple[int, int, int]] = []
    matching = {")": "(", "]": "[", "}": "{", "⦄": "⦃"}
    delimiters: list[str] = []
    in_string = False
    escaped = False
    line_start = 0
    clause_start = 0
    cursor = 0
    while cursor < len(source):
        char = source[cursor]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            cursor += 1
            continue
        if char == '"':
            in_string = True
            cursor += 1
            continue
        if char in "([{⦃":
            delimiters.append(char)
            cursor += 1
            continue
        if char in ")]}⦄":
            if delimiters and delimiters[-1] == matching.get(char):
                delimiters.pop()
            cursor += 1
            continue
        if char == "\n":
            line_start = cursor + 1
            clause_start = line_start
            cursor += 1
            continue
        if char == ";" and not delimiters:
            clause_start = cursor + 1
            cursor += 1
            continue
        if source.startswith(":=", cursor) and not delimiters:
            line_prefix = source[line_start:cursor]
            indentation = len(line_prefix) - len(line_prefix.lstrip(" \t"))
            candidates.append((cursor, indentation, clause_start))
            cursor += 2
            continue
        cursor += 1
    return candidates


def _top_level_assignment_is_let(source: str, assignment: int, clause_start: int) -> bool:
    """Return whether one top-level assignment belongs to a result-type `let`."""

    prefix = source[clause_start:assignment].strip()
    # This covers both a layout-style `let x := ...` line and the first inline
    # `theorem t : let x := ...; ...` clause.  A semicolon resets clause_start,
    # so the declaration assignment after that inline result is still found.
    return re.search(r"(?:^|:)\s*let(?:\s+rec)?\b", prefix) is not None


def declaration_body_assignment_start(
    source: str, declaration_match: re.Match[str] | None = None
) -> int | None:
    """Find the actual declaration ``:=`` while ignoring result-type lets.

    The declaration body is the first non-`let` top-level assignment; proof
    `have` assignments necessarily follow it.  Its indentation can be much
    deeper than the declaration header when a long result type ends with
    ``... := by`` on its final continuation line, so indentation is recorded
    only for diagnostics rather than used as a selector.  If the small scanner
    cannot isolate one, callers fail closed rather than inspect proof text as
    though it were the statement.
    """

    declaration_re = (
        _legacy_review_surface_structure_module().REVIEW_DECL_KIND_RE
    )
    match = declaration_match or declaration_re.match(source)
    if match is None:
        return None
    candidates = [
        (offset, indentation)
        for offset, indentation, clause_start in _top_level_lean_assignment_candidates(source)
        if not _top_level_assignment_is_let(source, offset, clause_start)
    ]
    if not candidates:
        return None
    return min(candidates, key=lambda candidate: candidate[0])[0]


def declaration_semantic_surface_signature(source: str, kind: str | None = None) -> str:
    """Return comment-free statement text for one direct declaration.

    A theorem/lemma contributes its proposition type, never its proof body. A
    transparent ``def``/``abbrev`` contributes its defining body as well,
    because source definitions are often directly routed through a Prop-valued
    definition.  The declared name is replaced by a neutral marker so a token
    contract cannot pass merely because a function happened to be named after
    a source concept.
    """

    surface = lean_code_text(source)
    declaration_re = (
        _legacy_review_surface_structure_module().REVIEW_DECL_KIND_RE
    )
    match = declaration_re.match(surface)
    declaration_kind = kind or (match.group(1) if match is not None else "")
    if declaration_kind not in {"def", "abbrev"}:
        body_start = declaration_body_assignment_start(surface, match)
        if body_start is None and declaration_kind not in {"axiom", "structure", "class", "inductive"}:
            # A semantic-surface contract must never fall back to proof text.
            # An unfamiliar declaration layout therefore fails closed through
            # an empty signature instead of accepting a proof-body decoy.
            return ""
        if body_start is not None:
            surface = surface[:body_start]
        match = declaration_re.match(surface)
    else:
        # The definition assignment token is not source-level equality.  Keep
        # the full transparent body, but do not let either its assignment or
        # a local `let ... :=` satisfy an equality requirement.
        surface = surface.replace(":=", ": ")
    if match is not None:
        name_start, name_end = match.span(2)
        surface = surface[:name_start] + "<declaration>" + surface[name_end:]
    return re.sub(r"\s+", " ", surface).strip()


def semantic_surface_token_present(surface: str, token: str) -> bool:
    """Match a configured source token without accepting identifier substrings."""

    if not token:
        return False
    if token == "=":
        # `:=` is an assignment, not an equality in a source proposition.
        return re.search(r"(?<![:<>=!])=(?![=>])", surface) is not None
    identifier_char = r"[A-Za-z0-9_']"
    left = (
        r"(?<!" + identifier_char + r")"
        if re.match(identifier_char, token[0])
        else ""
    )
    right = (
        r"(?!" + identifier_char + r")"
        if re.match(identifier_char, token[-1])
        else ""
    )
    return re.search(left + re.escape(token) + right, surface) is not None


SEMANTIC_SURFACE_RELATION_HEADS = {
    "eq": {"Eq"},
    "iff": {"Iff"},
    "lt": {"LT.lt"},
    "le": {"LE.le"},
    "not": {"Not"},
}
SEMANTIC_SURFACE_FEATURE_CONSTANTS = {
    "addition": {"HAdd.hAdd", "Add.add"},
    "conditional": {"ite", "dite"},
    "division": {"HDiv.hDiv", "Div.div"},
    "exponential": {"Real.exp"},
    "integral": {"MeasureTheory.integral"},
    "multiplication": {"HMul.hMul", "Mul.mul"},
    "subtraction": {"HSub.hSub", "Sub.sub"},
    "sum": {"Finset.sum", "MeasureTheory.integral"},
}

# Schema-3 features are a small, reviewed registry of exact elaborated Lean
# foundation primitives.  The source-map never receives raw declaration
# suffixes and no route, binder, proof-body, or paper-local helper spelling is
# inspected.  Paper-specific semantics are checked through result relations
# and alpha-normalized capture/reuse, not a growing list of paper names here.
SEMANTIC_SURFACE_RESULT_FEATURE_CONSTANTS = {
    "addition": {"HAdd.hAdd", "Add.add"},
    "conditional": {"ite", "dite"},
    "continuous": {"ContinuousAt"},
    "density": {"MeasureTheory.Measure.withDensity"},
    "density_coercion": {"ENNReal.ofReal"},
    "division": {"HDiv.hDiv", "Div.div"},
    "differentiable": {"DifferentiableAt"},
    "exponential": {"Real.exp"},
    "finite_cardinality": {"Fintype.card"},
    "finite_nonempty": {"Finset.Nonempty"},
    "finite_sum": {"Finset.sum"},
    "integral": {"MeasureTheory.integral"},
    "measure_map": {"MeasureTheory.Measure.map"},
    "measure_comp_prod": {"MeasureTheory.Measure.compProd"},
    "measure_pi": {"MeasureTheory.Measure.pi"},
    "measure_product": {"MeasureTheory.Measure.prod"},
    "multiplication": {"HMul.hMul", "Mul.mul"},
    "measure_dirac": {"MeasureTheory.Measure.dirac"},
    "pmf_map": {"PMF.map"},
    "pmf_to_measure": {"PMF.toMeasure"},
    "power": {"HPow.hPow", "Pow.pow"},
    "subtraction": {"HSub.hSub", "Sub.sub"},
    "tendsto": {"Filter.Tendsto"},
}


def _canonical_json_key(value: object) -> str:
    """Return a stable structural key for alpha-normalized canonical JSON."""

    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _canonical_scope_normalized_schema3_expression(value: object) -> object | None:
    """Locally normalize result-binder scope labels in one schema-3 expression.

    Result-leaf extraction assigns globally fresh ``scoped_bvar`` labels so
    captures cannot cross logical branches.  Those allocation labels are not
    mathematical content of an individual formula or guard, however:
    alpha-equivalent expressions from separate branches must receive the same
    digest.  This helper therefore renumbers just the labels visible within
    one expression while preserving equality/distinction among its bound
    variables.
    """

    scopes: set[int] = set()
    malformed = False

    def collect(current: object) -> None:
        nonlocal malformed
        if isinstance(current, list):
            for item in current:
                collect(item)
            return
        if not isinstance(current, dict):
            return
        if current.get("tag") == "scoped_bvar":
            raw_scope = current.get("scope")
            try:
                scope = int(str(raw_scope))
            except (TypeError, ValueError):
                malformed = True
                return
            if scope < 0:
                malformed = True
                return
            scopes.add(scope)
        for child in current.values():
            collect(child)

    collect(value)
    if malformed:
        return None
    replacements = {scope: str(index) for index, scope in enumerate(sorted(scopes))}

    def rewrite(current: object) -> object:
        if isinstance(current, list):
            return [rewrite(item) for item in current]
        if not isinstance(current, dict):
            return current
        rewritten = {key: rewrite(child) for key, child in current.items()}
        if rewritten.get("tag") == "scoped_bvar":
            raw_scope = rewritten.get("scope")
            try:
                scope = int(str(raw_scope))
            except (TypeError, ValueError):
                # ``collect`` checked every scoped binder; keep this branch
                # defensive for synthetic callers that mutate during traversal.
                return {"tag": "malformed_scoped_bvar"}
            rewritten["scope"] = replacements[scope]
        return rewritten

    return rewrite(value)


def canonical_schema3_expression_sha256(value: object) -> str:
    """Return a fail-closed digest of one scope-normalized schema-3 expression."""

    normalized = _canonical_scope_normalized_schema3_expression(value)
    if normalized is None:
        return ""
    return hashlib.sha256(_canonical_json_key(normalized).encode("utf-8")).hexdigest()


def _canonical_bvar_index(value: object) -> int | None:
    if not isinstance(value, dict) or value.get("tag") != "bvar":
        return None
    try:
        return int(str(value.get("index") or ""))
    except ValueError:
        return None


def _canonical_shift_bvars(value: object, cutoff: int, delta: int, depth: int = 0) -> object:
    """Shift canonical de-Bruijn variables while preserving binders."""

    index = _canonical_bvar_index(value)
    if index is not None:
        if index >= cutoff + depth:
            shifted = dict(value) if isinstance(value, dict) else {}
            shifted["index"] = str(index + delta)
            return shifted
        return value
    if isinstance(value, list):
        return [_canonical_shift_bvars(item, cutoff, delta, depth) for item in value]
    if not isinstance(value, dict):
        return value
    tag = value.get("tag")
    result: dict[str, object] = {}
    for key, child in value.items():
        child_depth = depth + 1 if tag in {"lam", "forall", "let"} and key == "body" else depth
        result[key] = _canonical_shift_bvars(child, cutoff, delta, child_depth)
    return result


def _canonical_substitute_let_bvar(
    value: object, replacement: object, depth: int = 0
) -> object:
    """Substitute the outer let-bound variable into canonical expression JSON."""

    index = _canonical_bvar_index(value)
    if index is not None:
        if index == depth:
            return _canonical_shift_bvars(replacement, 0, depth)
        if index > depth:
            substituted = dict(value) if isinstance(value, dict) else {}
            substituted["index"] = str(index - 1)
            return substituted
        return value
    if isinstance(value, list):
        return [
            _canonical_substitute_let_bvar(item, replacement, depth) for item in value
        ]
    if not isinstance(value, dict):
        return value
    tag = value.get("tag")
    result: dict[str, object] = {}
    for key, child in value.items():
        child_depth = depth + 1 if tag in {"lam", "forall", "let"} and key == "body" else depth
        result[key] = _canonical_substitute_let_bvar(child, replacement, child_depth)
    return result


def _canonical_zeta_result_lets(value: object) -> object:
    """Expand outer result lets without treating their values as free evidence."""

    current = value
    for _ in range(128):
        if not isinstance(current, dict) or current.get("tag") != "let":
            return current
        body = current.get("body")
        if body is None or "value" not in current:
            return current
        current = _canonical_substitute_let_bvar(body, current["value"])
    # A pathological synthetic manifest should fail its pattern rather than
    # looping forever. Live Lean manifests have the same bounded zeta policy.
    return {"tag": "malformed_result_let_chain"}


def _canonical_semantic_children(value: object) -> list[object]:
    """Return children in asserted term positions, never elaborator metadata.

    Canonical Lean applications retain the binder role of their final argument.
    Type, implicit, and instance arguments are evidence about elaboration, not
    mathematical content asserted by a source-facing proposition.  Older test
    fixtures predate that field, so their arguments remain explicit by default;
    a live ``unknown`` role fails closed by excluding the argument.
    """

    if isinstance(value, list):
        return list(value)
    if not isinstance(value, dict):
        return []
    tag = value.get("tag")
    if tag in {
        "forall",
        "inlined_definition",
        "internal_proof",
        "local_theorem",
        "local_constructor",
        "local_inductive",
        "local_recursor",
        "generated_proof",
    }:
        return []
    if tag == "lam":
        return [value.get("body")]
    if tag == "let":
        # Result-level lets are zeta-reduced before this matcher.  A nested
        # let contributes only through its asserted body, never its type/value.
        return [value.get("body")]
    if tag == "app":
        children = [value.get("fn")]
        binder_info = value.get("arg_binder_info")
        if binder_info is None or binder_info == "explicit":
            children.append(value.get("arg"))
        return children
    if tag == "proj":
        return [value.get("structure")]
    return [child for key, child in value.items() if key != "tag"]


def _canonical_subexpressions(value: object) -> list[object]:
    """Return semantic term subexpressions, excluding type/proof metadata.

    Schema-3 evidence must be asserted by a formula's term-level operands.
    In particular, a raw law appearing only in an embedded implication domain,
    local theorem type, dependency fingerprint, or typeclass argument is not a
    stated result law.
    """

    result: list[object] = []

    def visit(current: object) -> None:
        result.append(current)
        for item in _canonical_semantic_children(current):
            visit(item)

    visit(value)
    return result


def _canonical_feature_count(value: object, feature: str) -> int:
    """Count exact trusted feature constants in one canonical expression."""

    constants = SEMANTIC_SURFACE_RESULT_FEATURE_CONSTANTS.get(feature, set())
    if not constants:
        return 0
    return sum(
        1
        for item in _canonical_subexpressions(value)
        if isinstance(item, dict)
        and item.get("tag") == "const"
        and str(item.get("name") or "") in constants
    )


def _canonical_root_has_feature(value: object, feature: str) -> bool:
    """Check an exact feature at a subterm root, for capture selection."""

    constants = SEMANTIC_SURFACE_RESULT_FEATURE_CONSTANTS.get(feature, set())
    if not constants:
        return False
    head, _arguments = _canonical_application_head_and_args(value)
    if head in constants:
        return True
    return (
        isinstance(value, dict)
        and value.get("tag") == "const"
        and str(value.get("name") or "") in constants
    )


def _canonical_maximal_feature_roots(value: object, feature: str) -> list[object]:
    """Find feature-root applications without their partial-app prefixes."""

    constants = SEMANTIC_SURFACE_RESULT_FEATURE_CONSTANTS.get(feature, set())
    if not constants:
        return []
    roots: list[object] = []

    def visit(current: object, enclosing_head: str = "") -> None:
        head, _arguments = _canonical_application_head_and_args(current)
        if head in constants and head != enclosing_head:
            roots.append(current)
        if isinstance(current, dict) and current.get("tag") == "app":
            # The `fn` child of an application is a partial prefix of the
            # same head; do not treat it as a second law candidate.
            visit(current.get("fn"), head)
            binder_info = current.get("arg_binder_info")
            if binder_info is None or binder_info == "explicit":
                visit(current.get("arg"), "")
            return
        for item in _canonical_semantic_children(current):
            visit(item, "")

    visit(value)
    return roots


def _canonical_capture_candidates(
    component: object, feature: str, mode: str = "root"
) -> list[object]:
    """Find unique structural subterms eligible for a schema-3 capture."""

    candidates: list[object] = []
    relation_operands = _canonical_schema3_relation_operands(component)
    if mode == "opposite_relation_operand":
        if len(relation_operands) != 2:
            return []
        matching_indices = [
            index
            for index, operand in enumerate(relation_operands)
            if _canonical_feature_count(operand, feature) > 0
        ]
        if len(matching_indices) != 1:
            return []
        candidates = [relation_operands[1 - matching_indices[0]]]
    elif feature == "pmf_law":
        # A PMF law bridge is an equality whose direct operand is
        # `PMF.toMeasure law`.  Looking through every type/instance argument
        # would find unrelated occurrences of that projection in elaborated
        # metadata and make a capture ambiguous.
        for operand in relation_operands:
            head, arguments = _canonical_application_head_and_args(operand)
            if (
                head in SEMANTIC_SURFACE_RESULT_FEATURE_CONSTANTS["pmf_to_measure"]
                and arguments
            ):
                candidates.append(arguments[-1])
    else:
        # Equality/inequality bridge rows normally expose the law as a direct
        # relation operand.  Prefer that semantic position over occurrences
        # nested in elaborated typeclass metadata.  Fall back to a unique
        # proper subterm for expressions such as a product law under an
        # integral.
        direct = [
            operand
            for operand in relation_operands
            if _canonical_root_has_feature(operand, feature)
        ]
        candidates = direct or [
            item
            for operand in relation_operands
            for item in _canonical_maximal_feature_roots(operand, feature)
        ]
    # Multiple occurrences of one alpha-normalized subterm are harmless; two
    # different choices would make capture/reuse under-specified and fail.
    unique: dict[str, object] = {}
    for candidate in candidates:
        unique.setdefault(_canonical_json_key(candidate), candidate)
    return list(unique.values())


def _canonical_equality_alias_capture_candidate(
    formula: object, raw_capture: dict[str, object]
) -> dict[str, object] | None:
    """Bind one equality operand to one exact construction subtree.

    This intentionally does no equality rewriting.  The later result must
    contain the captured operand structurally, so an unrelated law, an alias
    chain, or a witness from another logical scope cannot receive credit.
    ``scoped_bvar`` identities installed by the result-leaf walker make
    same-spelling witnesses from distinct quantifier scopes nonidentical.
    """

    head, _arguments = _canonical_application_head_and_args(formula)
    if head != "Eq":
        return None
    operands = _canonical_schema3_relation_operands(formula)
    if len(operands) != 2:
        return None
    alias_side = raw_capture.get("alias_side")
    if alias_side not in {"left", "right"}:
        return None
    feature = str(raw_capture.get("construction_feature") or "")
    if feature not in SEMANTIC_SURFACE_RESULT_FEATURE_CONSTANTS:
        return None
    alias_index = 0 if alias_side == "left" else 1
    construction_index = 1 - alias_index
    alias = operands[alias_index]
    construction_operand = operands[construction_index]
    # The alias side must not be another occurrence of the construction.  A
    # law-equals-law equality has no directional alias binding to reuse.
    if _canonical_feature_count(alias, feature) != 0:
        return None
    roots = _canonical_maximal_feature_roots(construction_operand, feature)
    # Do not collapse duplicate roots by structural JSON: two textual
    # occurrences are ambiguous even if they elaborate alpha-equivalently.
    if len(roots) != 1:
        return None
    return {"alias": alias, "construction": roots[0]}


def _canonical_equality_alias_is_used(
    operand: object, capture: object
) -> bool:
    """Require exact same-scope syntactic use of an equality-bound alias."""

    if not isinstance(capture, dict) or "alias" not in capture:
        return False
    return _canonical_contains_subterm(operand, capture["alias"])


def _canonical_schema3_pattern_equality_alias_names(
    pattern: dict[str, object],
) -> set[str] | None:
    """Read every equality alias required by one result pattern.

    Alias placement is permitted in an operand pattern, so liveness and
    independent-content checks must account for both the formula and operand
    levels.  A malformed requirement fails closed even for direct callers that
    did not first run the schema validator.
    """

    nodes: list[dict[str, object]] = [pattern]
    raw_operand_patterns = pattern.get("operand_patterns")
    if raw_operand_patterns is not None:
        if not isinstance(raw_operand_patterns, list):
            return None
        for raw_operand in raw_operand_patterns:
            if not isinstance(raw_operand, dict):
                return None
            nodes.append(raw_operand)

    required_aliases: set[str] = set()
    for node in nodes:
        raw_required = node.get("requires_equality_aliases")
        if raw_required is None:
            continue
        if not isinstance(raw_required, list) or not raw_required:
            return None
        if any(
            not isinstance(name, str)
            or not name.strip()
            or name != name.strip()
            for name in raw_required
        ):
            return None
        if len(raw_required) != len(set(raw_required)):
            return None
        required_aliases.update(raw_required)
    return required_aliases


def _canonical_schema3_pattern_declares_alias_independent_feature(
    pattern: dict[str, object],
) -> bool:
    """Require a consumer to name at least one trusted semantic primitive."""

    nodes: list[dict[str, object]] = [pattern]
    raw_operand_patterns = pattern.get("operand_patterns")
    if raw_operand_patterns is not None:
        if not isinstance(raw_operand_patterns, list):
            return False
        for raw_operand in raw_operand_patterns:
            if not isinstance(raw_operand, dict):
                return False
            nodes.append(raw_operand)

    for node in nodes:
        raw_features = node.get("all_features")
        if raw_features is not None:
            if not isinstance(raw_features, list) or not raw_features:
                return False
            if any(
                not isinstance(feature, str)
                or feature not in SEMANTIC_SURFACE_RESULT_FEATURE_CONSTANTS
                for feature in raw_features
            ):
                return False
            return True
        raw_feature_counts = node.get("minimum_feature_counts")
        if raw_feature_counts is not None:
            if not isinstance(raw_feature_counts, dict) or not raw_feature_counts:
                return False
            if any(
                not isinstance(feature, str)
                or feature not in SEMANTIC_SURFACE_RESULT_FEATURE_CONSTANTS
                or not isinstance(count, int)
                or isinstance(count, bool)
                or count < 1
                for feature, count in raw_feature_counts.items()
            ):
                return False
            return True
    return False


def _canonical_feature_count_outside_subterms(
    value: object, feature: str, excluded_subterms: list[object]
) -> int:
    """Count a trusted feature only where it is not supplied by an alias term."""

    constants = SEMANTIC_SURFACE_RESULT_FEATURE_CONSTANTS.get(feature, set())
    if not constants:
        return 0
    excluded = {_canonical_json_key(item) for item in excluded_subterms}

    def visit(current: object) -> int:
        if _canonical_json_key(current) in excluded:
            return 0
        here = int(
            isinstance(current, dict)
            and current.get("tag") == "const"
            and str(current.get("name") or "") in constants
        )
        return here + sum(visit(child) for child in _canonical_semantic_children(current))

    return visit(value)


def _canonical_schema3_alias_requirements_have_independent_content(
    subjects: list[object],
    pattern: dict[str, object],
    equality_aliases: dict[str, object],
    required_aliases: set[str],
) -> bool:
    """Reject alias-only or repeated-alias equations as semantic evidence."""

    if len(subjects) != 2 or _canonical_json_key(subjects[0]) == _canonical_json_key(
        subjects[1]
    ):
        return False

    captures: list[dict[str, object]] = []
    for name in required_aliases:
        capture = equality_aliases.get(name)
        if (
            not isinstance(capture, dict)
            or "alias" not in capture
            or "construction" not in capture
        ):
            return False
        captures.append(capture)

    subject_keys = [_canonical_json_key(subject) for subject in subjects]
    for capture in captures:
        alias_key = _canonical_json_key(capture["alias"])
        construction_key = _canonical_json_key(capture["construction"])
        if subject_keys in ([alias_key, construction_key], [construction_key, alias_key]):
            # A separate copy of the binding equality does not establish a
            # later result that substantively uses the alias.
            return False

    alias_terms = [capture["alias"] for capture in captures]
    feature_nodes: list[tuple[list[object], dict[str, object]]] = [(subjects, pattern)]
    raw_operand_patterns = pattern.get("operand_patterns")
    if raw_operand_patterns is not None:
        if not isinstance(raw_operand_patterns, list):
            return False
        side_indices = {"left": 0, "right": 1, "argument": 0}
        for raw_operand in raw_operand_patterns:
            if not isinstance(raw_operand, dict):
                return False
            side = raw_operand.get("side")
            subject_index = side_indices.get(side)
            if subject_index is None or subject_index >= len(subjects):
                return False
            feature_nodes.append(([subjects[subject_index]], raw_operand))

    for scoped_subjects, node in feature_nodes:
        raw_features = node.get("all_features")
        if raw_features is not None:
            if not isinstance(raw_features, list) or not raw_features:
                return False
            for feature in raw_features:
                if (
                    isinstance(feature, str)
                    and feature in SEMANTIC_SURFACE_RESULT_FEATURE_CONSTANTS
                    and sum(
                        _canonical_feature_count_outside_subterms(
                            subject, feature, alias_terms
                        )
                        for subject in scoped_subjects
                    )
                    > 0
                ):
                    return True
        raw_feature_counts = node.get("minimum_feature_counts")
        if raw_feature_counts is not None:
            if not isinstance(raw_feature_counts, dict) or not raw_feature_counts:
                return False
            for feature, count in raw_feature_counts.items():
                if (
                    isinstance(feature, str)
                    and feature in SEMANTIC_SURFACE_RESULT_FEATURE_CONSTANTS
                    and isinstance(count, int)
                    and not isinstance(count, bool)
                    and count >= 1
                    and sum(
                        _canonical_feature_count_outside_subterms(
                            subject, feature, alias_terms
                        )
                        for subject in scoped_subjects
                    )
                    > 0
                ):
                    return True
    return False


def _schema3_equality_alias_contract_mismatches(patterns: list[object]) -> list[str]:
    """Fail closed on alias graph defects before structural leaf matching."""

    captures: set[str] = set()
    alias_capture_indices: dict[str, int] = {}
    alias_consumers: dict[str, list[int]] = {}
    mismatches: list[str] = []

    for index, raw_pattern in enumerate(patterns):
        if not isinstance(raw_pattern, dict):
            continue
        pattern_id = str(raw_pattern.get("id") or index)
        raw_capture = raw_pattern.get("capture")
        if isinstance(raw_capture, dict):
            capture_name = raw_capture.get("as")
            if isinstance(capture_name, str) and capture_name.strip():
                if capture_name in captures or capture_name in alias_capture_indices:
                    mismatches.append(
                        f"result pattern `{pattern_id}` repeats a capture or equality alias "
                        f"name `{capture_name}`"
                    )
                else:
                    captures.add(capture_name)

        raw_alias_capture = raw_pattern.get("equality_alias_capture")
        if isinstance(raw_alias_capture, dict):
            alias_name = raw_alias_capture.get("as")
            if isinstance(alias_name, str) and alias_name.strip():
                if alias_name in alias_capture_indices or alias_name in captures:
                    mismatches.append(
                        f"result pattern `{pattern_id}` repeats a capture or equality alias "
                        f"name `{alias_name}`"
                    )
                else:
                    alias_capture_indices[alias_name] = index

        required_aliases = _canonical_schema3_pattern_equality_alias_names(raw_pattern)
        if required_aliases is None:
            mismatches.append(
                f"result pattern `{pattern_id}` has malformed equality alias requirements"
            )
            continue
        if not required_aliases:
            continue
        if raw_pattern.get("allow_leaf_reuse") is True:
            mismatches.append(
                f"result pattern `{pattern_id}` may not reuse an equality alias consumer leaf"
            )
        if not _canonical_schema3_pattern_declares_alias_independent_feature(
            raw_pattern
        ):
            mismatches.append(
                f"result pattern `{pattern_id}` lacks independent semantic feature content "
                "outside an equality alias"
            )
        for alias_name in required_aliases:
            alias_consumers.setdefault(alias_name, []).append(index)

    for alias_name, capture_index in alias_capture_indices.items():
        if not any(
            consumer_index > capture_index
            for consumer_index in alias_consumers.get(alias_name, [])
        ):
            mismatches.append(
                f"equality alias `{alias_name}` captured by result pattern {capture_index} "
                "is not required by a later distinct result pattern"
            )
    return mismatches


def _canonical_contains_subterm(value: object, sought: object) -> bool:
    needle = _canonical_json_key(sought)
    return any(_canonical_json_key(item) == needle for item in _canonical_subexpressions(value))


def _canonical_application_head_and_args(value: object) -> tuple[str, list[object]]:
    """Return one elaborated application's head constant and ordered arguments."""

    current = value
    arguments: list[object] = []
    while isinstance(current, dict) and current.get("tag") == "app":
        arguments.append(current.get("arg"))
        current = current.get("fn")
    arguments.reverse()
    if isinstance(current, dict) and current.get("tag") == "const":
        name = current.get("name")
        return (name if isinstance(name, str) else "", arguments)
    return "", arguments


def _canonical_contains_constant(value: object, predicate: Callable[[str], bool]) -> bool:
    """Search the name-independent elaborated expression tree for one primitive."""

    if isinstance(value, list):
        return any(_canonical_contains_constant(item, predicate) for item in value)
    if not isinstance(value, dict):
        return False
    if value.get("tag") == "const" and predicate(str(value.get("name") or "")):
        return True
    return any(_canonical_contains_constant(item, predicate) for item in value.values())


def _canonical_is_zero(value: object) -> bool:
    """Recognize the elaborated numeral-zero term used by Lean arithmetic."""

    head, _arguments = _canonical_application_head_and_args(value)
    if head != "OfNat.ofNat":
        return False

    saw_zero_literal = False
    saw_zero_constructor = False

    def visit(item: object) -> None:
        nonlocal saw_zero_constructor, saw_zero_literal
        if isinstance(item, list):
            for child in item:
                visit(child)
            return
        if not isinstance(item, dict):
            return
        if item.get("tag") == "lit" and str(item.get("value") or "").endswith("natVal 0"):
            saw_zero_literal = True
        if item.get("tag") == "const" and str(item.get("name") or "") == "Zero.toOfNat0":
            saw_zero_constructor = True
        for child in item.values():
            visit(child)

    visit(value)
    return saw_zero_constructor and saw_zero_literal


def _canonical_strip_result_lets(value: object) -> object:
    """Remove elaborated `let` wrappers around a proposition result."""

    current = value
    while isinstance(current, dict) and current.get("tag") == "let":
        current = current.get("body")
    return current


def _canonical_result_components(value: object) -> list[object]:
    """Return result-side logical leaves, never binder premises or proof bodies."""

    components: list[object] = []

    def visit(current: object) -> None:
        current = _canonical_strip_result_lets(current)
        if isinstance(current, dict) and current.get("tag") == "forall":
            # A Pi/arrow's domain is a theorem premise.  Traverse only the
            # body, so a hypothesis cannot launder a source conclusion.
            visit(current.get("body"))
            return
        head, arguments = _canonical_application_head_and_args(current)
        if head == "And" and len(arguments) >= 2:
            visit(arguments[-2])
            visit(arguments[-1])
            return
        components.append(current)

    visit(value)
    return components


def _canonical_rightmost_top_level_conjunct(value: object) -> object:
    """Return the rightmost top-level conjunction component after result lets."""

    current = _canonical_strip_result_lets(value)
    while True:
        head, arguments = _canonical_application_head_and_args(current)
        if head != "And" or len(arguments) < 2:
            return current
        current = _canonical_strip_result_lets(arguments[-1])


def _canonical_component_matches_surface_clause(
    component: object, clause: dict[str, object]
) -> bool:
    """Check one result-side formula clause against an elaborated Lean component."""

    relation = str(clause.get("relation") or "")
    head, arguments = _canonical_application_head_and_args(component)
    if head not in SEMANTIC_SURFACE_RELATION_HEADS.get(relation, set()) or len(arguments) < 2:
        return False
    left, _right = arguments[-2:]
    if clause.get("left_operand") == "zero" and not _canonical_is_zero(left):
        return False

    raw_features = clause.get("required_semantic_features", [])
    features = raw_features if isinstance(raw_features, list) else []
    for feature in features:
        constants = SEMANTIC_SURFACE_FEATURE_CONSTANTS.get(str(feature), set())
        if not constants or not _canonical_contains_constant(
            component, lambda name, constants=constants: name in constants
        ):
            return False

    raw_suffixes = clause.get("required_constant_suffixes", [])
    suffixes = raw_suffixes if isinstance(raw_suffixes, list) else []
    for suffix in suffixes:
        normalized = str(suffix)
        if not _canonical_contains_constant(
            component,
            lambda name, normalized=normalized: name == normalized
            or name.endswith("." + normalized),
        ):
            return False
    return True


def semantic_surface_conclusion_component_mismatches(
    manifest: object, raw_surface: dict[str, object]
) -> list[str]:
    """Check schema-2 conclusion clauses against Lean's elaborated result.

    The declaration route is used only to obtain its current Lean manifest.
    This comparison inspects the result atom's canonical expression after
    outer theorem binders have been peeled, so statement, binder, and helper
    declaration names cannot make a formula obligation pass.
    """

    if not schema_version_is_exact(raw_surface.get("schema"), 2):
        return []
    if not isinstance(manifest, dict):
        return ["has no current Lean-elaborated conclusion manifest"]
    atoms = manifest.get("atoms")
    if not isinstance(atoms, list) or not atoms:
        return ["has no current Lean-elaborated conclusion manifest"]
    result = atoms[-1]
    if (
        not isinstance(result, dict)
        or result.get("ref") != "result"
        or result.get("role") != "conclusion"
        or result.get("canonical") is None
    ):
        return ["has no usable Lean-elaborated conclusion atom"]
    conclusion = result.get("canonical")
    raw_clauses = raw_surface.get("required_conclusion_components", [])
    clauses = raw_clauses if isinstance(raw_clauses, list) else []
    mismatches: list[str] = []
    for index, raw_clause in enumerate(clauses):
        if not isinstance(raw_clause, dict):
            continue
        selector = str(raw_clause.get("selector") or "")
        if selector == "rightmost_top_level_conjunct":
            candidates = [_canonical_rightmost_top_level_conjunct(conclusion)]
        elif selector == "any_result_component":
            candidates = _canonical_result_components(conclusion)
        else:
            candidates = []
        min_matches = raw_clause.get("min_matches", 1)
        required = min_matches if isinstance(min_matches, int) else 1
        matches = sum(
            _canonical_component_matches_surface_clause(candidate, raw_clause)
            for candidate in candidates
        )
        if matches < required:
            mismatches.append(
                "does not expose required conclusion component "
                f"{index} ({selector}, relation={raw_clause.get('relation')!r}, "
                f"expected at least {required} match(es), found {matches})"
            )
    return mismatches


def _canonical_scope_result_bvars(
    value: object, logical_binder_scopes: tuple[int, ...], local_depth: int = 0
) -> object:
    """Give result-quantified variables stable scope identities.

    Canonical expressions use de Bruijn indices.  A bare ``bvar(0)`` from two
    separate existential branches is not the same witness, even though their
    local serializations look identical.  Rewrite only variables that refer to
    result-level logical binders; lambda/let binders internal to a formula stay
    alpha-normalized de Bruijn indices.
    """

    index = _canonical_bvar_index(value)
    if index is not None:
        logical_index = index - local_depth
        if 0 <= logical_index < len(logical_binder_scopes):
            return {
                "tag": "scoped_bvar",
                "scope": str(logical_binder_scopes[-1 - logical_index]),
            }
        return value
    if isinstance(value, list):
        return [
            _canonical_scope_result_bvars(item, logical_binder_scopes, local_depth)
            for item in value
        ]
    if not isinstance(value, dict):
        return value
    tag = value.get("tag")
    result: dict[str, object] = {}
    for key, child in value.items():
        child_depth = (
            local_depth + 1
            if tag in {"lam", "forall", "let"} and key == "body"
            else local_depth
        )
        result[key] = _canonical_scope_result_bvars(
            child, logical_binder_scopes, child_depth
        )
    return result


def _canonical_schema3_is_logical_barrier(value: object) -> bool:
    """Return whether a leaf only contains a claim conditionally or disjunctively."""

    if isinstance(value, dict) and value.get("tag") == "forall":
        # The helper writes this field from Lean's ``isProp``.  Treat missing
        # metadata conservatively: synthetic/stale manifests must not turn an
        # implication premise into an unconditional result claim.
        return value.get("domain_is_proposition") is not False
    head, _arguments = _canonical_application_head_and_args(value)
    return head in {"Or", "Exists"}


def _canonical_result_leaves_schema3(
    value: object,
) -> list[tuple[object, tuple[object, ...], tuple[str, ...]]]:
    """Return result leaves with visible implication guards and scope preserved.

    Conjunctions and bodies of data quantifiers jointly state their leaves.
    A proposition-domain ``forall`` is an implication: its body is retained
    only with the exact visible guards that establish it.  A pattern must opt
    in to those guards, preventing a conditional source law from being read as
    unconditional.  Disjunctions remain nonmatching barriers.
    """

    leaves: list[tuple[object, tuple[object, ...], tuple[str, ...]]] = []
    next_scope = 0

    def fresh_scope() -> int:
        nonlocal next_scope
        scope = next_scope
        next_scope += 1
        return scope

    def lambda_body(value: object) -> object | None:
        if isinstance(value, dict) and value.get("tag") == "lam":
            return value.get("body")
        return None

    def add_leaf(
        current: object,
        scopes: tuple[int, ...],
        guards: tuple[object, ...],
        quantifiers: tuple[str, ...],
    ) -> None:
        leaves.append((
            _canonical_scope_result_bvars(current, scopes),
            guards,
            quantifiers,
        ))

    def visit(
        current: object,
        scopes: tuple[int, ...] = (),
        guards: tuple[object, ...] = (),
        quantifiers: tuple[str, ...] = (),
    ) -> None:
        current = _canonical_zeta_result_lets(current)
        if isinstance(current, dict) and current.get("tag") == "forall":
            if current.get("domain_is_proposition") is False:
                visit(
                    current.get("body"),
                    (*scopes, fresh_scope()),
                    guards,
                    (*quantifiers, "forall"),
                )
            else:
                # Preserve the condition itself and give the proof binder its
                # own scope before reading a potentially dependent body.
                condition = _canonical_scope_result_bvars(
                    current.get("domain"), scopes
                )
                visit(
                    current.get("body"),
                    (*scopes, fresh_scope()),
                    (*guards, condition),
                    quantifiers,
                )
            return
        head, arguments = _canonical_application_head_and_args(current)
        if head == "And" and len(arguments) >= 2:
            visit(arguments[-2], scopes, guards, quantifiers)
            visit(arguments[-1], scopes, guards, quantifiers)
            return
        if head == "Or":
            add_leaf(current, scopes, guards, quantifiers)
            return
        if head == "Exists" and arguments:
            body = lambda_body(arguments[-1])
            if body is not None:
                visit(
                    body,
                    (*scopes, fresh_scope()),
                    guards,
                    (*quantifiers, "exists"),
                )
                return
        add_leaf(current, scopes, guards, quantifiers)

    visit(value)
    return leaves


def _canonical_schema3_relation_operands(value: object) -> list[object]:
    """Return the formula-level operands, excluding relation typeclass data."""

    head, arguments = _canonical_application_head_and_args(value)
    if head in {"Eq", "Iff", "LT.lt", "LE.le"} and len(arguments) >= 2:
        return arguments[-2:]
    if head == "Not" and arguments:
        return [arguments[-1]]
    return []


def _canonical_schema3_feature_constraints_match(
    subjects: list[object], pattern: dict[str, object]
) -> bool:
    raw_features = pattern.get("all_features", [])
    features = raw_features if isinstance(raw_features, list) else []
    if any(
        sum(_canonical_feature_count(subject, str(feature)) for subject in subjects)
        < 1
        for feature in features
    ):
        return False
    raw_feature_counts = pattern.get("minimum_feature_counts", {})
    feature_counts = raw_feature_counts if isinstance(raw_feature_counts, dict) else {}
    for feature, count in feature_counts.items():
        if not isinstance(count, int) or sum(
            _canonical_feature_count(subject, str(feature)) for subject in subjects
        ) < count:
            return False
    return True


def _canonical_schema3_operand_matches(
    operand: object,
    pattern: dict[str, object],
    captures: dict[str, object],
    equality_aliases: dict[str, object],
) -> bool:
    if not _canonical_schema3_feature_constraints_match([operand], pattern):
        return False
    raw_required = pattern.get("requires_captures", [])
    required = raw_required if isinstance(raw_required, list) else []
    if not all(
        isinstance(name, str)
        and name in captures
        and _canonical_contains_subterm(operand, captures[name])
        for name in required
    ):
        return False
    raw_required_aliases = pattern.get("requires_equality_aliases", [])
    required_aliases = (
        raw_required_aliases if isinstance(raw_required_aliases, list) else []
    )
    return all(
        isinstance(name, str)
        and name in equality_aliases
        and _canonical_equality_alias_is_used(operand, equality_aliases[name])
        for name in required_aliases
    )


def _canonical_schema3_formula_matches(
    formula: object,
    pattern: dict[str, object],
    captures: dict[str, object],
    equality_aliases: dict[str, object],
) -> bool:
    """Match one formula at its asserted relation operands, never metadata."""

    if _canonical_schema3_is_logical_barrier(formula):
        return False
    expected_digest = pattern.get("canonical_sha256")
    if expected_digest is not None and (
        not isinstance(expected_digest, str)
        or canonical_schema3_expression_sha256(formula) != expected_digest
    ):
        return False
    relation = str(pattern.get("relation") or "")
    if relation != "any":
        head, arguments = _canonical_application_head_and_args(formula)
        minimum_arguments = 1 if relation == "not" else 2
        if (
            head not in SEMANTIC_SURFACE_RELATION_HEADS.get(relation, set())
            or len(arguments) < minimum_arguments
        ):
            return False

    subjects = (
        [formula]
        if relation == "any"
        else _canonical_schema3_relation_operands(formula)
    )
    if not subjects or not _canonical_schema3_feature_constraints_match(subjects, pattern):
        return False
    required_equality_aliases = _canonical_schema3_pattern_equality_alias_names(
        pattern
    )
    if required_equality_aliases is None:
        return False
    if required_equality_aliases and (
        not _canonical_schema3_pattern_declares_alias_independent_feature(pattern)
        or not _canonical_schema3_alias_requirements_have_independent_content(
            subjects, pattern, equality_aliases, required_equality_aliases
        )
    ):
        return False
    if relation == "any":
        # An unrelativized predicate requirement is positive evidence only at
        # the formula root.  Searching below `Not`, implication, or another
        # logical wrapper would turn the negation of a source condition into a
        # passing occurrence.
        raw_features = pattern.get("all_features", [])
        features = raw_features if isinstance(raw_features, list) else []
        raw_feature_counts = pattern.get("minimum_feature_counts", {})
        feature_counts = (
            raw_feature_counts if isinstance(raw_feature_counts, dict) else {}
        )
        if any(
            not _canonical_root_has_feature(formula, str(feature))
            for feature in features
        ) or any(
            not isinstance(count, int)
            or count != 1
            or not _canonical_root_has_feature(formula, str(feature))
            for feature, count in feature_counts.items()
        ):
            return False

    raw_operand_patterns = pattern.get("operand_patterns", [])
    operand_patterns = (
        raw_operand_patterns if isinstance(raw_operand_patterns, list) else []
    )
    side_indices = {"left": 0, "right": 1, "argument": 0}
    for raw_operand in operand_patterns:
        if not isinstance(raw_operand, dict):
            return False
        side = str(raw_operand.get("side") or "")
        index = side_indices.get(side)
        if index is None or index >= len(subjects):
            return False
        if not _canonical_schema3_operand_matches(
            subjects[index], raw_operand, captures, equality_aliases
        ):
            return False

    if pattern.get("require_distinct_operands") is True:
        if len(subjects) != 2 or _canonical_json_key(subjects[0]) == _canonical_json_key(subjects[1]):
            return False

    raw_required = pattern.get("requires_captures", [])
    required = raw_required if isinstance(raw_required, list) else []
    if not all(
        isinstance(name, str)
        and name in captures
        and any(
            _canonical_contains_subterm(subject, captures[name])
            for subject in subjects
        )
        for name in required
    ):
        return False
    return all(
        isinstance(name, str)
        and name in equality_aliases
        and any(
            _canonical_equality_alias_is_used(subject, equality_aliases[name])
            for subject in subjects
        )
        for name in required_equality_aliases
    )


def _canonical_schema3_guard_patterns_match(
    guards: tuple[object, ...],
    pattern: dict[str, object],
    captures: dict[str, object],
    equality_aliases: dict[str, object],
) -> bool:
    raw_guard_patterns = pattern.get("guard_patterns")
    if raw_guard_patterns is None:
        return not guards
    guard_patterns = (
        raw_guard_patterns if isinstance(raw_guard_patterns, list) else []
    )
    if len(guards) != len(guard_patterns):
        return False
    unmatched = list(guards)
    for raw_guard in guard_patterns:
        if not isinstance(raw_guard, dict):
            return False
        match_index = next(
            (
                index
                for index, guard in enumerate(unmatched)
                if _canonical_schema3_formula_matches(
                    guard, raw_guard, captures, equality_aliases
                )
            ),
            None,
        )
        if match_index is None:
            return False
        del unmatched[match_index]
    return not unmatched


def _canonical_result_leaf_matches_schema3(
    leaf: tuple[object, tuple[object, ...], tuple[str, ...]],
    pattern: dict[str, object],
    captures: dict[str, object],
    equality_aliases: dict[str, object],
) -> bool:
    formula, guards, quantifiers = leaf
    raw_quantifier_shape = pattern.get("quantifier_shape")
    quantifier_shape = (
        raw_quantifier_shape if isinstance(raw_quantifier_shape, dict) else {}
    )
    if (
        quantifiers.count("forall") != quantifier_shape.get("forall")
        or quantifiers.count("exists") != quantifier_shape.get("exists")
    ):
        return False
    return _canonical_schema3_guard_patterns_match(
        guards, pattern, captures, equality_aliases
    ) and _canonical_schema3_formula_matches(
        formula, pattern, captures, equality_aliases
    )


def semantic_surface_result_pattern_mismatches(
    manifest: object, raw_surface: dict[str, object]
) -> list[str]:
    """Check schema-3 result-only structural contracts.

    A match is based solely on Lean's elaborated result atom, exact foundation
    primitives, and alpha-normalized subterm identity.  This makes wrapper,
    binder, source-term, and proof-body names irrelevant to the decision.
    """

    if not schema_version_is_exact(raw_surface.get("schema"), 3):
        return []
    if not isinstance(manifest, dict):
        return ["has no current Lean-elaborated conclusion manifest"]
    if manifest.get("declaration_kind") != "theorem":
        return ["schema-3 direct route must be a theorem"]
    atoms = manifest.get("atoms")
    if not isinstance(atoms, list) or not atoms:
        return ["has no current Lean-elaborated conclusion manifest"]
    result = atoms[-1]
    if (
        not isinstance(result, dict)
        or result.get("ref") != "result"
        or result.get("role") != "conclusion"
        or result.get("canonical") is None
    ):
        return ["has no usable Lean-elaborated conclusion atom"]

    leaves = _canonical_result_leaves_schema3(result.get("canonical"))
    raw_patterns = raw_surface.get("required_result_patterns", [])
    patterns = raw_patterns if isinstance(raw_patterns, list) else []
    mismatches = _schema3_equality_alias_contract_mismatches(patterns)
    if mismatches:
        return mismatches
    failures: list[tuple[int, str]] = []
    failed_states: set[
        tuple[
            int,
            tuple[tuple[str, str], ...],
            tuple[tuple[str, str], ...],
            tuple[int, ...],
        ]
    ] = set()

    def capture_state_key(captures: dict[str, object]) -> tuple[tuple[str, str], ...]:
        return tuple(
            sorted(
                (name, _canonical_json_key(value)) for name, value in captures.items()
            )
        )

    def equality_alias_state_key(
        equality_aliases: dict[str, object],
    ) -> tuple[tuple[str, str], ...]:
        return tuple(
            sorted(
                (name, _canonical_json_key(value))
                for name, value in equality_aliases.items()
            )
        )

    def search_pattern_graph(
        index: int,
        captures: dict[str, object],
        equality_aliases: dict[str, object],
        used_leaf_indices: frozenset[int],
    ) -> dict[str, object] | None:
        if index >= len(patterns):
            return captures
        raw_pattern = patterns[index]
        if not isinstance(raw_pattern, dict):
            return search_pattern_graph(
                index + 1, captures, equality_aliases, used_leaf_indices
            )
        state = (
            index,
            capture_state_key(captures),
            equality_alias_state_key(equality_aliases),
            tuple(sorted(used_leaf_indices)),
        )
        if state in failed_states:
            return None
        pattern_id = str(raw_pattern.get("id") or index)
        matching_indices = [
            leaf_index
            for leaf_index, leaf in enumerate(leaves)
            if _canonical_result_leaf_matches_schema3(
                leaf, raw_pattern, captures, equality_aliases
            )
        ]
        raw_minimum = raw_pattern.get("min_matches", 1)
        minimum = raw_minimum if isinstance(raw_minimum, int) else 1
        allow_leaf_reuse = raw_pattern.get("allow_leaf_reuse") is True
        eligible_indices = (
            matching_indices
            if allow_leaf_reuse
            else [
                leaf_index
                for leaf_index in matching_indices
                if leaf_index not in used_leaf_indices
            ]
        )
        if len(eligible_indices) < minimum:
            failures.append((
                index,
                f"does not expose required result pattern `{pattern_id}` "
                f"(expected at least {minimum} unused match(es), found {len(eligible_indices)})",
            ))
            failed_states.add(state)
            return None

        raw_capture = raw_pattern.get("capture")
        raw_equality_alias_capture = raw_pattern.get("equality_alias_capture")
        if isinstance(raw_capture, dict) and isinstance(raw_equality_alias_capture, dict):
            # The schema validator rejects this combination.  Keep the
            # matching path fail-closed for callers that bypass validation.
            failures.append((
                index,
                f"result pattern `{pattern_id}` cannot combine capture and equality alias capture",
            ))
            failed_states.add(state)
            return None
        if isinstance(raw_equality_alias_capture, dict):
            if allow_leaf_reuse:
                # An equality alias must be consumed by a later distinct leaf;
                # reusing its source leaf would make that condition vacuous.
                failures.append((
                    index,
                    f"result pattern `{pattern_id}` may not reuse an equality alias capture leaf",
                ))
                failed_states.add(state)
                return None
            alias_name = str(raw_equality_alias_capture.get("as") or "")
            if (
                minimum != 1
                or not alias_name
                or alias_name in equality_aliases
                or alias_name in captures
            ):
                # These cases are rejected by the schema validator.  Do not
                # let direct callers turn an under-specified alias binding
                # into a successful surface match.
                failures.append((
                    index,
                    f"result pattern `{pattern_id}` has an invalid equality alias capture",
                ))
                failed_states.add(state)
                return None
            # Candidate selection is intentionally global across matching
            # leaves.  Two equality bindings, even alpha-equivalent ones,
            # leave the requested alias under-specified.
            alias_candidates = [
                (leaf_index, candidate)
                for leaf_index in matching_indices
                if (
                    candidate := _canonical_equality_alias_capture_candidate(
                        leaves[leaf_index][0], raw_equality_alias_capture
                    )
                )
                is not None
            ]
            if len(alias_candidates) != 1:
                qualifier = "no" if not alias_candidates else "more than one"
                failures.append((
                    index,
                    f"result pattern `{pattern_id}` exposes {qualifier} uniquely bindable "
                    "equality alias",
                ))
                failed_states.add(state)
                return None
            leaf_index, alias_capture = alias_candidates[0]
            if leaf_index not in eligible_indices:
                failures.append((
                    index,
                    f"result pattern `{pattern_id}` binds its equality alias only from an "
                    "already consumed result leaf",
                ))
                failed_states.add(state)
                return None
            next_aliases = dict(equality_aliases)
            next_aliases[alias_name] = alias_capture
            outcome = search_pattern_graph(
                index + 1,
                captures,
                next_aliases,
                used_leaf_indices.union({leaf_index}),
            )
            if outcome is not None:
                return outcome
            failures.append((
                index,
                f"result pattern `{pattern_id}` has no equality alias binding compatible "
                "with later required result patterns",
            ))
            failed_states.add(state)
            return None

        if not isinstance(raw_capture, dict):
            for selected_indices in itertools.combinations(eligible_indices, minimum):
                next_used = (
                    used_leaf_indices
                    if allow_leaf_reuse
                    else used_leaf_indices.union(selected_indices)
                )
                outcome = search_pattern_graph(
                    index + 1, captures, equality_aliases, next_used
                )
                if outcome is not None:
                    return outcome
            failed_states.add(state)
            return None

        feature = str(raw_capture.get("feature") or "")
        mode = str(raw_capture.get("mode") or "root")
        capture_name = str(raw_capture.get("as") or "")
        if (
            not capture_name
            or capture_name in captures
            or capture_name in equality_aliases
        ):
            failures.append((
                index,
                f"result pattern `{pattern_id}` has an invalid capture name",
            ))
            failed_states.add(state)
            return None
        raw_distinct = raw_capture.get("distinct_from", [])
        distinct_from = raw_distinct if isinstance(raw_distinct, list) else []
        candidates_by_key: dict[tuple[int, str], object] = {}
        for leaf_index in eligible_indices:
            capture_leaf = leaves[leaf_index]
            candidates = _canonical_capture_candidates(capture_leaf[0], feature, mode)
            if len(candidates) == 1:
                candidates_by_key.setdefault(
                    (leaf_index, _canonical_json_key(candidates[0])), candidates[0]
                )
        if not candidates_by_key:
            failures.append((
                index,
                f"result pattern `{pattern_id}` cannot uniquely capture `{feature}` "
                "from any matching result leaf",
            ))
            failed_states.add(state)
            return None
        for (leaf_index, _candidate_key), candidate in candidates_by_key.items():
            equal_prior = [
                name
                for name in distinct_from
                if isinstance(name, str)
                and name in captures
                and _canonical_json_key(captures[name]) == _canonical_json_key(candidate)
            ]
            if equal_prior:
                continue
            next_captures = dict(captures)
            next_captures[capture_name] = candidate
            next_used = (
                used_leaf_indices
                if allow_leaf_reuse
                else used_leaf_indices.union({leaf_index})
            )
            outcome = search_pattern_graph(
                index + 1, next_captures, equality_aliases, next_used
            )
            if outcome is not None:
                return outcome
        failures.append((
            index,
            f"result pattern `{pattern_id}` has no capture choice compatible with "
            "later required result patterns",
        ))
        failed_states.add(state)
        return None

    if search_pattern_graph(0, {}, {}, frozenset()) is None:
        if failures:
            first_failure = min(failures, key=lambda failure: failure[0])[1]
            mismatches.append(first_failure)
        else:
            mismatches.append("does not expose a coherent required result-pattern graph")

    raw_assumption_patterns = raw_surface.get("required_assumption_patterns", [])
    assumption_patterns = (
        raw_assumption_patterns if isinstance(raw_assumption_patterns, list) else []
    )
    assumption_types = [
        atom.get("canonical")
        for atom in atoms[:-1]
        if isinstance(atom, dict)
        and atom.get("role") == "assumption"
        and atom.get("canonical") is not None
    ]
    for index, raw_pattern in enumerate(assumption_patterns):
        if not isinstance(raw_pattern, dict):
            continue
        pattern_id = str(raw_pattern.get("id") or index)
        matches = sum(
            _canonical_schema3_formula_matches(assumption, raw_pattern, {}, {})
            for assumption in assumption_types
        )
        raw_minimum = raw_pattern.get("min_matches", 1)
        minimum = raw_minimum if isinstance(raw_minimum, int) else 1
        if matches < minimum:
            mismatches.append(
                f"does not expose required explicit assumption `{pattern_id}` "
                f"(expected at least {minimum} match(es), found {matches})"
            )
    return mismatches


def semantic_surface_signature_mismatches(
    declaration: LeanDeclaration, raw_surface: dict[str, object]
) -> list[str]:
    """Compare one direct declaration's visible type against a valid contract.

    ``required_structural_tokens`` are mathematical syntax, while
    ``required_terms`` can pin source-model primitives such as a raw law or
    finite expectation operator.  Neither category consults the declaration's
    own name, and opaque wrapper names are checked only in the visible type.
    """

    signature = declaration_semantic_surface_signature(
        declaration.source, declaration.kind
    )
    if not signature:
        return ["has no readable declaration signature"]

    def tokens(field: str) -> list[str]:
        raw = raw_surface.get(field, [])
        if not isinstance(raw, list):
            return []
        return [
            value.strip()
            for value in raw
            if isinstance(value, str) and value.strip()
        ]

    mismatches: list[str] = []
    missing_structural = [
        token
        for token in tokens("required_structural_tokens")
        if not semantic_surface_token_present(signature, token)
    ]
    if missing_structural:
        mismatches.append(
            "is missing required structural token(s) in its comment-free declaration "
            "signature: " + ", ".join(missing_structural)
        )
    missing_terms = [
        token
        for token in tokens("required_terms")
        if not semantic_surface_token_present(signature, token)
    ]
    if missing_terms:
        mismatches.append(
            "is missing required source-model term(s) in its comment-free declaration "
            "signature: " + ", ".join(missing_terms)
        )
    opaque_terms = [
        token
        for token in tokens("forbidden_opaque_terms")
        if semantic_surface_token_present(signature, token)
    ]
    if opaque_terms:
        mismatches.append(
            "contains forbidden opaque wrapper term(s) in its declaration signature: "
            + ", ".join(opaque_terms)
        )
    return mismatches


@dataclass(frozen=True)
class SemanticContractSurfaceRoute:
    """A current exact contract eligible to supply a schema-3 audit surface.

    The declaration names retained here are only stable handles for Lean and
    the source map.  Acceptance is established by declaration identity,
    Lean-Meta type equality, and the transparent Spec body; no matcher treats
    either spelling as mathematical evidence.
    """

    source_key: str
    evidence: LeanDeclaration
    specification: LeanDeclaration
    qualified_evidence: str
    qualified_specification: str
    evidence_mode: str


@dataclass(frozen=True)
class SemanticSurfaceManifestRequest:
    """One current elaborated root for a schema-2/3 surface check."""

    source_key: str
    route: str
    declaration: LeanDeclaration
    qualified_manifest_name: str
    raw_surface: dict[str, object]
    contract_specification: bool = False


def semantic_contract_spec_definition_value_manifest(
    manifest: object,
) -> dict[str, object] | None:
    """Project a transparent Prop definition manifest into a schema-3 surface.

    Lean's ordinary manifest records a ``def``/``abbrev`` result as
    ``{tag: definition, type: Prop, value: <rhs>}``.  Schema 3 needs the
    independently written proposition, not that outer ``Prop`` type and not
    the proof theorem's potentially opaque-looking conclusion.  This derived
    manifest keeps the Spec's elaborated outer binders and replaces only its
    result with the transparent definition value.

    It is intentionally theorem-shaped for the existing result-pattern
    matcher and outer-binder digest: it represents a proposition *surface*,
    not a declaration that can receive direct source coverage on its own.
    """

    if not isinstance(manifest, dict):
        return None
    if (
        manifest.get("declaration_kind") != "definition"
        or manifest.get("conclusion_mode") != "type_and_value"
    ):
        return None
    raw_atoms = manifest.get("atoms")
    if not isinstance(raw_atoms, list) or not raw_atoms:
        return None
    result = raw_atoms[-1]
    if (
        not isinstance(result, dict)
        or result.get("ref") != "result"
        or result.get("role") != "conclusion"
    ):
        return None
    canonical = result.get("canonical")
    if not isinstance(canonical, dict) or canonical.get("tag") != "definition":
        return None
    value = canonical.get("value")
    if value is None:
        return None

    atoms: list[dict[str, object]] = []
    for atom in raw_atoms[:-1]:
        if not isinstance(atom, dict):
            return None
        atoms.append(dict(atom))
    atoms.append(
        {
            "ref": "result",
            "role": "conclusion",
            "canonical": value,
            "display": "transparent Spec proposition body",
        }
    )
    return {
        "schema": manifest.get("schema"),
        "declaration_kind": "theorem",
        "conclusion_mode": "type_only",
        "semantic_surface_origin": "transparent_contract_spec",
        "atoms": atoms,
    }


def _resolve_schema3_surface_route(
    paper_declarations: dict[str, list[LeanDeclaration]],
    route: str,
    paper_interface_path: Path,
) -> list[LeanDeclaration]:
    """Resolve a paper-facing schema-3 route without short-name credit."""

    resolved = resolve_declaration_name(paper_declarations, route)
    if len(resolved) != 1:
        # A paper may retain an implementation helper with the same short
        # name.  The PaperInterface declaration is the paper-facing route.
        resolved = [
            declaration
            for declaration in resolved
            if declaration.path.resolve() == paper_interface_path
        ]
    return resolved


def semantic_contract_schema3_surface_routes(
    paper_id: str,
    folder: Path,
    status: object,
    payload: dict[str, object],
    paper_declarations: dict[str, list[LeanDeclaration]],
    reviewed_declaration_keys: set[tuple[Path, int, str]],
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    run_context: PaperCloseoutRunContext | None = None,
) -> tuple[dict[str, SemanticContractSurfaceRoute], list[Finding]]:
    """Return schema-3 routes whose current contract can supply a Spec body.

    This is deliberately narrower than the full semantic-contract audit.  It
    supplies an alternate *surface root* only after exact identity binding,
    current Lean-Meta proof checking, and current transitive Spec
    transparency.  Schema 1/2 routes never enter this function.
    """

    statement_map = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    severity = completed_status_finding_severity(status)
    findings: list[Finding] = []
    routes: dict[str, SemanticContractSurfaceRoute] = {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return routes, findings

    try:
        from scripts.audit_evidence_integrity import (
            SEMANTIC_CONTRACT_SCHEMAS,
            semantic_contract_validation_errors,
        )
    except Exception as error:  # noqa: BLE001 - a closeout route fails closed.
        return routes, [
            Finding(
                "ERROR",
                statement_map,
                f"`{paper_id}` contract-backed schema-3 surface audit could not run: {error}",
            )
        ]

    contract_schema = payload.get("semantic_contract_schema")
    if not schema_version_is_supported(
        contract_schema, SEMANTIC_CONTRACT_SCHEMAS
    ):
        return routes, findings

    paper_interface_path = (folder / "PaperInterface.lean").resolve()
    requested: dict[str, SemanticContractSurfaceRoute] = {}
    for raw_source_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict):
            continue
        raw_surface = raw_item.get("semantic_surface")
        if not isinstance(raw_surface, dict) or not schema_version_is_exact(
            raw_surface.get("schema"), 3
        ):
            continue
        raw_contract = raw_item.get("semantic_contract")
        if not isinstance(raw_contract, dict):
            continue
        source_key = str(raw_source_key)
        if raw_item.get("claim_bearing") is not True:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` schema-3 semantic-contract "
                    "surface must be claim-bearing",
                )
            )
            continue
        if semantic_contract_validation_errors(raw_contract, schema=contract_schema):
            # The full semantic-contract inventory reports precise schema
            # errors.  Do not manufacture an alternate route from malformed
            # metadata here.
            continue
        direct_routes = explicit_source_coverage_declaration_names(raw_item)
        if direct_routes is None or len(direct_routes) != 1:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` contract-backed schema-3 "
                    "surface requires exactly one explicit direct coverage route",
                )
            )
            continue
        direct_resolved = _resolve_schema3_surface_route(
            paper_declarations, direct_routes[0], paper_interface_path
        )
        if len(direct_resolved) != 1:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` contract-backed schema-3 "
                    f"direct route `{direct_routes[0]}` must resolve to one paper-facing declaration",
                )
            )
            continue
        direct = direct_resolved[0]
        spec_name = str(raw_contract["spec_declaration"]).strip()
        evidence_name = str(raw_contract["evidence_declaration"]).strip()
        mode = str(raw_contract["evidence_mode"]).strip()
        spec_resolved = resolve_declaration_name(paper_declarations, spec_name)
        evidence_resolved = resolve_declaration_name(paper_declarations, evidence_name)
        if len(spec_resolved) != 1 or len(evidence_resolved) != 1:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` contract-backed schema-3 "
                    "surface must resolve its Spec and evidence to one paper-local declaration each",
                )
            )
            continue
        specification = spec_resolved[0]
        evidence = evidence_resolved[0]
        if declaration_key(evidence) != declaration_key(direct):
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` contract evidence is not "
                    "the exact explicit direct coverage declaration",
                )
            )
            continue
        if declaration_key(specification) == declaration_key(evidence):
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` contract Spec and evidence "
                    "must be distinct declarations",
                )
            )
            continue
        if (
            evidence.kind not in SEMANTIC_CONTRACT_EVIDENCE_KINDS
            or specification.kind not in {"def", "abbrev"}
            or mode not in {"proves", "definitionally_realizes"}
        ):
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` contract-backed schema-3 "
                    "surface requires a theorem/lemma evidence route, a transparent def/abbrev "
                    "Prop Spec, and a positive evidence mode",
                )
            )
            continue
        if (
            declaration_key(evidence) not in reviewed_declaration_keys
            or declaration_key(specification) not in reviewed_declaration_keys
            or evidence.path.resolve() != paper_interface_path
            or specification.path.resolve() != paper_interface_path
        ):
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` contract-backed schema-3 "
                    "surface must keep both exact declarations on the reviewed PaperInterface surface",
                )
            )
            continue
        native_surface = (
            run_context.v11_lean_review_surface
            if run_context is not None
            and run_context.selected_v11_closeout
            else None
        )
        native_sources = getattr(native_surface, "source_declarations", None)
        native_targets = getattr(native_surface, "semantic_targets", None)
        qualified_specification = _qualified_contract_declaration_name(
            paper_declarations, spec_name
        )
        if isinstance(native_sources, Mapping) and isinstance(
            native_targets, Mapping
        ):
            native_source = native_sources.get(qualified_specification)
            independence_error = (
                "specification is absent from the accepted Lean semantic graph"
                if not isinstance(native_source, Mapping)
                or qualified_specification not in native_targets
                else ""
            )
        else:
            independence_error = semantic_contract_spec_structure_error(
                paper_declarations,
                specification,
                require_visible_syntax=not source_spec_correspondence_enabled(payload),
            )
        if independence_error:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` contract-backed schema-3 "
                    f"surface {independence_error}",
                )
            )
            continue
        qualified_evidence = _qualified_contract_declaration_name(
            paper_declarations, evidence_name
        )
        if not qualified_specification or not qualified_evidence:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` contract-backed schema-3 "
                    "surface could not determine unique namespace-qualified Lean identities",
                )
            )
            continue
        requested[source_key] = SemanticContractSurfaceRoute(
            source_key=source_key,
            evidence=evidence,
            specification=specification,
            qualified_evidence=qualified_evidence,
            qualified_specification=qualified_specification,
            evidence_mode=mode,
        )

    if not requested:
        return routes, findings
    try:
        from scripts.lean_signature_manifest import (
            paper_local_module_names,
            run_lean_semantic_contract_matches,
            run_lean_semantic_contract_transparency_checks,
        )
        from scripts.review_dashboard import review_source_file, review_source_module
        source_path = review_source_file(folder)
        module = review_source_module(folder, source_path)
        transparency_checks = run_lean_semantic_contract_transparency_checks(
            ROOT,
            module,
            sorted(
                {
                    route.qualified_specification
                    for route in requested.values()
                }
            ),
            paper_local_module_names(
                ROOT, folder, provider=build_input_provider
            ),
            build_input_provider=build_input_provider,
        )
        meta_matches = run_lean_semantic_contract_matches(
            ROOT,
            module,
            [
                (
                    route.qualified_specification,
                    route.qualified_evidence,
                    route.evidence_mode,
                )
                for route in requested.values()
            ],
            build_input_provider=build_input_provider,
        )
    except Exception:  # noqa: BLE001 - unavailable current Lean evidence fails closed.
        transparency_checks = {}
        meta_matches = {}

    for source_key, route in requested.items():
        transparency = transparency_checks.get(route.qualified_specification)
        if not isinstance(transparency, dict) or transparency.get("passes") is not True:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` contract-backed schema-3 "
                    "surface has no current Lean-AST transitive transparency receipt for "
                    "its independently written Spec",
                )
            )
            continue
        route_key = (
            route.qualified_specification,
            route.qualified_evidence,
            route.evidence_mode,
        )
        if meta_matches.get(route_key) is not True:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` contract-backed schema-3 "
                    "surface has no current Lean-Meta exact evidence-to-Spec proof",
                )
            )
            continue
        routes[source_key] = route
    return routes, findings


def paper_statement_map_semantic_surface_findings(
    paper_id: str,
    folder: Path,
    status: object,
    payload: dict[str, object],
    paper_declarations: dict[str, list[LeanDeclaration]],
    reviewed_declaration_keys: set[tuple[Path, int, str]],
    *,
    presentation_hygiene: bool = False,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    run_context: PaperCloseoutRunContext | None = None,
) -> list[Finding]:
    """Check opt-in source-map semantic surfaces on explicit direct routes.

    Schema-3 routes are structural closeout checks over current elaborated
    Lean surfaces.  Legacy schema-1/2 token and term matching is presentation
    hygiene only: exact source contracts and source-record evidence, rather
    than a familiar vocabulary, supply default semantic credit.
    """

    statement_map = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    severity = completed_status_finding_severity(status)
    findings: list[Finding] = []
    try:
        from scripts.audit_evidence_integrity import semantic_surface_validation_errors
    except Exception as error:  # noqa: BLE001 - source-fidelity audit fails closed.
        return [
            Finding(
                "ERROR",
                statement_map,
                f"`{paper_id}` semantic-surface schema audit could not run: {error}",
            )
        ]

    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return findings
    contract_routes, contract_route_findings = semantic_contract_schema3_surface_routes(
        paper_id,
        folder,
        status,
        payload,
        paper_declarations,
        reviewed_declaration_keys,
        build_input_provider=build_input_provider,
        run_context=run_context,
    )
    findings.extend(contract_route_findings)
    manifest_requests: list[SemanticSurfaceManifestRequest] = []
    paper_interface_path = (folder / "PaperInterface.lean").resolve()
    for raw_source_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict) or "semantic_surface" not in raw_item:
            continue
        source_key = str(raw_source_key)
        raw_surface = raw_item.get("semantic_surface")
        validation_errors = semantic_surface_validation_errors(raw_surface)
        if validation_errors:
            for error in validation_errors:
                findings.append(
                    Finding(
                        severity,
                        statement_map,
                        f"`{paper_id}` source item `{source_key}` {error}",
                    )
                )
            continue
        assert isinstance(raw_surface, dict)

        direct_routes = explicit_source_coverage_declaration_names(raw_item)
        if direct_routes is None:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` has malformed explicit "
                    "source-coverage declaration routing for semantic_surface",
                )
            )
            continue
        if not direct_routes:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` semantic_surface requires an "
                    "explicit direct Lean route; aliases are navigation-only metadata",
                )
            )
            continue

        for route in direct_routes:
            resolved = resolve_declaration_name(paper_declarations, route)
            if len(resolved) != 1:
                # A route is paper-facing only through PaperInterface.lean.
                # Implementation modules may retain a same-named helper; do
                # not turn that harmless duplicate into an ambiguity that
                # hides the visible row from semantic-surface enforcement.
                visible = [
                    declaration
                    for declaration in resolved
                    if declaration.path.resolve() == paper_interface_path
                ]
                if len(visible) == 1:
                    resolved = visible
            if len(resolved) != 1:
                findings.append(
                    Finding(
                        severity,
                        statement_map,
                        f"`{paper_id}` source item `{source_key}` semantic_surface route "
                        f"`{route}` must resolve to exactly one paper-local declaration",
                    )
                )
                continue
            declaration = resolved[0]
            if declaration_key(declaration) not in reviewed_declaration_keys:
                findings.append(
                    Finding(
                        severity,
                        statement_map,
                        f"`{paper_id}` source item `{source_key}` semantic_surface route "
                        f"`{route}` is outside the configured reviewed/assumption surface",
                    )
                )
                continue
            if presentation_hygiene and schema_version_is_supported(
                raw_surface.get("schema"), {1, 2}
            ):
                for mismatch in semantic_surface_signature_mismatches(
                    declaration, raw_surface
                ):
                    findings.append(
                        Finding(
                            severity,
                            statement_map,
                            f"`{paper_id}` source item `{source_key}` semantic_surface route "
                            f"`{route}` {mismatch}",
                        )
                    )
            if schema_version_is_exact(
                raw_surface.get("schema"), 3
            ) and declaration.path.resolve() != paper_interface_path:
                findings.append(
                    Finding(
                        severity,
                        statement_map,
                        f"`{paper_id}` source item `{source_key}` semantic_surface route "
                        f"`{route}` must be declared in PaperInterface.lean for schema-3 review",
                    )
                )
                continue
            if schema_version_is_supported(raw_surface.get("schema"), {2, 3}):
                contract_route = (
                    contract_routes.get(source_key)
                    if schema_version_is_exact(raw_surface.get("schema"), 3)
                    else None
                )
                manifest_declaration = (
                    contract_route.specification
                    if contract_route is not None
                    else declaration
                )
                qualified = (
                    contract_route.qualified_specification
                    if contract_route is not None
                    else qualified_declaration_identity(manifest_declaration)
                )
                if not qualified:
                    findings.append(
                        Finding(
                            severity,
                            statement_map,
                            f"`{paper_id}` source item `{source_key}` semantic_surface route "
                            f"`{route}` has no namespace-qualified Lean identity for its "
                            "conclusion-shape audit",
                        )
                    )
                else:
                    manifest_requests.append(
                        SemanticSurfaceManifestRequest(
                            source_key=source_key,
                            route=route,
                            declaration=manifest_declaration,
                            qualified_manifest_name=qualified,
                            raw_surface=raw_surface,
                            contract_specification=contract_route is not None,
                        )
                    )

    def unavailable_outer_binder_digest(_manifest: object) -> str:
        return ""

    manifests: dict[str, dict[str, object]] = {}
    signature_manifest_outer_binder_digest: Callable[[object], str] = (
        unavailable_outer_binder_digest
    )
    if manifest_requests:
        requested_names = sorted(
            {
                request.qualified_manifest_name
                for request in manifest_requests
                if request.qualified_manifest_name
            }
        )
        try:
            from scripts.lean_signature_manifest import (
                paper_local_module_names,
                run_lean_signature_manifests,
                signature_manifest_outer_binder_digest,
            )
            manifests = run_lean_signature_manifests(
                ROOT,
                f"{folder.name}.PaperInterface",
                requested_names,
                semantic_dependency_modules=paper_local_module_names(
                    ROOT, folder, provider=build_input_provider
                ),
                build_input_provider=build_input_provider,
            )
        except Exception:  # noqa: BLE001 - high-assurance contracts fail closed.
            manifests = {}

    for request in manifest_requests:
        source_key = request.source_key
        route = request.route
        raw_surface = request.raw_surface
        qualified = request.qualified_manifest_name
        manifest = manifests.get(qualified)
        if request.contract_specification:
            manifest = semantic_contract_spec_definition_value_manifest(manifest)
            if manifest is None:
                findings.append(
                    Finding(
                        severity,
                        statement_map,
                        f"`{paper_id}` source item `{source_key}` semantic_surface route "
                        f"`{route}` has no current transparent Spec definition-value manifest",
                    )
                )
                continue
        if schema_version_is_exact(raw_surface.get("schema"), 3):
            expected_outer_binder_digest = str(
                raw_surface.get("outer_binder_sha256") or ""
            )
            actual_outer_binder_digest = (
                signature_manifest_outer_binder_digest(manifest)
                if isinstance(manifest, dict)
                else ""
            )
            if actual_outer_binder_digest != expected_outer_binder_digest:
                findings.append(
                    Finding(
                        severity,
                        statement_map,
                        f"`{paper_id}` source item `{source_key}` semantic_surface route "
                        f"`{route}` has a changed outer elaborated binder interface "
                        f"(expected {expected_outer_binder_digest or '<missing>'}, "
                        f"current {actual_outer_binder_digest or '<unavailable>'})",
                    )
                )
            mismatches = semantic_surface_result_pattern_mismatches(
                manifest, raw_surface
            )
        else:
            mismatches = semantic_surface_conclusion_component_mismatches(
                manifest, raw_surface
            )
        for mismatch in mismatches:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source item `{source_key}` semantic_surface route "
                    f"`{route}` {mismatch}",
                )
            )
    return findings


def _qualified_contract_declaration_name(
    declaration_index: dict[str, list[LeanDeclaration]], raw_name: str
) -> str:
    """Resolve one route to its unique namespace-qualified Lean name."""

    resolved = resolve_declaration_name(declaration_index, raw_name)
    if len(resolved) != 1:
        return ""
    target_key = declaration_key(resolved[0])
    if "." in raw_name and raw_name in declaration_index:
        exact = resolve_declaration_name(declaration_index, raw_name)
        if len(exact) == 1 and declaration_key(exact[0]) == target_key:
            return raw_name
    candidates = {
        name
        for name, declarations in declaration_index.items()
        if "." in name
        and any(declaration_key(declaration) == target_key for declaration in declarations)
    }
    if len(candidates) == 1:
        return next(iter(candidates))
    if not candidates and "." not in raw_name and raw_name in declaration_index:
        # A declaration at Lean's root namespace has a valid unqualified route.
        return raw_name
    return ""


def configured_source_proof_fidelity_path(
    folder: Path, status_payload: dict[str, object]
) -> Path | None:
    """Resolve the configured fidelity ledger through the shared path guard."""

    review_surface = status_payload.get("review_surface")
    config = (
        review_surface.get("source_proof_fidelity_review")
        if isinstance(review_surface, dict)
        else None
    )
    if not isinstance(config, dict):
        organized = folder / PAPER_AUDIT_DIR / "source_proof_fidelity.json"
        return organized if organized.exists() else folder / "source_proof_fidelity.json"
    try:
        from scripts.audit_evidence_integrity import source_proof_fidelity_ledger_path
        path, error = source_proof_fidelity_ledger_path(folder, status_payload)
    except Exception:  # noqa: BLE001 - callers fail closed on missing evidence.
        return None
    return path if not error else None


SEMANTIC_CONTRACT_SPEC_STRUCTURE_RE = re.compile(
    r"(?:∀|∃|∧|∨|↔|→|=|≠|≤|≥|<|>|∈|∉|\bif\b|\bmatch\b|∫|∑)"
)


def semantic_contract_spec_structure_error(
    declaration_index: dict[str, list[LeanDeclaration]],
    spec_declaration: LeanDeclaration,
    *,
    require_visible_syntax: bool = True,
) -> str:
    """Reject a nontransparent or structurally empty contract Spec.

    This is deliberately name-independent.  Circularity is established by
    the current Lean-AST transparency receipt, which follows elaborated
    declaration dependencies rather than guessing from a theorem's spelling.
    The historical v10 lane also requires visible surface syntax as a cheap
    review aid.  The atom-level v11 lane can instead use the complete
    elaborated closure plus source-to-component bindings, so an atomic but
    transparent predicate is not rejected merely for its printed syntax.
    """

    if spec_declaration.kind not in {"def", "abbrev"}:
        return (
            "specification must be a manually transparent `def` or `abbrev` "
            "with a Prop body; inductive/opaque proposition packages cannot "
            "serve as a semantic-contract closeout Spec"
        )
    if declaration_result_type_text(spec_declaration.source) != "Prop":
        return "specification must explicitly declare result type `Prop`"

    body = lean_code_text(declaration_body(spec_declaration.source)).strip()
    if not body:
        return "specification has no transparent proposition body"
    if body.startswith("by") and require_visible_syntax:
        return "specification body must state a proposition, not construct a proof/certificate"
    normalized_body = re.sub(r"\s+", " ", body).strip()
    if normalized_body in {"True", "False", "(True)", "(False)"}:
        return "specification body is a trivial truth value rather than a source-facing proposition"

    alias_target = alias_target_name(spec_declaration.source)
    if alias_target is not None:
        targets = resolve_declaration_name(declaration_index, alias_target)
        if any(target.kind in {"theorem", "lemma"} for target in targets):
            return (
                "specification is a trivial alias of a theorem/lemma; write the "
                "source proposition independently"
            )
        return (
            "specification is a trivial declaration alias; write the source "
            "proposition independently"
        )

    if require_visible_syntax and not SEMANTIC_CONTRACT_SPEC_STRUCTURE_RE.search(body):
        return (
            "specification body has no visible logical/mathematical structure; "
            "a bare predicate/certificate wrapper cannot serve as a semantic closeout Spec"
        )
    return ""


_REALIZATION_EXTERNALLY_RESOLVABLE_FAILURE_TAGS = frozenset(
    {"unregistered_workspace_dependency", "unregistered_imported_dependency"}
)


def _realization_json_sha256(value: object) -> str:
    """Hash a structural realization fragment without using route spellings."""

    return hashlib.sha256(_canonical_json_key(value).encode("utf-8")).hexdigest()


def semantic_contract_spec_surface_component_sha256s(
    surface: object,
    *,
    root_surface_sha256: object,
) -> set[str]:
    """Return name-free canonical subexpression/path identities for one Spec.

    The root surface is always selectable, while every canonical Lean
    subexpression with a structural ``tag`` supplies a more precise repair
    handoff target.  Paths are generated from JSON structure, never from
    binder, declaration, or source-item names.
    """

    if not isinstance(surface, dict):
        return set()
    root = str(root_surface_sha256 or "").strip().lower()
    if not re.fullmatch(r"[0-9a-f]{64}", root):
        return set()
    components = {root}

    def visit(value: object, path: str) -> None:
        if isinstance(value, dict):
            if isinstance(value.get("tag"), str) and value.get("tag"):
                components.add(
                    _realization_json_sha256(
                        {
                            "schema": SOURCE_SPEC_CORRESPONDENCE_SCHEMA,
                            "structural_path": path,
                            "canonical": value,
                        }
                    )
                )
            for key in sorted(value):
                visit(value[key], f"{path}/{key}")
        elif isinstance(value, list):
            for index, child in enumerate(value):
                visit(child, f"{path}/{index}")

    raw_binders = surface.get("binder_domains")
    if isinstance(raw_binders, list):
        for index, raw_binder in enumerate(raw_binders):
            if isinstance(raw_binder, dict):
                visit(raw_binder.get("canonical"), f"binder/{index}")
    visit(surface.get("body"), "body")
    return components


def semantic_contract_closure_node_component_sha256(node: object) -> str:
    """Return one name-free material-node identity from Lean's closure receipt."""

    if not isinstance(node, dict):
        return ""
    path = str(node.get("structural_path") or "").strip()
    role = str(node.get("node_role") or "").strip()
    origin = str(node.get("origin_class") or "").strip()
    identity = node.get("canonical_identity")
    if not path or not role or not origin or not isinstance(identity, dict):
        return ""
    return _realization_json_sha256(
        {
            "schema": SOURCE_SPEC_CORRESPONDENCE_SCHEMA,
            "structural_path": path,
            "node_role": role,
            "origin_class": origin,
            "canonical_identity": identity,
        }
    )


def semantic_contract_closure_environment_sha256(
    closure: object,
) -> str:
    """Bind a correspondence to narrow, relevant toolchain/terminal pins.

    The Lean helper's broad execution-context hash includes the entire
    workspace module inventory so it can conservatively classify origins.
    That is useful to execute a closure but inappropriate for item reuse: an
    unrelated paper build must not invalidate this Spec.  The helper therefore
    emits a separate module-context hash containing only the dependency
    toolchain/package pins and exact module artifacts reached by this current
    elaborated closure.  This wrapper intentionally never substitutes the
    broad context hash.
    """

    if not isinstance(closure, dict):
        return ""
    value = str(closure.get("closure_module_context_sha256") or "").strip().lower()
    return value if re.fullmatch(r"[0-9a-f]{64}", value) else ""


def _realization_required_node_components(
    closure: dict[str, object],
) -> tuple[dict[str, dict[str, object]], list[str]]:
    """Return manual material nodes and receipt-shape errors.

    A paper definition/inductive that Lean fully expands is a checked
    transparent derivation, so its commitments remain covered by the
    source-atom-to-Spec bindings rather than requiring a duplicate handwritten
    row.  Every terminal outside the approved foundation remains explicit.
    """

    raw_nodes = closure.get("nodes")
    if not isinstance(raw_nodes, list):
        return {}, ["Lean closure has no node list"]
    required: dict[str, dict[str, object]] = {}
    errors: list[str] = []
    for raw_node in raw_nodes:
        if not isinstance(raw_node, dict):
            errors.append("Lean closure has a malformed node")
            continue
        component = semantic_contract_closure_node_component_sha256(raw_node)
        origin = str(raw_node.get("origin_class") or "").strip()
        role = str(raw_node.get("node_role") or "").strip()
        if not component or not origin or not role:
            errors.append("Lean closure has a malformed material node identity")
            continue
        if origin in {"foundation", "foreign_model_definition"}:
            continue
        # Every production paper-owned node has already been recursively
        # traversed and inlined into the canonical Spec surface. Unsafe paper
        # terminals remain rejection entries in the failure ledger below.
        if origin == "paper":
            continue
        if component in required:
            errors.append("Lean closure has duplicate material structural node identity")
            continue
        required[component] = raw_node
    return required, errors


def source_spec_correspondence_runtime_errors(
    raw_item: object,
    closure: object,
) -> list[str]:
    """Validate current Lean realization evidence against one strict record.

    This is the semantic gate: source atom bindings must point into the actual
    current canonical Spec surface, and every nonfoundation terminal must have
    a current disposition.  The helper's origin/failure judgments come from
    Lean Meta; Python does not infer safety from a declaration name, a record
    shape, a data classification, or a function signature spelling.
    """

    if not isinstance(raw_item, dict):
        return ["source item is malformed"]
    correspondence = raw_item.get(SOURCE_SPEC_CORRESPONDENCE_KEY)
    static_errors = source_spec_correspondence_validation_errors(
        correspondence,
        raw_atoms=raw_item.get(SOURCE_CLAIM_ATOMS_KEY),
        raw_contract=raw_item.get("semantic_contract"),
    )
    if static_errors:
        return ["static realization correspondence is invalid: " + static_errors[0]]
    assert isinstance(correspondence, dict)
    if not isinstance(closure, dict):
        return ["no current Lean-owned complete Spec closure receipt"]
    errors: list[str] = []
    surface = closure.get("surface")
    closure_sha = str(closure.get("sha256") or "").strip().lower()
    surface_sha = str(closure.get("surface_sha256") or "").strip().lower()
    expected_environment = semantic_contract_closure_environment_sha256(closure)
    for field, actual in (
        ("spec_closure_sha256", closure_sha),
        ("spec_surface_sha256", surface_sha),
        ("closure_environment_sha256", expected_environment),
    ):
        recorded = str(correspondence.get(field) or "").strip().lower()
        if not re.fullmatch(r"[0-9a-f]{64}", actual) or recorded != actual:
            errors.append(
                f"{field} is stale for the current Lean-owned Spec realization receipt"
            )
    if not isinstance(surface, dict):
        return errors + ["current Lean closure did not expose a canonical Spec surface"]
    surface_mode = str(closure.get("surface_mode") or "").strip()
    if surface_mode not in {
        "closure_expanded",
        "terminal_fallback",
        "closure_fingerprints",
        "terminal_fingerprints",
        "lean_dependency_fingerprint",
    }:
        errors.append("current Lean closure has an unsupported surface mode")
    source_components = semantic_contract_spec_surface_component_sha256s(
        surface, root_surface_sha256=surface_sha
    )
    if not source_components:
        errors.append("current Lean closure has no auditable canonical Spec components")
    raw_bindings = correspondence.get("source_atom_bindings")
    if isinstance(raw_bindings, list):
        for index, raw_binding in enumerate(raw_bindings):
            if not isinstance(raw_binding, dict):
                continue
            raw_components = raw_binding.get("spec_component_sha256s")
            if not isinstance(raw_components, list):
                continue
            for component in raw_components:
                component_sha = str(component).strip().lower()
                if component_sha not in source_components:
                    errors.append(
                        "source_atom_bindings["
                        + str(index)
                        + "] names a Spec component absent from the current canonical surface"
                    )

    required_nodes, node_shape_errors = _realization_required_node_components(closure)
    errors.extend(node_shape_errors)
    raw_dispositions = correspondence.get("closure_node_dispositions")
    dispositions: dict[str, dict[str, object]] = {}
    if isinstance(raw_dispositions, list):
        for raw_disposition in raw_dispositions:
            if not isinstance(raw_disposition, dict):
                continue
            component = str(raw_disposition.get("closure_component_sha256") or "").strip().lower()
            if re.fullmatch(r"[0-9a-f]{64}", component):
                dispositions[component] = raw_disposition
    expected_components = set(required_nodes)
    actual_components = set(dispositions)
    missing_components = sorted(expected_components - actual_components)
    extra_components = sorted(actual_components - expected_components)
    if missing_components:
        errors.append(
            "material closure node(s) lack a source-contract disposition: "
            + ", ".join(missing_components[:4])
            + ("; ..." if len(missing_components) > 4 else "")
        )
    if extra_components:
        errors.append(
            "closure_node_dispositions include component(s) absent from the current material closure: "
            + ", ".join(extra_components[:4])
            + ("; ..." if len(extra_components) > 4 else "")
        )
    for component, node in required_nodes.items():
        disposition = dispositions.get(component)
        if disposition is None:
            continue
        origin = str(node.get("origin_class") or "").strip()
        if origin in {"workspace", "external"}:
            expected_pin = str(node.get("pinned_declaration_identity_sha256") or "").strip().lower()
            recorded_pin = str(
                disposition.get("pinned_declaration_identity_sha256") or ""
            ).strip().lower()
            if not expected_pin or recorded_pin != expected_pin:
                errors.append(
                    "workspace/external closure terminal has no matching explicit pinned declaration disposition"
                )
            if not isinstance(disposition.get("semantic_basis"), dict):
                errors.append(
                    "workspace/external closure terminal needs an explicit version-pinned semantic_basis"
                )
        elif origin == "unresolved":
            errors.append("unresolved closure origin is never a realizable semantic terminal")

    raw_failures = closure.get("failures")
    if not isinstance(raw_failures, list):
        errors.append("current Lean closure has no failure ledger")
    else:
        for raw_failure in raw_failures:
            if not isinstance(raw_failure, dict):
                errors.append("current Lean closure has a malformed failure entry")
                continue
            tag = str(raw_failure.get("tag") or "").strip()
            if tag not in _REALIZATION_EXTERNALLY_RESOLVABLE_FAILURE_TAGS:
                errors.append(
                    "current Lean closure has a non-resolvable semantic dependency failure: "
                    + (tag or "unknown")
                )
    return errors


def paper_statement_map_semantic_contract_findings(
    paper_id: str,
    folder: Path,
    status: object,
    payload: dict[str, object],
    paper_declarations: dict[str, list[LeanDeclaration]],
    _reviewed_names: set[str],
    status_payload: dict[str, object],
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> list[Finding]:
    """Lean-check opt-in source-map proof and refutation contracts."""

    statement_map = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    severity = completed_status_finding_severity(status)
    findings: list[Finding] = []
    build_input_provider = (
        run_context.build_input_provider if run_context is not None else None
    )
    try:
        from scripts.audit_evidence_integrity import (
            SEMANTIC_CONTRACT_SCHEMAS,
            semantic_contract_inventory_findings,
            semantic_contract_validation_errors,
        )
        structural_findings = semantic_contract_inventory_findings(
            folder,
            str(status or ""),
            context=(
                run_context.evidence_context
                if run_context is not None
                else None
            ),
        )
    except Exception as error:  # noqa: BLE001 - semantic contracts fail closed.
        return [
            Finding(
                "ERROR",
                statement_map,
                f"`{paper_id}` semantic-contract schema audit could not run: {error}",
            )
        ]
    for finding in structural_findings:
        raw_path = Path(str(finding.path))
        path = raw_path if raw_path.is_absolute() else ROOT / raw_path
        findings.append(Finding(str(finding.severity), path, str(finding.message)))

    raw_items = payload.get("items")
    items = raw_items if isinstance(raw_items, dict) else {}
    review_surface = status_payload.get("review_surface")
    reviewed_declaration_keys: set[tuple[Path, int, str]] = set()
    if isinstance(review_surface, dict):
        reviewed_source_paths = {
            review_surface_source_file_path(folder, review_surface).resolve(),
            proof_endpoint_source_file_path(folder, review_surface).resolve(),
            assumption_source_file_path(folder, review_surface).resolve(),
        }
        for field in ("include_names", "assumption_names"):
            raw_names = review_surface.get(field)
            if not isinstance(raw_names, list):
                continue
            for raw_name in raw_names:
                if not isinstance(raw_name, str) or not raw_name.strip():
                    continue
                resolved_review_name = resolve_declaration_name(
                    paper_declarations, raw_name.strip()
                )
                # A paper can retain a same-short-name implementation helper.
                # The configured human review source, rather than short-name
                # ambiguity, determines the reviewed declaration.
                if len(resolved_review_name) != 1:
                    resolved_review_name = [
                        declaration
                        for declaration in resolved_review_name
                        if declaration.path.resolve() in reviewed_source_paths
                    ]
                if len(resolved_review_name) == 1:
                    reviewed_declaration_keys.add(
                        declaration_key(resolved_review_name[0])
                    )
        # The human review row is the transparent Spec in PaperInterface.  A
        # paired theorem/lemma may live in a separate paper-local proof module
        # without becoming a second source claim.  Admit precisely those
        # endpoints here; `check_proposition_spec_routes` subsequently uses
        # Lean Meta to require that each endpoint has exactly its paired Spec
        # type.  No other declaration in the proof module receives review
        # credit merely because of its file location.
        raw_pairs = review_surface.get("proposition_spec_proofs")
        include_names = {
            str(name).strip()
            for name in review_surface.get("include_names", [])
            if isinstance(name, str) and name.strip()
        }
        if isinstance(raw_pairs, dict):
            proof_path = proof_endpoint_source_file_path(folder, review_surface).resolve()
            source_path = review_surface_source_file_path(folder, review_surface).resolve()
            for raw_spec, raw_proof in raw_pairs.items():
                if not isinstance(raw_spec, str) or not isinstance(raw_proof, str):
                    continue
                spec_name = raw_spec.strip()
                proof_name = raw_proof.strip()
                if not spec_name or not proof_name or spec_name not in include_names:
                    continue
                specs = resolve_declaration_name(paper_declarations, spec_name)
                proofs = resolve_declaration_name(paper_declarations, proof_name)
                if len(specs) != 1:
                    specs = [decl for decl in specs if decl.path.resolve() == source_path]
                if len(proofs) != 1:
                    proofs = [decl for decl in proofs if decl.path.resolve() == proof_path]
                if (
                    len(specs) == 1
                    and declaration_key(specs[0]) in reviewed_declaration_keys
                    and len(proofs) == 1
                    and proofs[0].path.resolve() == proof_path
                    and proofs[0].kind in LEAN_PROOF_DECLARATION_KINDS
                ):
                    reviewed_declaration_keys.add(declaration_key(proofs[0]))
    contract_schema = payload.get("semantic_contract_schema")
    strict_realization = source_spec_correspondence_requested(
        status_payload,
        payload,
        folder=folder,
    )
    # The source inventory decides which source claims may mint a full-surface
    # occurrence receipt.  Do this once, inside the same exact evidence
    # transaction that will run Lean below.  It is intentionally not inferred
    # from a Spec, declaration, binder, or source-item label.
    strict_source_scope_keys: frozenset[str] = frozenset()
    if strict_realization:
        try:
            strict_inventory, strict_inventory_findings = (
                semantic_contract_closeout_bridge_inventory(
                    folder,
                    str(status or ""),
                    context=(
                        run_context.evidence_context
                        if run_context is not None
                        else None
                    ),
                )
            )
            if strict_inventory is not None and not strict_inventory_findings:
                strict_source_scope_keys = frozenset(
                    strict_inventory.contract_item_keys
                )
                if run_context is not None:
                    run_context.record_strict_source_spec_correspondence_scope_keys(
                        strict_source_scope_keys
                    )
        except Exception:
            # The receipt is a closeout capability.  An unavailable inventory
            # withholds it; fail closed below before starting obsolete Lean
            # fallback work.
            strict_source_scope_keys = frozenset()
        if not strict_source_scope_keys:
            # A v11 source-to-Spec paper cannot recover from an invalid strict
            # inventory by replaying the legacy transparency and manifest
            # lanes.  Those programs do not repair missing/ambiguous source
            # obligations, and running them first turns a cheap metadata error
            # into minutes of needless Lean imports.  Preserve any precise
            # structural findings already collected and otherwise emit one
            # explicit fail-closed diagnostic.
            if not findings:
                findings.append(
                    Finding(
                        severity,
                        statement_map,
                        f"`{paper_id}` strict source-to-Spec inventory is unavailable; "
                        "repair the source inventory before running Lean realization",
                    )
                )
            return findings
    requested: dict[str, tuple[str, str, str, str, dict[str, object]]] = {}
    defect_ids_by_item: dict[str, set[str]] = {}
    for source_key, raw_item in items.items():
        if not isinstance(raw_item, dict) or "semantic_contract" not in raw_item:
            continue
        raw_contract = raw_item.get("semantic_contract")
        if semantic_contract_validation_errors(
            raw_contract,
            schema=(
                contract_schema
                if schema_version_is_supported(
                    contract_schema, SEMANTIC_CONTRACT_SCHEMAS
                )
                else SEMANTIC_CONTRACT_SCHEMA
            ),
        ):
            continue
        assert isinstance(raw_contract, dict)
        spec_name = str(raw_contract["spec_declaration"]).strip()
        evidence_name = str(raw_contract["evidence_declaration"]).strip()
        mode = str(raw_contract["evidence_mode"]).strip()
        shape = str(raw_contract["semantic_shape"]).strip()
        spec_resolved = resolve_declaration_name(paper_declarations, spec_name)
        evidence_resolved = resolve_declaration_name(paper_declarations, evidence_name)
        if len(spec_resolved) != 1:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` semantic contract `{source_key}` does not resolve "
                    f"spec_declaration `{spec_name}` to one paper-local declaration",
                )
            )
            continue
        if len(evidence_resolved) != 1:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` semantic contract `{source_key}` does not resolve "
                    f"evidence_declaration `{evidence_name}` to one paper-local declaration",
                )
            )
            continue
        if spec_resolved[0].kind not in SEMANTIC_CONTRACT_SPEC_KINDS:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` semantic contract `{source_key}` specification must be "
                    "a transparent def/abbrev `Spec : Prop`",
                )
            )
            continue
        if evidence_resolved[0].kind not in SEMANTIC_CONTRACT_EVIDENCE_KINDS:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` semantic contract `{source_key}` evidence must be a theorem/lemma",
                )
            )
            continue
        independence_error = semantic_contract_spec_structure_error(
            paper_declarations,
            spec_resolved[0],
            require_visible_syntax=not strict_realization,
        )
        if independence_error:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` semantic contract `{source_key}` {independence_error}",
                )
            )
            continue
        unreviewed = [
            name
            for name, resolved in (
                (spec_name, spec_resolved[0]),
                (evidence_name, evidence_resolved[0]),
            )
            if declaration_key(resolved) not in reviewed_declaration_keys
        ]
        if unreviewed:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` semantic contract `{source_key}` uses declaration(s) "
                    "outside the configured review surface: " + ", ".join(unreviewed),
                )
            )
            continue
        qualified_spec = _qualified_contract_declaration_name(
            paper_declarations, spec_name
        )
        qualified_evidence = _qualified_contract_declaration_name(
            paper_declarations, evidence_name
        )
        if not qualified_spec or not qualified_evidence:
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` semantic contract `{source_key}` could not determine "
                    "unique namespace-qualified Lean routes",
                )
            )
            continue
        requested[str(source_key)] = (
            qualified_spec,
            qualified_evidence,
            mode,
            shape,
            raw_item,
        )
        raw_defect_ids = raw_item.get("source_defect_ids")
        defect_ids_by_item[str(source_key)] = {
            str(value).strip()
            for value in (raw_defect_ids if isinstance(raw_defect_ids, list) else [])
            if isinstance(value, str) and value.strip()
        }

    transparency_checks: dict[str, dict[str, object]] = {}
    closure_manifests: dict[str, dict[str, object]] = {}
    strict_specs = sorted(
        {
            spec
            for source_key, (spec, _evidence, _mode, _shape, _raw_item) in (
                requested.items()
            )
            if source_key in strict_source_scope_keys
        }
    )
    semantic_authority_realization_errors: list[str] | None = None
    correspondence_authority_errors: list[str] | None = None
    if strict_realization and strict_source_scope_keys:
        semantic_authority_realization_errors = (
            semantic_authority_source_spec_correspondence_errors(
                ROOT,
                folder,
                payload,
                [
                    (source_key, raw_item)
                    for source_key, (
                        _spec,
                        _evidence,
                        _mode,
                        _shape,
                        raw_item,
                    ) in requested.items()
                    if source_key in strict_source_scope_keys
                ],
                evidence_context=(
                    run_context.evidence_context
                    if run_context is not None
                    else None
                ),
            )
        )
        correspondence_authority_errors = (
            semantic_authority_realization_errors
            if semantic_authority_realization_errors is not None
            else graph_authority_source_spec_correspondence_errors(
                ROOT,
                folder,
                payload,
                [
                    (source_key, raw_item)
                    for source_key, (
                        _spec,
                        _evidence,
                        _mode,
                        _shape,
                        raw_item,
                    ) in requested.items()
                    if source_key in strict_source_scope_keys
                ],
                evidence_context=(
                    run_context.evidence_context
                    if run_context is not None
                    else None
                ),
            )
        )
    semantic_authority_realization_current = (
        semantic_authority_realization_errors == []
    )
    correspondence_authority_current = correspondence_authority_errors == []
    graph_native_receipts: dict[str, dict[str, str]] = {}
    if (
        correspondence_authority_current
        and run_context is not None
        and run_context.current_v11_closeout
    ):
        graph_receipt_result = graph_native_source_spec_realization_receipts(
            ROOT,
            folder,
            payload,
            [
                (source_key, raw_item)
                for source_key, (
                    _spec,
                    _evidence,
                    _mode,
                    _shape,
                    raw_item,
                ) in requested.items()
                if source_key in strict_source_scope_keys
            ],
            evidence_context=run_context.evidence_context,
        )
        if graph_receipt_result is not None:
            graph_native_receipts, graph_receipt_errors = graph_receipt_result
            if graph_receipt_errors:
                correspondence_authority_current = False
                correspondence_authority_errors = graph_receipt_errors
                graph_native_receipts = {}
    if requested and not correspondence_authority_current:
        foreign_definitions: tuple[str, ...] = ()
        foreign_modules: tuple[str, ...] = ()
        foreign_scope_error = ""
        try:
            from scripts.lean_signature_manifest import (
                foreign_model_definition_scope,
                paper_local_module_names,
                run_lean_semantic_contract_closure_manifests,
                run_lean_semantic_contract_transparency_checks,
            )
            from scripts.review_dashboard import review_source_file, review_source_module
            source_path = review_source_file(folder)
            review_module = review_source_module(folder, source_path)
            paper_modules = paper_local_module_names(
                ROOT, folder, provider=build_input_provider
            )
            foreign_definitions, foreign_modules, foreign_scope_error = (
                foreign_model_definition_scope(ROOT, folder)
            )
            if foreign_scope_error:
                findings.append(
                    Finding(
                        severity,
                        folder / "status.json",
                        f"`{paper_id}` foreign model definition scope is invalid: "
                        + foreign_scope_error,
                    )
                )
            transparency_checks = run_lean_semantic_contract_transparency_checks(
                ROOT,
                review_module,
                sorted(
                    {
                        spec
                        for spec, _evidence, _mode, _shape, _item in requested.values()
                    }
                ),
                paper_modules,
                build_input_provider=build_input_provider,
            )
            if (
                strict_realization
                and strict_specs
                and not foreign_scope_error
                and not correspondence_authority_current
            ):
                closure_manifests = run_lean_semantic_contract_closure_manifests(
                    ROOT,
                    review_module,
                    strict_specs,
                    paper_modules,
                    foreign_model_definitions=foreign_definitions,
                    foreign_model_modules=foreign_modules,
                    build_input_provider=build_input_provider,
                )
        except Exception:  # noqa: BLE001 - unavailable structural evidence fails closed.
            transparency_checks = {}
            closure_manifests = {}

    meta_matches: dict[tuple[str, str, str], bool] = {}
    if requested and not semantic_authority_realization_current:
        try:
            from scripts.lean_signature_manifest import run_lean_semantic_contract_matches
            from scripts.review_dashboard import (
                review_proof_module,
                review_source_file,
                review_source_module,
            )
            source_path = review_source_file(folder)
            meta_matches = run_lean_semantic_contract_matches(
                ROOT,
                # Semantic Specs remain expanded from PaperInterface, while
                # proof endpoints are checked from their configured
                # paper-local proof module.  Their location is immaterial;
                # the exact Spec/evidence relationship is the authority.
                review_proof_module(folder, source_path),
                [
                    (spec, evidence, mode)
                    for spec, evidence, mode, _shape, _item in requested.values()
                ],
                build_input_provider=build_input_provider,
            )
        except Exception:  # noqa: BLE001 - missing Meta evidence fails below.
            meta_matches = {}

    checked_items: set[str] = set()
    for source_key, (spec, evidence, mode, shape, raw_item) in requested.items():
        transparency = transparency_checks.get(spec)
        transparency_accepted = correspondence_authority_current or (
            isinstance(transparency, dict) and transparency.get("passes") is True
        )
        terminal_policy_errors: list[str] = []
        if (
            not transparency_accepted
            and isinstance(transparency, dict)
            and str(transparency.get("failure_tag") or "").strip()
            == "recursive_executable_terminal"
        ):
            terminal_policy_errors = semantic_contract_executable_terminal_policy_errors(
                paper_id,
                folder,
                source_key=source_key,
                transparency=transparency,
                run_context=run_context,
            )
            transparency_accepted = not terminal_policy_errors
        if not transparency_accepted:
            failure_tag = (
                str(transparency.get("failure_tag") or "unavailable")
                if isinstance(transparency, dict)
                else "unavailable"
            )
            failure_declaration = (
                str(transparency.get("failure_declaration") or "")
                if isinstance(transparency, dict)
                else ""
            )
            diagnostic = (
                f" at `{failure_declaration}`" if failure_declaration else ""
            )
            terminal_diagnostic = (
                " Executable recursion candidates require an exact current direct "
                "source-model association, signature/dependency fingerprint, and "
                "complete semantic-model review: "
                + "; ".join(terminal_policy_errors[:2])
                + "."
                if terminal_policy_errors
                else ""
            )
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` semantic contract `{source_key}` ({shape}) has no "
                    "Lean-AST transitive transparency proof for its specification "
                    f"`{spec}`: `{failure_tag}`{diagnostic}. Paper-local opaque, axiom, "
                    "theorem, cyclic, unresolved, or fuel-exhausted semantic wrappers "
                    "cannot receive source-map credit."
                    + terminal_diagnostic,
                )
            )
            continue
        if (
            not semantic_authority_realization_current
            and meta_matches.get((spec, evidence, mode)) is not True
        ):
            expected = (
                "the exact specification"
                if mode == "proves"
                else (
                    "an exact definition-to-Spec equivalence"
                    if mode == "definitionally_realizes"
                    else "exactly `Not` the specification"
                )
            )
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` Lean Meta did not establish semantic contract `{source_key}` "
                    f"({shape}): evidence `{evidence}` must prove {expected} `{spec}`. "
                    "Extra premises, partial conjunctions, nearby executor bounds, post-transform "
                    "claims, ambiguous routes, and unavailable Meta results fail closed.",
                )
            )
            continue
        if strict_realization and source_key in strict_source_scope_keys:
            realization_errors = (
                []
                if correspondence_authority_current
                else source_spec_correspondence_runtime_errors(
                    raw_item, closure_manifests.get(spec)
                )
            )
            if realization_errors:
                findings.append(
                    Finding(
                        severity,
                        statement_map,
                        f"`{paper_id}` strict realization contract `{source_key}` is not current: "
                        + "; ".join(realization_errors[:4])
                        + ("; ..." if len(realization_errors) > 4 else ""),
                    )
                )
                continue
            # Reuse this just-validated Lean closure in the later occurrence
            # gate.  The projector rechecks every field against the exact
            # map, parent association, atom contexts, and component route, so
            # this is not a blanket source-map exemption.
            raw_contract = raw_item.get("semantic_contract")
            graph_receipt = graph_native_receipts.get(source_key)
            if (
                run_context is not None
                and isinstance(graph_receipt, Mapping)
                and isinstance(raw_contract, dict)
                and str(graph_receipt.get("spec_declaration") or "").strip()
                == spec
                and str(graph_receipt.get("evidence_declaration") or "").strip()
                == evidence
                and str(graph_receipt.get("evidence_mode") or "").strip()
                == mode
                and str(graph_receipt.get("semantic_shape") or "").strip()
                == shape
            ):
                run_context.record_strict_source_spec_correspondence_receipt(
                    StrictSourceSpecCorrespondenceReceipt(
                        source_item_key=source_key,
                        spec_declaration=spec,
                        evidence_declaration=evidence,
                        evidence_mode=mode,
                        semantic_shape=shape,
                        source_atoms_sha256=str(
                            graph_receipt["source_atoms_sha256"]
                        ),
                        item_identity_sha256=str(
                            graph_receipt["item_identity_sha256"]
                        ),
                        spec_closure_sha256=str(
                            graph_receipt["spec_closure_sha256"]
                        ),
                        spec_surface_sha256=str(
                            graph_receipt["spec_surface_sha256"]
                        ),
                        closure_environment_sha256=str(
                            graph_receipt["closure_environment_sha256"]
                        ),
                        authority="v11_graph_native_v1",
                    )
                )
                checked_items.add(source_key)
                continue
            raw_correspondence = raw_item.get(SOURCE_SPEC_CORRESPONDENCE_KEY)
            if (
                run_context is not None
                and source_key in strict_source_scope_keys
                and mode in {"proves", "definitionally_realizes"}
                and isinstance(raw_correspondence, dict)
                and isinstance(raw_contract, dict)
                and str(raw_contract.get("spec_declaration") or "").strip()
                == spec
                and str(raw_contract.get("evidence_declaration") or "").strip()
                == evidence
                and str(raw_contract.get("evidence_mode") or "").strip()
                == mode
                and str(raw_contract.get("semantic_shape") or "").strip()
                == shape
                and source_spec_correspondence_item_identity_sha256(
                    raw_contract, raw_correspondence
                )
                == str(raw_correspondence.get("item_identity_sha256") or "")
                .strip()
                .lower()
            ):
                receipt_values = (
                    str(raw_correspondence.get("source_atoms_sha256") or "")
                    .strip()
                    .lower(),
                    str(raw_correspondence.get("item_identity_sha256") or "")
                    .strip()
                    .lower(),
                    str(raw_correspondence.get("spec_closure_sha256") or "")
                    .strip()
                    .lower(),
                    str(raw_correspondence.get("spec_surface_sha256") or "")
                    .strip()
                    .lower(),
                    str(raw_correspondence.get("closure_environment_sha256") or "")
                    .strip()
                    .lower(),
                )
                if all(re.fullmatch(r"[0-9a-f]{64}", value) for value in receipt_values):
                    run_context.record_strict_source_spec_correspondence_receipt(
                        StrictSourceSpecCorrespondenceReceipt(
                            source_item_key=source_key,
                            spec_declaration=spec,
                            evidence_declaration=evidence,
                            evidence_mode=mode,
                            semantic_shape=shape,
                            source_atoms_sha256=receipt_values[0],
                            item_identity_sha256=receipt_values[1],
                            spec_closure_sha256=receipt_values[2],
                            spec_surface_sha256=receipt_values[3],
                            closure_environment_sha256=receipt_values[4],
                        )
                    )
        checked_items.add(source_key)

    if schema_version_is_supported(contract_schema, SEMANTIC_CONTRACT_SCHEMAS):
        fidelity_path = configured_source_proof_fidelity_path(folder, status_payload)
        fidelity = (
            run_context.exact_json_payload(fidelity_path)
            if fidelity_path is not None and run_context is not None
            else load_json_object(fidelity_path) if fidelity_path is not None else None
        )
        fidelity = fidelity or {}
        raw_defects = fidelity.get("defects")
        repaired_ids = {
            str(defect.get("id") or "").strip()
            for defect in (raw_defects if isinstance(raw_defects, list) else [])
            if isinstance(defect, dict)
            and str(defect.get("resolution") or "").strip() == "repaired_in_lean"
            and str(defect.get("id") or "").strip()
        }
        for defect_id in sorted(repaired_ids):
            if any(
                source_key in checked_items
                and defect_id in defect_ids_by_item.get(source_key, set())
                for source_key in requested
            ):
                continue
            findings.append(
                Finding(
                    severity,
                    statement_map,
                    f"`{paper_id}` source-proof defect `{defect_id}` is `repaired_in_lean` "
                    "without a successfully Lean-checked source-map semantic contract",
                )
            )
    if (
        run_context is not None
        and strict_source_scope_keys
        and strict_source_scope_keys.issubset(checked_items)
        and not findings
    ):
        run_context.record_semantic_contract_closeout_bridge(
            strict_source_scope_keys,
            _issuer=_SEMANTIC_CONTRACT_CLOSEOUT_BRIDGE_ISSUER,
        )
    return findings


def semantic_contract_precloseout_exact_contract_pairs(
    paper_id: str,
    folder: Path,
    status: object,
    status_payload: dict[str, object],
    paper_declarations: dict[str, list[LeanDeclaration]] | None = None,
) -> tuple[tuple[str, str], ...]:
    """Return exact direct/Spec pairs usable by the source-record precloseout lane.

    This is deliberately narrower than the final-closeout bridge below.  It is
    available *only* while a paper is ``partially formalized`` and is consumed
    solely by the source-record generator to avoid duplicate review of a
    direct statement binder and an alpha-equal transparent ``Spec`` binder.
    It neither changes dashboard behavior nor permits a blank statement or
    coverage sidecar to pass at partial status.

    A nonempty result means that the complete byte-pinned source inventory and
    every exact semantic contract are current, independently transparent, and
    Lean-Meta checked.  Declaration identities merely select the checked
    routes; callers must still compare generated binder surfaces before
    suppressing a source-record item.  Corrected targets and ambiguous pairs
    are excluded here even if their contracts otherwise validate.
    """

    status_text = str(status or "").strip()
    if status_text != "partially formalized":
        return ()
    if str(status_payload.get("status") or "").strip() != status_text:
        return ()

    try:
        from scripts.audit_evidence_integrity import (
            semantic_contract_closeout_bridge_inventory,
        )
        inventory, inventory_findings = semantic_contract_closeout_bridge_inventory(
            folder, status_text
        )
    except Exception:
        # This projection is an optimization only.  Any unavailable source
        # evidence leaves every ordinary input on the source-record surface.
        return ()
    if inventory is None or inventory_findings or not inventory.contract_item_keys:
        return ()

    statement_map = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    map_payload = load_json_object(statement_map)
    if not isinstance(map_payload, dict):
        return ()
    raw_items = map_payload.get("items")
    if not isinstance(raw_items, dict):
        return ()

    declarations = paper_declarations or paper_lean_declaration_index(folder)
    try:
        contract_findings = paper_statement_map_semantic_contract_findings(
            paper_id,
            folder,
            status_text,
            map_payload,
            declarations,
            set(),
            status_payload,
        )
    except Exception:
        return ()
    if contract_findings:
        return ()

    all_pairs_by_member: dict[str, set[tuple[str, str]]] = {}
    corrected_pairs: set[tuple[str, str]] = set()
    for raw_item in raw_items.values():
        if not isinstance(raw_item, dict) or raw_item.get("claim_bearing") is not True:
            continue
        raw_contract = raw_item.get("semantic_contract")
        if not isinstance(raw_contract, dict):
            continue
        evidence = _qualified_contract_declaration_name(
            declarations, str(raw_contract.get("evidence_declaration") or "")
        )
        spec = _qualified_contract_declaration_name(
            declarations, str(raw_contract.get("spec_declaration") or "")
        )
        if not evidence or not spec or evidence == spec:
            continue
        pair = (evidence, spec)
        all_pairs_by_member.setdefault(evidence, set()).add(pair)
        all_pairs_by_member.setdefault(spec, set()).add(pair)
        if (
            str(raw_item.get("coverage_status") or "").strip().lower()
            == "corrected_source_statement"
        ):
            corrected_pairs.add(pair)

    pairs: set[tuple[str, str]] = set()
    for source_key in inventory.contract_item_keys:
        raw_item = raw_items.get(source_key)
        if not isinstance(raw_item, dict):
            return ()
        # A repaired target has a distinct archival/corrected-target route.
        # It must never inherit ordinary duplicate-input credit here.
        if (
            str(raw_item.get("coverage_status") or "").strip().lower()
            == "corrected_source_statement"
        ):
            continue
        raw_contract = raw_item.get("semantic_contract")
        if not isinstance(raw_contract, dict):
            return ()
        # A refutation contract has a different source-record relationship;
        # retain its premises for independent review rather than attempting
        # to project it through a positive direct/Spec pair.
        if str(raw_contract.get("evidence_mode") or "").strip() != "proves":
            continue
        evidence = _qualified_contract_declaration_name(
            declarations, str(raw_contract.get("evidence_declaration") or "")
        )
        spec = _qualified_contract_declaration_name(
            declarations, str(raw_contract.get("spec_declaration") or "")
        )
        if not evidence or not spec or evidence == spec:
            return ()
        pair = (evidence, spec)
        pairs.add(pair)

    # A declaration participating in multiple source-map pairs could map a
    # binder to a nearby but distinct source proposition.  A corrected target
    # sharing an otherwise ordinary pair is similarly not separable at the
    # binder surface. Do not choose one based on spelling or ordering; leave
    # all such inputs independently due.
    return tuple(
        sorted(
            pair
            for pair in pairs
            if pair not in corrected_pairs
            and all(
                len(all_pairs_by_member.get(member, set())) == 1
                for member in pair
            )
        )
    )


def semantic_contract_closeout_bridge_is_current(
    paper_id: str,
    folder: Path,
    status: object,
    status_payload: dict[str, object],
    paper_declarations: dict[str, list[LeanDeclaration]] | None = None,
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> bool:
    """Return whether exact contracts can replace blank legacy statement lanes.

    The decision is source-map-item based: every ordinary claim-bearing source
    item must have a byte-anchored, manually independent Spec and a
    Lean-Meta-checked exact evidence theorem.  Route names only locate the
    declarations fed to Lean Meta; they do not count as coverage evidence.

    This intentionally does *not* replace recursive source-record or
    semantic-model review.  Those lanes inspect model fields, expanded carrier
    domains, probability/conditioning semantics, and consistency conditions
    which a theorem-level exact type check alone cannot certify.
    """

    if status not in {"formalized", "formalized with caveat"}:
        return False
    if (
        run_context is not None
        and run_context.current_semantic_contract_closeout_bridge_scope_keys()
    ):
        # The declaration gate already completed the full source inventory,
        # semantic-contract, Lean-Meta/correspondence, and repaired-defect
        # checks in this exact builder-issued transaction.  Replaying the same
        # function here adds no evidence; the transaction's final mutation
        # check remains the shared boundary for both consumers.
        return True
    try:
        from scripts.audit_evidence_integrity import (
            semantic_contract_closeout_bridge_inventory,
        )
        inventory, inventory_findings = semantic_contract_closeout_bridge_inventory(
            folder,
            str(status),
            context=(
                run_context.evidence_context
                if run_context is not None
                else None
            ),
        )
    except Exception:
        # A bridge is a closeout relaxation, so any unavailable prerequisite
        # fails closed and leaves the ordinary dashboard checks in force.
        return False
    if inventory is None or inventory_findings or not inventory.contract_item_keys:
        return False

    statement_map = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    map_payload = (
        run_context.exact_json_payload(statement_map)
        if run_context is not None
        else load_json_object(statement_map)
    )
    if not isinstance(map_payload, dict):
        return False
    declarations = paper_declarations or (
        run_context.paper_declaration_index()
        if run_context is not None
        else paper_lean_declaration_index(folder)
    )
    contract_findings = paper_statement_map_semantic_contract_findings(
        paper_id,
        folder,
        status,
        map_payload,
        declarations,
        set(),
        status_payload,
        run_context=run_context,
    )
    # Any failure, including an unavailable Meta result or anti-circular Spec,
    # means a blank LLM sidecar remains insufficient.
    return not contract_findings




def _configured_review_sidecar_path(
    folder: Path,
    status_payload: Mapping[str, object],
    *,
    section_names: tuple[str, ...],
    field_name: str,
    default_basename: str,
    run_context: PaperCloseoutRunContext,
) -> Path | None:
    """Resolve one configured sidecar from the transaction's exact status."""

    review_surface = status_payload.get("review_surface")
    if isinstance(review_surface, Mapping):
        for section_name in section_names:
            section = review_surface.get(section_name)
            if not isinstance(section, Mapping):
                continue
            raw_path = section.get(field_name)
            if raw_path is None:
                continue
            if not isinstance(raw_path, str) or not raw_path.strip():
                return None
            relative_path = Path(raw_path.strip())
            if relative_path.is_absolute():
                return None
            anchor = ROOT if relative_path.parts[:1] == ("papers",) else folder
            try:
                configured = (anchor / relative_path).resolve()
                configured.relative_to(folder.resolve())
            except (OSError, RuntimeError, ValueError):
                return None
            return configured

    evidence_context = run_context.evidence_context
    canonical_path = getattr(evidence_context, "canonical_sidecar_path", None)
    if callable(canonical_path):
        resolved = canonical_path(default_basename)
        return resolved if isinstance(resolved, Path) else None
    return None


def _blank_non_evidence_sidecar(
    path: Path,
    dashboard: Any,
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> bool:
    """Return whether a dashboard sidecar has explicitly supplied no evidence.

    Missing files are equivalent to an absent legacy lane.  Existing files are
    accepted only when the dashboard's narrow non-evidence marker is present
    *and* no row judgments have been added.  A malformed, stale, populated, or
    adverse sidecar remains visible to the ordinary dashboard audit.
    """

    if run_context is not None:
        evidence_context = run_context.evidence_context
        snapshot_lookup = getattr(evidence_context, "json_snapshot", None)
        snapshot = snapshot_lookup(path) if callable(snapshot_lookup) else None
        if snapshot is None:
            return False
        if getattr(snapshot, "sha256", None) is None:
            return True
        payload = getattr(snapshot, "payload", None)
    else:
        if not path.exists():
            return True
        payload = load_json_object(path)
    if not isinstance(payload, dict):
        return False
    if not dashboard.is_non_evidence_scaffold_payload(payload):
        return False
    for field in ("items", "judgments"):
        value = payload.get(field)
        if isinstance(value, (dict, list)) and value:
            return False
    for field in ("judgment", "verdict", "coverage", "matches"):
        value = payload.get(field)
        if value not in {None, "", False}:
            return False
    recorded_rows = payload.get("review_rows")
    if isinstance(recorded_rows, int) and not isinstance(recorded_rows, bool):
        if recorded_rows != 0:
            return False
    elif recorded_rows not in {None, ""}:
        return False
    if payload.get("source_grounded") is True:
        return False
    return True


def semantic_contract_closeout_blank_sidecar_lanes(
    folder: Path,
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> dict[str, bool]:
    """Return which legacy v10 lanes are explicitly blank, never merely stale.

    A semantic contract may replace the statement/coverage review only when
    the corresponding sidecar supplies no competing evidence.  This preserves
    a real current mismatch, uncertainty, stale row, or populated review as a
    closeout blocker instead of allowing a later contract to erase it.
    """

    try:
        from scripts import review_dashboard as dashboard
        if run_context is None:
            review_surface_path = dashboard.llm_review_surface_file(folder)
            lean_to_tex_path = dashboard.llm_lean_to_tex_drafts_file(folder)
            statement_path = dashboard.llm_statement_judgments_file(folder)
            coverage_path = dashboard.llm_paper_coverage_file(folder)
        else:
            status_payload = run_context.exact_json_payload(folder / "status.json")
            if status_payload is None:
                return {
                    "review_surface": False,
                    "statement": False,
                    "coverage": False,
                }
            statement_sections = ("llm_statement_review",)
            coverage_sections = (
                "llm_paper_coverage_review",
                "llm_statement_review",
            )
            review_surface_path = _configured_review_sidecar_path(
                folder,
                status_payload,
                section_names=statement_sections,
                field_name="review_surface_audit_file",
                default_basename="review_surface_llm.json",
                run_context=run_context,
            )
            lean_to_tex_path = _configured_review_sidecar_path(
                folder,
                status_payload,
                section_names=statement_sections,
                field_name="lean_to_tex_file",
                default_basename="lean_to_tex_llm.json",
                run_context=run_context,
            )
            statement_path = _configured_review_sidecar_path(
                folder,
                status_payload,
                section_names=statement_sections,
                field_name="match_judgment_file",
                default_basename="statement_match_llm.json",
                run_context=run_context,
            )
            coverage_path = _configured_review_sidecar_path(
                folder,
                status_payload,
                section_names=coverage_sections,
                field_name="paper_coverage_audit_file",
                default_basename="paper_coverage_llm.json",
                run_context=run_context,
            )
            if any(
                path is None
                for path in (
                    review_surface_path,
                    lean_to_tex_path,
                    statement_path,
                    coverage_path,
                )
            ):
                return {
                    "review_surface": False,
                    "statement": False,
                    "coverage": False,
                }
        assert isinstance(review_surface_path, Path)
        assert isinstance(lean_to_tex_path, Path)
        assert isinstance(statement_path, Path)
        assert isinstance(coverage_path, Path)
        review_surface = _blank_non_evidence_sidecar(
            review_surface_path,
            dashboard,
            run_context=run_context,
        )
        statement = _blank_non_evidence_sidecar(
            lean_to_tex_path,
            dashboard,
            run_context=run_context,
        ) and _blank_non_evidence_sidecar(
            statement_path,
            dashboard,
            run_context=run_context,
        )
        coverage = _blank_non_evidence_sidecar(
            coverage_path,
            dashboard,
            run_context=run_context,
        )
    except Exception:
        return {"review_surface": False, "statement": False, "coverage": False}
    return {
        "review_surface": review_surface,
        "statement": statement,
        "coverage": coverage,
    }


def semantic_contract_closeout_current_semantic_reuse_lanes(
    surface: Mapping[str, object],
    statements: Mapping[str, object],
) -> dict[str, bool]:
    """Identify a stale positive surface safely replaced by current row evidence.

    This is intentionally narrower than a generic stale-sidecar waiver.  The
    caller must separately establish the current exact source-contract bridge.
    Here, every current review row must have exactly one current statement
    judgment selected by its elaborated signature plus current paper and
    translated-statement digests.  The legacy review-surface pass must itself
    be a metadata-complete positive pass with an unchanged row count.  Any
    missing, ambiguous, adverse, prompt-stale, or unpinned item leaves the
    stale sidecar visible.
    """

    def exact_int(value: object) -> int | None:
        if isinstance(value, int) and not isinstance(value, bool):
            return value
        return None

    row_count = exact_int(surface.get("row_count"))
    recorded_rows = exact_int(surface.get("recorded_review_rows"))
    semantic_rows = exact_int(statements.get("semantic_current_judgment_count"))
    if (
        row_count is None
        or row_count <= 0
        or recorded_rows != row_count
        or semantic_rows != row_count
        or exact_int(statements.get("row_count")) != row_count
    ):
        return {"review_surface": False, "statement": False, "coverage": False}

    current_digest = str(surface.get("review_surface_sha256") or "").strip().lower()
    recorded_digest = str(
        surface.get("recorded_review_surface_sha256") or ""
    ).strip().lower()
    if (
        not re.fullmatch(r"[0-9a-f]{64}", current_digest)
        or not re.fullmatch(r"[0-9a-f]{64}", recorded_digest)
        or current_digest == recorded_digest
        or surface.get("judgment") != "passes"
        or not bool(surface.get("stale"))
        or bool(surface.get("missing_required"))
        or bool(surface.get("prompt_version_stale"))
        or bool(surface.get("metadata_missing"))
        or bool(surface.get("non_evidence_scaffold"))
        or bool(surface.get("unknown_judgment"))
    ):
        return {"review_surface": False, "statement": False, "coverage": False}

    required_zero_counts = (
        "missing_draft_count",
        "stale_draft_count",
        "missing_judgment_count",
        "stale_judgment_count",
        "missing_obligation_ledger_count",
        "mismatch_count",
        "uncertain_count",
        "unknown_count",
        "ambiguous_semantic_judgment_count",
    )
    if bool(statements.get("needs_attention")) or any(
        exact_int(statements.get(field)) != 0 for field in required_zero_counts
    ):
        return {"review_surface": False, "statement": False, "coverage": False}
    return {"review_surface": True, "statement": False, "coverage": False}


def paper_statement_map_declaration_findings(
    paper_id: str,
    folder: Path,
    status: object,
    *,
    presentation_hygiene: bool = False,
    run_context: PaperCloseoutRunContext | None = None,
    skip_semantic_contract_lean: bool = False,
) -> list[Finding]:
    """Check that source-inventory Lean declaration names resolve."""

    statement_map = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    if run_context is not None:
        payload = run_context.exact_json_payload(statement_map)
        if payload is None:
            return [
                Finding(
                    completed_status_finding_severity(status),
                    statement_map,
                    f"`{paper_id}` source inventory is absent or not readable JSON",
                )
            ]
    else:
        if not statement_map.exists():
            return []
        try:
            payload = json.loads(statement_map.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            return [
                Finding(
                    completed_status_finding_severity(status),
                    statement_map,
                    f"`{paper_id}` source inventory is not readable JSON: {exc}",
                )
            ]
    if not isinstance(payload, dict):
        return [
            Finding(
                completed_status_finding_severity(status),
                statement_map,
                f"`{paper_id}` source inventory must be a JSON object",
            )
        ]
    items = payload.get("items") if isinstance(payload, dict) else None
    if not isinstance(items, dict):
        return [
            Finding(
                completed_status_finding_severity(status),
                statement_map,
                f"`{paper_id}` source inventory `items` must be a JSON object",
            )
        ]

    # The ordinary coverage selector treats a byte-pinned, source-only
    # repeated presentation as the canonical result's one obligation. Reuse
    # that validated relation here as well: a proof-appendix restatement must
    # retain its source anchor, but it must not be forced to invent a second
    # Lean theorem route. Invalid alias metadata remains an error below.
    presentation_aliases, presentation_alias_errors = source_presentation_aliases(
        items
    )

    coverage_mode, _coverage_mode_error = source_coverage_mode_from_map(payload)
    source_index_selected_ids = source_index_byte_pinned_anchor_item_ids(
        folder,
        payload,
        coverage_mode,
        context=(
            run_context.evidence_context if run_context is not None else None
        ),
    )
    direct_proof_items = filter_source_map_items_for_proof_obligations(
        items,
        coverage_mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            payload
        ),
        additional_selected_item_ids=source_index_selected_ids,
    )
    # A valid repeated presentation inherits its canonical source result and
    # must never be forced to invent a second Lean endpoint.  Invalid alias
    # metadata remains visible through the structural finding above.
    direct_proof_items = {
        source_key: item
        for source_key, item in direct_proof_items.items()
        if source_key not in presentation_aliases
        # Support-only rows remain source-visible proof inventory. They are
        # deliberately not direct source-result obligations and therefore
        # need no theorem route, atom contract, or transparent Spec card.
        and not bool(source_item_effective_route_policy(item).get("is_support_only"))
    }
    direct_proof_item_keys = set(direct_proof_items)
    direct_proof_payload = dict(payload)
    direct_proof_payload["items"] = direct_proof_items

    paper_declarations = (
        run_context.paper_declaration_index()
        if run_context is not None
        else paper_lean_declaration_index(folder)
    )
    library_declarations = (
        run_context.library_declaration_index()
        if run_context is not None
        else library_lean_declaration_index()
    )
    native_v11_routes = bool(
        run_context is not None
        and run_context.selected_v11_closeout
    )
    if run_context is not None:
        status_payload = run_context.exact_json_payload(folder / "status.json") or {}
    else:
        try:
            status_payload = json.loads(
                (folder / "status.json").read_text(encoding="utf-8")
            )
        except (OSError, json.JSONDecodeError):
            status_payload = {}
    review_surface = (
        status_payload.get("review_surface", {})
        if isinstance(status_payload, dict)
        else {}
    )
    reviewed_source_texts: dict[Path, str] | None = None
    if (
        presentation_hygiene
        and not native_v11_routes
        and run_context is not None
        and run_context.evidence_context is not None
    ):
        reviewed_source_texts = {}
        for source_path in {
            review_surface_source_file_path(folder, review_surface).resolve(),
            proof_endpoint_source_file_path(folder, review_surface).resolve(),
            assumption_source_file_path(folder, review_surface).resolve(),
        }:
            source_text = run_context.exact_lean_source_text(source_path)
            if source_text is not None:
                reviewed_source_texts[source_path] = source_text
    reviewed_bridge_names, reviewed_bridge_comments = (
        paper_reviewed_semantic_bridge_names(
            folder,
            status_payload=status_payload,
            source_text_by_path=reviewed_source_texts,
            include_legacy_comment_hygiene=(
                presentation_hygiene and not native_v11_routes
            ),
        )
    )
    reviewed_source_paths = {
        review_surface_source_file_path(folder, review_surface).resolve(),
        proof_endpoint_source_file_path(folder, review_surface).resolve(),
        assumption_source_file_path(folder, review_surface).resolve(),
    }
    reviewed_declaration_keys: set[tuple[Path, int, str]] = set()
    for reviewed_name in reviewed_bridge_names:
        resolved_reviewed = resolve_declaration_name(paper_declarations, reviewed_name)
        if len(resolved_reviewed) != 1:
            # A paper may retain implementation/audit wrappers with the same
            # short name as a declaration on PaperInterface.  The configured
            # review source is the authority for the reviewed row; do not let
            # an unrelated duplicate make that row disappear from proof
            # routing merely because status.json stores the short row name.
            resolved_reviewed = [
                declaration
                for declaration in resolved_reviewed
                if declaration.path.resolve() in reviewed_source_paths
            ]
        if len(resolved_reviewed) == 1:
            reviewed_declaration_keys.add(declaration_key(resolved_reviewed[0]))

    # The configured Spec/proof pairing is a single audited source claim:
    # admit its theorem endpoint to proof-route validation even though the
    # endpoint is intentionally absent from the human `include_names` list.
    # Exact Spec-type equality is checked independently by Lean Meta in
    # `check_proposition_spec_routes`; this narrow structural admission cannot
    # make an arbitrary proof-module helper reviewable.
    if isinstance(review_surface, dict):
        raw_pairs = review_surface.get("proposition_spec_proofs")
        include_names = {
            str(name).strip()
            for name in review_surface.get("include_names", [])
            if isinstance(name, str) and name.strip()
        }
        source_path = review_surface_source_file_path(folder, review_surface).resolve()
        proof_path = proof_endpoint_source_file_path(folder, review_surface).resolve()
        if isinstance(raw_pairs, dict):
            for raw_spec, raw_proof in raw_pairs.items():
                if not isinstance(raw_spec, str) or not isinstance(raw_proof, str):
                    continue
                spec_name = raw_spec.strip()
                proof_name = raw_proof.strip()
                if not spec_name or not proof_name or spec_name not in include_names:
                    continue
                resolved_spec = resolve_declaration_name(paper_declarations, spec_name)
                resolved_proof = resolve_declaration_name(paper_declarations, proof_name)
                if len(resolved_spec) != 1:
                    resolved_spec = [
                        declaration
                        for declaration in resolved_spec
                        if declaration.path.resolve() == source_path
                    ]
                if len(resolved_proof) != 1:
                    resolved_proof = [
                        declaration
                        for declaration in resolved_proof
                        if declaration.path.resolve() == proof_path
                    ]
                if (
                    len(resolved_spec) == 1
                    and declaration_key(resolved_spec[0]) in reviewed_declaration_keys
                    and len(resolved_proof) == 1
                    and resolved_proof[0].path.resolve() == proof_path
                    and resolved_proof[0].kind in LEAN_PROOF_DECLARATION_KINDS
                ):
                    reviewed_declaration_keys.add(declaration_key(resolved_proof[0]))

    def is_unique_reviewed_declaration(
        resolved: list[LeanDeclaration], expected_kinds: set[str] | None = None
    ) -> bool:
        return bool(
            len(resolved) == 1
            and declaration_key(resolved[0]) in reviewed_declaration_keys
            and (expected_kinds is None or resolved[0].kind in expected_kinds)
        )

    # Claim atoms must route to a result row, not to an assumption or an
    # implementation-side record/certificate.  This is a review-surface
    # identity check only; the atom's pinned source text remains the semantic
    # evidence for what has to be proved.
    review_source_path = review_surface_source_file_path(
        folder, review_surface
    ).resolve()
    proof_endpoint_path = proof_endpoint_source_file_path(
        folder, review_surface
    ).resolve()
    included_reviewed_declaration_keys: set[tuple[Path, int, str]] = set()
    raw_include_names = (
        _string_list_field(review_surface.get("include_names"))
        if isinstance(review_surface, dict)
        else None
    )
    for included_name in raw_include_names or []:
        resolved_included = resolve_declaration_name(
            paper_declarations, included_name
        )
        if len(resolved_included) != 1:
            resolved_included = [
                declaration
                for declaration in resolved_included
                if declaration.path.resolve() == review_source_path
            ]
        if len(resolved_included) == 1:
            included_reviewed_declaration_keys.add(
                declaration_key(resolved_included[0])
            )

    # One source claim may have a transparent `Spec : Prop` in
    # PaperInterface and its theorem/lemma endpoint in a separate, configured
    # paper-local proof module.  The endpoint is an auditable route only when
    # it is explicitly paired to an included Spec.  This keeps the semantic
    # row count unchanged and prevents arbitrary proof-module helpers from
    # acquiring source-claim credit.
    configured_endpoint_keys: set[tuple[Path, int, str]] = set()
    raw_spec_proof_pairs = (
        review_surface.get("proposition_spec_proofs")
        if isinstance(review_surface, dict)
        else None
    )
    if isinstance(raw_spec_proof_pairs, dict):
        for raw_spec, raw_proof in raw_spec_proof_pairs.items():
            if not isinstance(raw_spec, str) or not isinstance(raw_proof, str):
                continue
            spec_name = raw_spec.strip()
            proof_name = raw_proof.strip()
            if not spec_name or not proof_name:
                continue
            resolved_spec = resolve_declaration_name(paper_declarations, spec_name)
            resolved_proof = resolve_declaration_name(paper_declarations, proof_name)
            if len(resolved_spec) != 1:
                resolved_spec = [
                    declaration
                    for declaration in resolved_spec
                    if declaration.path.resolve() == review_source_path
                ]
            if len(resolved_proof) != 1:
                resolved_proof = [
                    declaration
                    for declaration in resolved_proof
                    if declaration.path.resolve() == proof_endpoint_path
                ]
            if (
                len(resolved_spec) == 1
                and declaration_key(resolved_spec[0])
                in included_reviewed_declaration_keys
                and len(resolved_proof) == 1
                and resolved_proof[0].path.resolve() == proof_endpoint_path
                and resolved_proof[0].kind in LEAN_PROOF_DECLARATION_KINDS
            ):
                configured_endpoint_keys.add(declaration_key(resolved_proof[0]))

    def resolve_atom_route(route: str) -> list[LeanDeclaration]:
        resolved_route = resolve_declaration_name(paper_declarations, route)
        if len(resolved_route) != 1:
            visible = [
                declaration
                for declaration in resolved_route
                if declaration.path.resolve()
                in {review_source_path, proof_endpoint_path}
            ]
            if len(visible) == 1:
                return visible
        return resolved_route

    def is_auditable_claim_atom_route(
        resolved_route: list[LeanDeclaration],
    ) -> bool:
        return bool(
            len(resolved_route) == 1
            and (
                declaration_key(resolved_route[0])
                in included_reviewed_declaration_keys
                or declaration_key(resolved_route[0]) in configured_endpoint_keys
            )
            and resolved_route[0].path.resolve()
            in {review_source_path, proof_endpoint_path}
            and resolved_route[0].kind in LEAN_PROOF_DECLARATION_KINDS
        )

    source_claim_atoms_enabled = schema_version_is_exact(
        payload.get(SOURCE_CLAIM_ATOMS_SCHEMA_KEY), SOURCE_CLAIM_ATOMS_SCHEMA
    )
    raw_quarantined = (
        review_surface.get("quarantined_auxiliary_names", [])
        if isinstance(review_surface, dict)
        else []
    )
    quarantined_auxiliary_names = {
        str(name).strip()
        for name in raw_quarantined
        if isinstance(name, str) and name.strip()
    }
    quarantined_auxiliary_short_names = {
        name.rsplit(".", 1)[-1] for name in quarantined_auxiliary_names
    }
    if run_context is not None and run_context.evidence_context is not None:
        _source_fidelity_path, exact_source_fidelity_payload = (
            run_context.exact_source_proof_fidelity_input()
        )
        source_fidelity_payload = exact_source_fidelity_payload or {}
    else:
        source_fidelity_path = configured_source_proof_fidelity_path(
            folder, status_payload if isinstance(status_payload, dict) else {}
        )
        if source_fidelity_path is None and not (
            isinstance(review_surface, dict)
            and isinstance(review_surface.get("source_proof_fidelity_review"), dict)
        ):
            source_fidelity_path = (
                folder / PAPER_AUDIT_DIR / "source_proof_fidelity.json"
            )
            if not source_fidelity_path.exists():
                source_fidelity_path = folder / "source_proof_fidelity.json"
        try:
            assert source_fidelity_path is not None
            source_fidelity_payload = json.loads(
                source_fidelity_path.read_text(encoding="utf-8")
            )
        except (OSError, json.JSONDecodeError):
            source_fidelity_payload = {}
    raw_defects = (
        source_fidelity_payload.get("defects", [])
        if isinstance(source_fidelity_payload, dict)
        else []
    )
    source_fidelity_defect_ids = {
        str(defect.get("id")).strip()
        for defect in raw_defects
        if isinstance(defect, dict) and str(defect.get("id") or "").strip()
    }
    missing: list[str] = []
    malformed: list[str] = []
    missing_semantic_bridge: list[str] = []
    missing_semantic_bridge_target: list[str] = []
    malformed_semantic_bridge: list[str] = []
    unreviewed_semantic_bridge: list[str] = []
    ambiguous_semantic_bridge_target: list[str] = []
    missing_semantic_bridge_source_status: list[str] = []
    theorem_source_without_reviewed_proof: list[str] = []
    invalid_result_proof_declarations: list[str] = []
    malformed_proof_declarations: list[str] = []
    missing_source_kinds: list[str] = []
    unknown_source_kinds: list[str] = []
    quarantined_routing: list[str] = []
    malformed_quarantined_defect: list[str] = []
    unknown_quarantined_defect_ids: list[str] = []
    quarantined_defect_without_reviewed_evidence: list[str] = []
    malformed_source_claim_atoms: list[str] = []
    unresolved_source_claim_atom_routes: list[str] = []
    unauditable_source_claim_atom_routes: list[str] = []
    for source_key, item in items.items():
        if not isinstance(item, dict):
            continue
        source_key_text = str(source_key).strip()
        if source_key_text in presentation_aliases:
            continue
        source_kind = str(item.get("source_kind") or "").strip().lower()
        source_status = str(item.get("source_status") or "").strip().lower()
        is_direct_proof_obligation = source_key_text in direct_proof_item_keys
        is_quarantined_source_defect = (
            source_status == QUARANTINED_SOURCE_DEFECT_STATUS
        )
        checks_direct_routes = (
            is_direct_proof_obligation or is_quarantined_source_defect
        )
        if not source_kind:
            missing_source_kinds.append(str(source_key))
        elif source_kind not in KNOWN_SOURCE_PRESENTATION_KINDS:
            unknown_source_kinds.append(f"{source_key}:{source_kind}")

        if (
            is_direct_proof_obligation
            and not is_quarantined_source_defect
            and source_claim_atoms_enabled
            and source_kind in SOURCE_CLAIM_ATOM_THEOREM_LIKE_KINDS
        ):
            raw_atoms = item.get(SOURCE_CLAIM_ATOMS_KEY)
            atom_errors = source_claim_atoms_validation_errors(raw_atoms)
            if atom_errors:
                malformed_source_claim_atoms.extend(
                    f"{source_key}:{error}" for error in atom_errors
                )
            elif isinstance(raw_atoms, list):
                for index, raw_atom in enumerate(raw_atoms):
                    assert isinstance(raw_atom, dict)
                    route = str(raw_atom.get("reviewed_lean_route") or "").strip()
                    atom_id = str(raw_atom.get("id") or index).strip()
                    resolved_route = resolve_atom_route(route)
                    if len(resolved_route) != 1:
                        unresolved_source_claim_atom_routes.append(
                            f"{source_key}:{atom_id}:{route or 'missing'}"
                        )
                    elif not is_auditable_claim_atom_route(resolved_route):
                        resolved_kind = resolved_route[0].kind
                        unauditable_source_claim_atom_routes.append(
                            f"{source_key}:{atom_id}:{route}:{resolved_kind}"
                        )
        if is_quarantined_source_defect:
            raw_defect_ids = item.get("source_defect_ids")
            if not isinstance(raw_defect_ids, list) or not raw_defect_ids or not all(
                isinstance(defect_id, str) and defect_id.strip()
                for defect_id in raw_defect_ids
            ):
                malformed_quarantined_defect.append(str(source_key))
            else:
                unknown_ids = sorted(
                    {
                        defect_id.strip()
                        for defect_id in raw_defect_ids
                        if defect_id.strip() not in source_fidelity_defect_ids
                    }
                )
                if unknown_ids:
                    unknown_quarantined_defect_ids.append(
                        f"{source_key}:{','.join(unknown_ids)}"
                    )

            reviewed_evidence = False
            raw_support = item.get("support_lean_declarations")
            if isinstance(raw_support, list):
                for support_name in raw_support:
                    if not isinstance(support_name, str) or not support_name.strip():
                        continue
                    resolved = resolve_declaration_name(
                        paper_declarations, support_name.strip()
                    )
                    if (
                        is_unique_reviewed_declaration(
                            resolved, LEAN_PROOF_DECLARATION_KINDS
                        )
                        or (
                            len(resolved) == 1
                            and resolved[0].kind in LEAN_PROOF_DECLARATION_KINDS
                            and (
                                support_name.strip() in quarantined_auxiliary_names
                                or support_name.strip().rsplit(".", 1)[-1]
                                in quarantined_auxiliary_short_names
                            )
                        )
                    ):
                        reviewed_evidence = True
                        break
            if not reviewed_evidence:
                quarantined_defect_without_reviewed_evidence.append(str(source_key))

        if not checks_direct_routes:
            continue

        # A quarantine excludes a declaration from paper-facing source credit.
        # Navigation aliases and proof-support links are deliberately
        # non-crediting provenance, so they may document an internal helper
        # without turning that helper into the source result's evidence route.
        for field_name in SOURCE_COVERAGE_DECLARATION_ROUTING_FIELDS:
            raw_names = item.get(field_name)
            if not isinstance(raw_names, list):
                continue
            for raw_name in raw_names:
                if not isinstance(raw_name, str) or not raw_name.strip():
                    continue
                name = raw_name.strip()
                if (
                    name in quarantined_auxiliary_names
                    or name.rsplit(".", 1)[-1] in quarantined_auxiliary_short_names
                ):
                    quarantined_routing.append(f"{source_key}:{field_name}:{name}")
        if (
            is_direct_proof_obligation
            and source_status
            not in {"added_audit_row", QUARANTINED_SOURCE_DEFECT_STATUS, "support_only"}
            and source_kind in THEOREM_LIKE_SOURCE_INVENTORY_KINDS
        ):
            proof_candidates: list[str] = []
            proof_fields_valid = True
            for field_name in ("lean_declarations", "proof_lean_declarations"):
                raw_proofs = item.get(field_name)
                if raw_proofs is None:
                    continue
                if not isinstance(raw_proofs, list) or not all(
                    isinstance(value, str) and value.strip() for value in raw_proofs
                ):
                    malformed_proof_declarations.append(f"{source_key}:{field_name}")
                    proof_fields_valid = False
                    continue
                proof_candidates.extend(value.strip() for value in raw_proofs)
            has_reviewed_theorem = False
            if proof_fields_valid:
                raw_explicit_proofs = item.get("proof_lean_declarations")
                if isinstance(raw_explicit_proofs, list):
                    for proof_name in raw_explicit_proofs:
                        if not isinstance(proof_name, str) or not proof_name.strip():
                            continue
                        name = proof_name.strip()
                        resolved = resolve_declaration_name(paper_declarations, name)
                        if (
                            not is_unique_reviewed_declaration(
                                resolved, LEAN_PROOF_DECLARATION_KINDS
                            )
                        ):
                            kinds = sorted({declaration.kind for declaration in resolved})
                            resolved_kind = "/".join(kinds) if kinds else "unresolved"
                            invalid_result_proof_declarations.append(
                                f"{source_key}:{name}:{resolved_kind}"
                            )
                for proof_name in proof_candidates:
                    resolved = resolve_declaration_name(paper_declarations, proof_name)
                    if (
                        is_unique_reviewed_declaration(
                            resolved, LEAN_PROOF_DECLARATION_KINDS
                        )
                        or (
                            not native_v11_routes
                            and
                            is_unique_reviewed_declaration(resolved)
                            and is_thin_review_alias_to_proved_theorem(
                                paper_declarations, resolved[0]
                            )
                        )
                    ):
                        has_reviewed_theorem = True
                        break
            if not has_reviewed_theorem and not is_quarantined_source_defect:
                theorem_source_without_reviewed_proof.append(str(source_key))
        bridge_names = source_inventory_semantic_bridge_names(item)
        if bridge_names is None:
            malformed_semantic_bridge.append(str(source_key))
            bridge_names = []
        bridge_resolved = False
        for bridge_name in bridge_names:
            resolved_bridges = resolve_declaration_name(paper_declarations, bridge_name)
            if resolved_bridges:
                bridge_resolved = True
                bridge_short_name = bridge_name.rsplit(".", 1)[-1]
                if len(resolved_bridges) != 1:
                    ambiguous_semantic_bridge_target.append(f"{source_key}:{bridge_name}")
                if not is_unique_reviewed_declaration(resolved_bridges):
                    unreviewed_semantic_bridge.append(f"{source_key}:{bridge_name}")
                leading_comment = reviewed_bridge_comments.get(bridge_short_name, "")
                if (
                    presentation_hygiene
                    and bridge_short_name in reviewed_bridge_names
                    and not SOURCE_STATUS_LINE_RE.search(leading_comment)
                ):
                    missing_semantic_bridge_source_status.append(f"{source_key}:{bridge_name}")
            else:
                missing_semantic_bridge_target.append(f"{source_key}:{bridge_name}")
        raw_declarations = item.get("lean_declarations")
        raw_support_declarations = item.get("support_lean_declarations")
        for field_name, raw_declarations in (
            ("lean_declarations", raw_declarations),
            ("support_lean_declarations", raw_support_declarations),
        ):
            if raw_declarations is None:
                continue
            if not isinstance(raw_declarations, list):
                malformed.append(str(source_key))
                continue
            for raw_name in raw_declarations:
                name = str(raw_name or "").strip()
                if not name:
                    malformed.append(str(source_key))
                    continue
                if resolve_declaration_name(paper_declarations, name):
                    continue
                if resolve_declaration_name(library_declarations, name):
                    # The selected v11 lane validates the exact reusable
                    # declaration, source route, Lean semantic identity, and
                    # current source-to-library judgment in the material
                    # library gate.  Requiring an additional paper-local
                    # equivalence wrapper here is location-based duplication:
                    # the same declaration would need no wrapper if moved into
                    # the paper folder.  Legacy lanes retain their historical
                    # explicit bridge requirement.
                    if not native_v11_routes and not bridge_resolved:
                        missing_semantic_bridge.append(f"{source_key}:{field_name}:{name}")
                    continue
                missing.append(f"{source_key}:{name}")

    findings: list[Finding] = []
    severity = completed_status_finding_severity(status)
    if presentation_alias_errors:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory has invalid repeated-presentation "
                "alias metadata: "
                + "; ".join(presentation_alias_errors[:4])
                + ("; ..." if len(presentation_alias_errors) > 4 else ""),
            )
        )
    if malformed:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory has malformed lean_declarations for "
                + ", ".join(malformed[:8])
                + ("; ..." if len(malformed) > 8 else ""),
            )
        )
    if malformed_semantic_bridge:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory has malformed semantic bridge declaration fields for "
                + ", ".join(malformed_semantic_bridge[:8])
                + ("; ..." if len(malformed_semantic_bridge) > 8 else ""),
            )
        )
    if missing_semantic_bridge_target:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory names semantic bridge declaration(s) that do not "
                "resolve in paper-local Lean files: "
                + ", ".join(missing_semantic_bridge_target[:8])
                + ("; ..." if len(missing_semantic_bridge_target) > 8 else ""),
            )
        )
    if ambiguous_semantic_bridge_target:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory names semantic bridge declaration(s) that "
                "resolve ambiguously in paper-local Lean files; bridge routing must identify "
                "one reviewed declaration: "
                + ", ".join(ambiguous_semantic_bridge_target[:8])
                + ("; ..." if len(ambiguous_semantic_bridge_target) > 8 else ""),
            )
        )
    if unreviewed_semantic_bridge:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory names semantic bridge declaration(s) that are "
                "not on the configured reviewed/assumption surface. A reusable-library bridge "
                "must be an auditable paper-local row, not a hidden helper or source-looking "
                "name: "
                + ", ".join(unreviewed_semantic_bridge[:8])
                + ("; ..." if len(unreviewed_semantic_bridge) > 8 else ""),
            )
        )
    if presentation_hygiene and missing_semantic_bridge_source_status:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory semantic bridge row(s) lack a `Source status:` "
                "line in the reviewed paper-facing comment: "
                + ", ".join(missing_semantic_bridge_source_status[:8])
                + ("; ..." if len(missing_semantic_bridge_source_status) > 8 else ""),
            )
        )
    if missing_semantic_bridge:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory links source item(s) directly to reusable-library "
                "declaration(s) without a paper-local semantic bridge/equivalence row. "
                "Do not rely on Lean/library names as source evidence; add one of "
                + ", ".join(f"`{field}`" for field in SEMANTIC_BRIDGE_DECLARATION_FIELDS)
                + " pointing to a paper-local declaration that states the source/library match: "
                + ", ".join(missing_semantic_bridge[:8])
                + ("; ..." if len(missing_semantic_bridge) > 8 else ""),
            )
        )
    if missing:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory names {len(missing)} Lean declaration(s) "
                "that do not resolve in paper-local or reusable-library Lean files: "
                + ", ".join(missing[:8])
                + ("; ..." if len(missing) > 8 else ""),
            )
        )
    if malformed_proof_declarations:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` theorem-like source inventory has malformed proof declaration "
                "routing for "
                + ", ".join(malformed_proof_declarations[:8])
                + ("; ..." if len(malformed_proof_declarations) > 8 else ""),
            )
        )
    if invalid_result_proof_declarations:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` result item `proof_lean_declarations` must each resolve to "
                "one reviewed Lean theorem/lemma; definitions and abbreviations are "
                "specification vocabulary, not proof evidence: "
                + ", ".join(invalid_result_proof_declarations[:8])
                + ("; ..." if len(invalid_result_proof_declarations) > 8 else ""),
            )
        )
    if missing_source_kinds:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory item(s) omit required `source_kind`: "
                + ", ".join(missing_source_kinds[:8])
                + ("; ..." if len(missing_source_kinds) > 8 else ""),
            )
        )
    if unknown_source_kinds:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory item(s) use unknown `source_kind`: "
                + ", ".join(unknown_source_kinds[:8])
                + ("; ..." if len(unknown_source_kinds) > 8 else ""),
            )
        )
    if quarantined_routing:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source inventory routes source item(s) through quarantined "
                "auxiliary declaration(s). A quarantine is a semantic exclusion from "
                "paper-facing evidence, not a cosmetic label: "
                + ", ".join(quarantined_routing[:8])
                + ("; ..." if len(quarantined_routing) > 8 else ""),
            )
        )
    if malformed_quarantined_defect:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source item(s) marked `{QUARANTINED_SOURCE_DEFECT_STATUS}` "
                "must cite a nonempty string-list `source_defect_ids`: "
                + ", ".join(malformed_quarantined_defect[:8])
                + ("; ..." if len(malformed_quarantined_defect) > 8 else ""),
            )
        )
    if unknown_quarantined_defect_ids:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` quarantined source item(s) cite defect id(s) absent from "
                "the source-proof-fidelity ledger: "
                + ", ".join(unknown_quarantined_defect_ids[:8])
                + ("; ..." if len(unknown_quarantined_defect_ids) > 8 else ""),
            )
        )
    if quarantined_defect_without_reviewed_evidence:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` quarantined source item(s) lack a reviewed theorem/lemma "
                "counterexample or defect-evidence route in `support_lean_declarations`: "
                + ", ".join(quarantined_defect_without_reviewed_evidence[:8])
                + ("; ..." if len(quarantined_defect_without_reviewed_evidence) > 8 else ""),
            )
        )
    if malformed_source_claim_atoms:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source-claim atom contract is malformed for "
                + ", ".join(malformed_source_claim_atoms[:8])
                + ("; ..." if len(malformed_source_claim_atoms) > 8 else ""),
            )
        )
    if unresolved_source_claim_atom_routes:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source-claim atom route(s) do not resolve to one "
                "paper-local reviewed theorem/lemma: "
                + ", ".join(unresolved_source_claim_atom_routes[:8])
                + ("; ..." if len(unresolved_source_claim_atom_routes) > 8 else ""),
            )
        )
    if unauditable_source_claim_atom_routes:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` source-claim atom route(s) must be configured "
                "Spec-paired theorem/lemma result endpoints, not assumptions, definitions, "
                "records, certificates, or hidden helpers: "
                + ", ".join(unauditable_source_claim_atom_routes[:8])
                + ("; ..." if len(unauditable_source_claim_atom_routes) > 8 else ""),
            )
        )
    if theorem_source_without_reviewed_proof:
        findings.append(
            Finding(
                severity,
                statement_map,
                f"`{paper_id}` theorem-like source item(s) do not route to a unique reviewed "
                "Lean theorem/lemma declaration: "
                + ", ".join(theorem_source_without_reviewed_proof[:8])
                + ("; ..." if len(theorem_source_without_reviewed_proof) > 8 else "")
                + ". Definitions, structures, inductives, and declaration names alone are not proof evidence.",
            )
        )
    findings.extend(
        paper_statement_map_semantic_surface_findings(
            paper_id,
            folder,
            status,
            direct_proof_payload,
            paper_declarations,
            reviewed_declaration_keys,
            presentation_hygiene=presentation_hygiene,
            build_input_provider=(
                run_context.build_input_provider
                if run_context is not None
                else None
            ),
            run_context=run_context,
        )
    )
    if not skip_semantic_contract_lean:
        findings.extend(
            paper_statement_map_semantic_contract_findings(
                paper_id,
                folder,
                status,
                direct_proof_payload,
                paper_declarations,
                reviewed_bridge_names,
                status_payload if isinstance(status_payload, dict) else {},
                run_context=run_context,
            )
        )
    return findings


def is_signature_only_review_alias(kind: str, source: str) -> bool:
    """Heuristic for review rows that expose only an imported function/type alias."""

    if kind not in {"abbrev", "def"} or ":=" not in source:
        return False
    body = re.sub(r"\s+", " ", source.split(":=", 1)[1].strip())
    if not body:
        return False
    if body.startswith("@"):
        return True
    if re.match(r"(?:[A-Z][A-Za-z0-9_']*|[A-Za-z_][A-Za-z0-9_']*\.)", body):
        return True
    if re.match(r"paper_[A-Za-z0-9_']+\b", body):
        return True
    return False


def review_surface_assumption_names(review_surface: dict[str, object]) -> tuple[set[str], list[str]]:
    """Read the explicit paper-assumption ledger from status.json review_surface."""

    raw = review_surface.get("assumption_names")
    if raw is None:
        return set(), []
    if not isinstance(raw, list):
        return set(), ["`review_surface.assumption_names` should be a string list"]
    names: set[str] = set()
    problems: list[str] = []
    for index, value in enumerate(raw, start=1):
        if not isinstance(value, str) or not value.strip():
            problems.append(f"`review_surface.assumption_names[{index}]` should be a nonempty string")
            continue
        names.add(value.strip())
    return names, problems


def review_surface_proof_boundary_names(review_surface: dict[str, object]) -> tuple[set[str], list[str]]:
    """Read approved paper-local proof-boundary declarations from status.json."""

    raw = review_surface.get("proof_boundary_names")
    if raw is None:
        return set(), []
    if not isinstance(raw, list):
        return set(), ["`review_surface.proof_boundary_names` should be a string list"]
    names: set[str] = set()
    problems: list[str] = []
    for index, value in enumerate(raw, start=1):
        if not isinstance(value, str) or not value.strip():
            problems.append(f"`review_surface.proof_boundary_names[{index}]` should be a nonempty string")
            continue
        names.add(value.strip())
    return names, problems


def review_surface_auxiliary_names(review_surface: dict[str, object]) -> tuple[set[str], list[str]]:
    """Read proof-facing declarations intentionally excluded from statement review."""

    raw = review_surface.get("auxiliary_names")
    if raw is None:
        return set(), []
    if not isinstance(raw, list):
        return set(), ["`review_surface.auxiliary_names` should be a string list"]
    names: set[str] = set()
    problems: list[str] = []
    for index, value in enumerate(raw, start=1):
        if not isinstance(value, str) or not value.strip():
            problems.append(f"`review_surface.auxiliary_names[{index}]` should be a nonempty string")
            continue
        names.add(value.strip())
    return names, problems


def review_surface_quarantined_auxiliary_names(
    review_surface: dict[str, object],
) -> tuple[set[str], list[str]]:
    """Read auxiliaries explicitly barred from paper-facing review credit."""

    raw = review_surface.get("quarantined_auxiliary_names")
    if raw is None:
        return set(), []
    if not isinstance(raw, list):
        return set(), ["`review_surface.quarantined_auxiliary_names` should be a string list"]
    names: set[str] = set()
    problems: list[str] = []
    for index, value in enumerate(raw, start=1):
        if not isinstance(value, str) or not value.strip():
            problems.append(
                "`review_surface.quarantined_auxiliary_names[{}]` should be a nonempty string".format(index)
            )
            continue
        names.add(value.strip())
    return names, problems


def assumption_source_file_path(folder: Path, review_surface: dict[str, object]) -> Path:
    """Return the paper-local Lean file that declares reviewed assumptions."""

    raw_path = review_surface.get("assumption_source_file")
    if isinstance(raw_path, str) and raw_path.strip():
        return ROOT / raw_path.strip()
    return folder / DEFAULT_ASSUMPTION_SOURCE_FILE


def review_surface_source_file_path(folder: Path, review_surface: dict[str, object]) -> Path:
    """Return the Lean file that contains the configured review-surface rows."""

    raw_path = review_surface.get("source_file")
    if isinstance(raw_path, str) and raw_path.strip():
        return ROOT / raw_path.strip()
    return folder / "PaperInterface.lean"


def v11_source_claim_review_names(
    status_payload: Mapping[str, object],
) -> frozenset[str] | None:
    """Return the explicit one-semantic-target-per-claim v11 surface.

    The selection is structural and location-independent.  Every configured
    human review name is selected here without guessing its semantic role from
    a status-list category. The retained Lean graph and typed statement-map
    routes subsequently prove whether it is a theorem-backed Spec or a direct
    source definition/model/algorithm and require the corresponding proof
    endpoint when applicable. Legacy `source_definition_names` may describe
    reusable vocabulary rather than paper-local claims, so it is not an
    admissible role classifier. ``None`` retains the legacy behavior.
    """

    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, Mapping) or not (
        explicit_raw_source_spec_screening_requested(status_payload)
    ):
        return None
    raw_names = review_surface.get("include_names")
    if not isinstance(raw_names, list):
        return None
    names = [
        str(value).strip()
        for value in raw_names
        if isinstance(value, str) and value.strip()
    ]
    if not names or len(names) != len(raw_names) or len(names) != len(set(names)):
        return None
    return frozenset(names)


def proof_endpoint_source_file_path(folder: Path, review_surface: dict[str, object]) -> Path:
    """Return the optional module containing theorem endpoints for reviewed Specs.

    PaperInterface remains the single human semantic-review surface.  When
    theorem endpoints are intentionally separated into ProofInterface, this
    path is still included in machine proof-route validation without creating
    duplicate human source-claim rows.
    """

    raw_path = review_surface.get("proof_file")
    if isinstance(raw_path, str) and raw_path.strip():
        return ROOT / raw_path.strip()
    # A separate ProofInterface is opt-in. Legacy and migrated papers may
    # keep the exact-type theorem endpoint beside the reviewed Spec in
    # PaperInterface; treating a nonexistent sibling as the default turns a
    # valid configured proof route into a spurious closeout failure.
    return review_surface_source_file_path(folder, review_surface)


def assumption_judgment_file_path(folder: Path, review_surface: dict[str, object]) -> Path:
    """Return the paper-root LLM assumption-provenance judgment file."""

    llm_assumption_review = review_surface.get("llm_assumption_review")
    if isinstance(llm_assumption_review, dict):
        raw_path = llm_assumption_review.get("assumption_judgment_file")
        if isinstance(raw_path, str) and raw_path.strip():
            return ROOT / raw_path.strip()
    return folder / DEFAULT_LLM_ASSUMPTION_JUDGE_FILE


def source_record_audit_file_path(folder: Path, review_surface: dict[str, object]) -> Path:
    """Return the paper-root generated source-record audit payload path."""

    llm_source_record_review = review_surface.get("llm_source_record_review")
    if isinstance(llm_source_record_review, dict):
        raw_path = llm_source_record_review.get("source_record_audit_file")
        if isinstance(raw_path, str) and raw_path.strip():
            return ROOT / raw_path.strip()
    return folder / DEFAULT_SOURCE_RECORD_AUDIT_FILE


def source_record_judgment_file_path(folder: Path, review_surface: dict[str, object]) -> Path:
    """Return the paper-root LLM source-record judgment sidecar path."""

    llm_source_record_review = review_surface.get("llm_source_record_review")
    if isinstance(llm_source_record_review, dict):
        raw_path = llm_source_record_review.get("source_record_judgment_file")
        if isinstance(raw_path, str) and raw_path.strip():
            return ROOT / raw_path.strip()
    return folder / DEFAULT_SOURCE_RECORD_JUDGE_FILE


def load_json_object(path: Path) -> dict[str, object] | None:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, dict) else None


def source_record_target_disposition_context(
    folder: Path,
    review_surface: dict[str, object],
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> tuple[dict[str, object] | None, dict[str, object] | None]:
    """Load the source map and configured fidelity ledger for semantic verdicts.

    The generated source-record association identifies source-map items, while
    the current map and ledger decide whether those items are literal,
    convention-qualified, or corrected targets.  Resolve a configured ledger
    only inside the current paper folder; an escaping path is deliberately
    treated as unavailable and the dedicated fidelity validator reports the
    path error separately.
    """

    statement_map_path = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    statement_map = (
        run_context.exact_json_payload(statement_map_path)
        if run_context is not None
        else load_json_object(statement_map_path)
    )
    ledger_path = folder / PAPER_AUDIT_DIR / "source_proof_fidelity.json"
    fidelity_review = review_surface.get("source_proof_fidelity_review")
    if isinstance(fidelity_review, dict):
        raw_path = fidelity_review.get("ledger_file")
        if isinstance(raw_path, str) and raw_path.strip():
            relative = Path(raw_path.strip())
            if relative.is_absolute():
                return statement_map, None
            anchor = ROOT if relative.parts[:1] == ("papers",) else folder
            try:
                candidate = (anchor / relative).resolve()
                candidate.relative_to(folder.resolve())
            except (OSError, RuntimeError, ValueError):
                return statement_map, None
            ledger_path = candidate
    ledger = (
        run_context.exact_json_payload(ledger_path)
        if run_context is not None
        else load_json_object(ledger_path)
    )
    return statement_map, ledger


def source_record_target_disposition_rebind_context(
    folder: Path,
    review_surface: dict[str, object],
    raw_audit: dict[str, object],
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> tuple[Any | None, str]:
    """Load the exact optional source-status transport receipt.

    The fast evidence gate and the repository provenance gate deliberately use
    the same receipt loader.  Its returned object is constructed only after
    rebuilding every claimed rebind from the current raw-audit bytes and
    current source-map bytes; callers get no fallback for an invalid receipt.
    """

    if run_context is not None:
        evidence_payload = _legacy_source_record_audit_payload(
            run_context.evidence_context
        )
        if raw_audit is evidence_payload:
            legacy_state = _legacy_source_record_state(
                run_context.evidence_context
            )
            return (
                getattr(
                    legacy_state,
                    "administrative_projection_rebind",
                    None,
                ),
                str(
                    getattr(
                        legacy_state,
                        "administrative_projection_rebind_error",
                        "",
                    )
                    or ""
                ),
            )
    status_payload = (
        run_context.exact_json_payload(folder / "status.json")
        if run_context is not None
        else load_json_object(folder / "status.json")
    )
    # The rebind itself is optional.  ``status.json`` only selects a
    # noncanonical receipt path when it is available; without it, use the
    # canonical optional-receipt path.  That loader still rejects a present
    # malformed receipt, so an invalid status file cannot turn existing
    # rebind evidence into an unchecked fallback.
    if not isinstance(status_payload, dict):
        status_payload = {}
    audit_path = source_record_audit_file_path(folder, review_surface)
    statement_map_path = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    statement_map = (
        run_context.exact_json_payload(statement_map_path)
        if run_context is not None
        else load_json_object(statement_map_path)
    )
    try:
        from scripts.audit_evidence_integrity import (
            source_record_administrative_projection_rebind_context,
        )
        context, _receipt_path, error = (
            source_record_administrative_projection_rebind_context(
                folder,
                status_payload,
                audit_path=audit_path,
                audit_payload=raw_audit,
                statement_map_path=statement_map_path,
                statement_map=statement_map,
            )
        )
        return context, error
    except Exception as exc:  # noqa: BLE001 - receipt transport must fail closed.
        return None, "could not validate administrative source-status rebind: " + str(exc)


def evaluate_author_approved_corrected_scope(
    folder: Path, status_payload: dict[str, object]
) -> bool:
    """Run the shared corrected-scope validator without changing failures."""

    from scripts.audit_evidence_integrity import (
        author_approved_corrected_scope_contract_is_current,
    )
    return author_approved_corrected_scope_contract_is_current(
        folder, status_payload
    )


def current_author_approved_corrected_scope(
    folder: Path, status_payload: dict[str, object]
) -> bool:
    """Return whether a pinned corrected-model contract is currently complete.

    This delegates the substantive decision to the evidence-integrity gate.  In
    particular, the declaration and record names below are only identifiers
    used to find expanded Lean artifacts; the gate verifies the source pin,
    scope, semantic rows, and every reachable governing-model field.
    """

    try:
        return evaluate_author_approved_corrected_scope(folder, status_payload)
    except Exception:
        # A missing/stale/unreadable contract must fall back to ordinary
        # closeout requirements rather than silently receiving an exception.
        return False


def current_corrected_scope_semantic_items(
    folder: Path,
    status_payload: dict[str, object],
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> dict[str, dict[str, object]]:
    """Return current generated items keyed by full Lean declaration identity.

    The integrity gate has already checked the contract's per-item hashes. This
    helper deliberately never resolves by a short row/type name: a renamed or
    same-suffix declaration must regenerate and reapprove the semantic item.
    """

    current = (
        run_context.corrected_scope_current(status_payload)
        if run_context is not None
        else current_author_approved_corrected_scope(folder, status_payload)
    )
    if not current:
        return {}
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return {}
    audit_path = source_record_audit_file_path(folder, review_surface)
    audit = (
        run_context.saved_source_record_audit(audit_path)
        if run_context is not None
        else load_json_object(audit_path)
    )
    if not audit:
        return {}
    items: dict[str, dict[str, object]] = {}
    for item in audit.get("semantic_model_items") or []:
        if not isinstance(item, dict):
            continue
        qualified = str(item.get("qualified_declaration") or "").strip()
        if not qualified or qualified in items:
            return {}
        items[qualified] = item
    return items


def corrected_scope_target_row_names(
    folder: Path,
    status_payload: dict[str, object],
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> set[str]:
    """Return corrected target rows only through exact generated identities."""

    scope = status_payload.get("formalization_scope")
    if not isinstance(scope, dict):
        return set()
    model_bindings, model_binding_errors = corrected_model_scope_model_bindings(scope)
    if model_binding_errors or model_bindings is None:
        return set()
    items = current_corrected_scope_semantic_items(
        folder, status_payload, run_context=run_context
    )
    rows: set[str] = set()
    for target in model_bindings.target_model_spec_declarations:
        item = items.get(target)
        row = str(item.get("row") or "").strip() if item else ""
        if not target or not row:
            return set()
        rows.add(row)
    return rows


def is_fully_qualified_lean_identity(value: str) -> bool:
    """Return whether ``value`` is a non-short Lean declaration identity.

    This deliberately accepts Lean identifier syntax broadly, including quoted
    or Unicode components, but requires at least one namespace separator.  The
    source-record generator, rather than this textual check, resolves the
    actual constants.  Here the qualification requirement prevents a short
    type tail such as ``SourceModel`` from routing a premise.
    """

    return bool(re.fullmatch(r"[^\s.]+(?:\.[^\s.]+)+", value))


@dataclass(frozen=True)
class CurrentCorrectedModelInputBinding:
    """One generated, fully instantiated corrected-model input surface."""

    governing_model_spec_declaration: str
    source_type_canonical: str
    expanded_type: str
    alpha_normalized_type: str
    fully_qualified_expanded_type_canonical: str


@dataclass(frozen=True)
class CurrentCorrectedModelPremiseBridge:
    """Exact current corrected-model premise routes keyed by declaration FQN.

    A route exists only where the current semantic contract names the generated
    semantic item and that item names a current configured declaration.  The
    binding includes the complete input type, rather than only the record root,
    so a use of the same record at another index or parameter cannot inherit a
    waiver.  Row short names and out-of-mode review rows are deliberately not
    part of this structure.
    """

    declaration_bindings: dict[
        str, tuple[Path, tuple[CurrentCorrectedModelInputBinding, ...]]
    ]


def current_corrected_model_contract_field_items(
    folder: Path,
    status_payload: dict[str, object],
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> dict[str, dict[str, object]] | None:
    """Return only the shared validator's complete transitive field graph."""

    if run_context is not None:
        if not run_context.corrected_scope_current(status_payload):
            return None
        transferred = getattr(
            run_context.evidence_context,
            "corrected_model_field_items",
            None,
        )
        if isinstance(transferred, Mapping):
            items = dict(transferred)
            if all(
                isinstance(key, str) and isinstance(value, dict)
                for key, value in items.items()
            ):
                return items
        return None
    try:
        from scripts.audit_evidence_integrity import (
            current_author_approved_corrected_model_field_items,
        )
        items = current_author_approved_corrected_model_field_items(
            folder, status_payload
        )
    except Exception:  # noqa: BLE001 - closeout exemptions must fail closed.
        return None
    if not isinstance(items, dict):
        return None
    if any(not isinstance(key, str) or not isinstance(value, dict) for key, value in items.items()):
        return None
    return dict(items)


def corrected_model_contract_file_path(
    folder: Path, scope: dict[str, object]
) -> Path | None:
    """Resolve the corrected-model contract only inside its paper folder."""

    contract_ref = scope.get("semantic_contract")
    raw_path = contract_ref.get("path") if isinstance(contract_ref, dict) else None
    if not isinstance(raw_path, str) or not raw_path.strip():
        return None
    candidate = Path(raw_path.strip())
    if candidate.is_absolute():
        return None
    try:
        resolved = (folder / candidate).resolve()
        resolved.relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return None
    return resolved


def corrected_model_recorded_source_path(
    folder: Path, raw_path: object
) -> Path | None:
    """Resolve one generated review source without accepting a path escape."""

    if not isinstance(raw_path, str) or not raw_path.strip():
        return None
    candidate = Path(raw_path.strip())
    if not candidate.is_absolute():
        candidate = ROOT / candidate
    try:
        resolved = candidate.resolve()
        resolved.relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return None
    return resolved


def canonical_corrected_model_input_type(type_text: object) -> str:
    """Match the generator's conservative canonical form for one input type."""

    text = re.sub(r"\s+", " ", str(type_text or "").strip())
    for source, target in (
        ("<->", "↔"),
        ("->", "→"),
        ("/\\", "∧"),
        ("\\/", "∨"),
        ("<=", "≤"),
        (">=", "≥"),
        ("!=", "≠"),
    ):
        text = text.replace(source, target)
    text = re.sub(r"(?<![\w'])forall(?![\w'])", "∀", text)
    text = re.sub(r"(?<![\w'])exists(?![\w'])", "∃", text)
    text = re.sub(r"\s*([(){}\[\],:.])\s*", r"\1", text)
    text = re.sub(r"\s*(→|↔|∧|∨|=|≠|≤|≥|<|>)\s*", r"\1", text)
    while text.startswith("(") and text.endswith(")"):
        text = text[1:-1].strip()
    return text


def raw_premise_type_text(premise: str) -> str:
    """Return the written premise type without dequalifying any identifiers."""

    normalized = normalize_premise_text(premise)
    if " : " not in normalized:
        return ""
    return normalized.split(" : ", 1)[1].strip()


def current_corrected_model_premise_bridge(
    folder: Path,
    status_payload: dict[str, object],
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> CurrentCorrectedModelPremiseBridge | None:
    """Build a fail-closed corrected-model input bridge from contract evidence.

    This is intentionally a projection of exact generated identities, not a
    second review-surface resolver.  In particular, `include_names`, row short
    names, and `out_of_mode_review_surface_rows` never participate in a waiver.
    The shared evidence-integrity helper first establishes the current complete
    contract; this function then retains only the exact mapping routes and the
    complete model-input types that those routes generated.
    """

    scope = status_payload.get("formalization_scope")
    review_surface = status_payload.get("review_surface")
    if not isinstance(scope, dict) or not isinstance(review_surface, dict):
        return None
    scope_model_bindings, scope_model_binding_errors = (
        corrected_model_scope_model_bindings(scope)
    )
    if scope_model_binding_errors or scope_model_bindings is None:
        return None
    audit_path = source_record_audit_file_path(folder, review_surface)
    try:
        audit_path.resolve().relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return None
    audit = (
        run_context.saved_source_record_audit(audit_path)
        if run_context is not None
        else load_json_object(audit_path)
    )
    mapped_transitive_fields = current_corrected_model_contract_field_items(
        folder, status_payload, run_context=run_context
    )
    contract_path = corrected_model_contract_file_path(folder, scope)
    contract = (
        run_context.exact_json_payload(contract_path)
        if run_context is not None and contract_path is not None
        else load_json_object(contract_path)
        if contract_path is not None
        else None
    )
    if audit is None or mapped_transitive_fields is None or contract is None:
        return None

    raw_fields = audit.get("recursive_field_items")
    if not isinstance(raw_fields, list) or not mapped_transitive_fields:
        return None
    fields_by_key: dict[str, dict[str, object]] = {}
    fields_by_structure: dict[str, set[str]] = {}
    for raw_field in raw_fields:
        if not isinstance(raw_field, dict):
            return None
        key = str(raw_field.get("judgment_key") or "").strip()
        structure = str(raw_field.get("structure") or "").strip()
        if (
            not key
            or key in fields_by_key
            or not is_fully_qualified_lean_identity(structure)
        ):
            return None
        fields_by_key[key] = raw_field
        fields_by_structure.setdefault(structure, set()).add(key)
    mapped_field_keys = set(mapped_transitive_fields)
    if not mapped_field_keys.issubset(fields_by_key):
        return None
    legacy_permitted_roots: set[str] = set()
    target_field_keys: dict[str, set[str]] = {}
    if scope_model_bindings.uses_legacy_scalar:
        model_spec = scope_model_bindings.model_spec_declarations[0]
        model_field_keys = fields_by_structure.get(model_spec, set())
        if not model_field_keys or not model_field_keys.issubset(mapped_field_keys):
            return None
        legacy_permitted_roots = {model_spec}
        for key in mapped_field_keys:
            nested_structures = fields_by_key[key].get("nested_structures")
            if not isinstance(nested_structures, list):
                return None
            for raw_root in nested_structures:
                root = str(raw_root).strip()
                nested_field_keys = fields_by_structure.get(root, set())
                if (
                    not is_fully_qualified_lean_identity(root)
                    or not nested_field_keys
                    or not nested_field_keys.issubset(mapped_field_keys)
                ):
                    return None
                legacy_permitted_roots.add(root)
    else:
        for target, model_spec in (
            scope_model_bindings.target_model_spec_declarations.items()
        ):
            target_fields, target_field_errors = (
                corrected_model_transitively_reachable_field_items(
                    audit,
                    model_spec_declaration=model_spec,
                    target_result_declarations=[target],
                )
            )
            if (
                target_field_errors
                or not target_fields
                or not set(target_fields).issubset(mapped_field_keys)
            ):
                return None
            model_field_keys = fields_by_structure.get(model_spec, set())
            if not model_field_keys or not model_field_keys.issubset(target_fields):
                return None
            target_field_keys[target] = set(target_fields)

    raw_expected_keys = audit.get("expected_semantic_model_judgment_keys")
    raw_semantic_items = audit.get("semantic_model_items")
    if not isinstance(raw_expected_keys, list) or not isinstance(raw_semantic_items, list):
        return None
    expected_keys = [
        str(key).strip()
        for key in raw_expected_keys
        if isinstance(key, str) and str(key).strip()
    ]
    if (
        not expected_keys
        or len(expected_keys) != len(raw_expected_keys)
        or len(expected_keys) != len(set(expected_keys))
    ):
        return None
    semantic_by_key: dict[str, dict[str, object]] = {}
    semantic_by_qualified: dict[str, dict[str, object]] = {}
    for raw_item in raw_semantic_items:
        if not isinstance(raw_item, dict):
            return None
        key = str(raw_item.get("judgment_key") or "").strip()
        qualified = str(raw_item.get("qualified_declaration") or "").strip()
        if (
            not key
            or not is_fully_qualified_lean_identity(qualified)
            or key in semantic_by_key
            or qualified in semantic_by_qualified
        ):
            return None
        semantic_by_key[key] = raw_item
        semantic_by_qualified[qualified] = raw_item
    if set(expected_keys) != set(semantic_by_key):
        return None

    raw_configured_rows = audit.get("configured_review_rows")
    if not isinstance(raw_configured_rows, list):
        return None
    configured_sources: dict[str, Path] = {}
    for raw_row in raw_configured_rows:
        if not isinstance(raw_row, dict):
            return None
        qualified = str(raw_row.get("qualified_declaration") or "").strip()
        source_path = corrected_model_recorded_source_path(
            folder, raw_row.get("source_file")
        )
        source_sha = str(raw_row.get("source_sha256") or "").strip().lower()
        elaborated_signature_sha = str(
            raw_row.get("elaborated_signature_sha256") or ""
        ).strip().lower()
        if (
            not is_fully_qualified_lean_identity(qualified)
            or qualified in configured_sources
            or source_path is None
            or not re.fullmatch(r"[0-9a-f]{64}", source_sha)
            or not re.fullmatch(r"[0-9a-f]{64}", elaborated_signature_sha)
        ):
            return None
        try:
            current_sha = hashlib.sha256(source_path.read_bytes()).hexdigest()
        except OSError:
            return None
        if current_sha != source_sha:
            return None
        configured_sources[qualified] = source_path

    def mapped_declarations(
        mapping_field: str,
        declaration_field: str,
        *,
        require_all_items: bool = False,
        allow_empty: bool = False,
    ) -> set[str] | None:
        raw_mappings = contract.get(mapping_field)
        if not isinstance(raw_mappings, list):
            return None
        if not raw_mappings:
            return set() if allow_empty else None
        declarations: set[str] = set()
        mapped_keys: set[str] = set()
        for raw_mapping in raw_mappings:
            if not isinstance(raw_mapping, dict):
                return None
            key = str(raw_mapping.get("source_record_item_key") or "").strip()
            qualified = str(raw_mapping.get(declaration_field) or "").strip()
            item = semantic_by_key.get(key)
            if (
                not key
                or not is_fully_qualified_lean_identity(qualified)
                or item is None
                or key in mapped_keys
                or qualified in declarations
                or str(item.get("qualified_declaration") or "").strip() != qualified
                or qualified not in configured_sources
            ):
                return None
            mapped_keys.add(key)
            declarations.add(qualified)
        if require_all_items and mapped_keys != set(expected_keys):
            return None
        return declarations

    target_declarations = mapped_declarations(
        "target_result_mappings", "target_declaration"
    )
    assumption_declarations = mapped_declarations(
        "assumption_mappings", "assumption_declaration", allow_empty=True
    )
    semantic_declarations = mapped_declarations(
        "semantic_item_mappings",
        "qualified_declaration",
        require_all_items=True,
    )
    if (
        target_declarations is None
        or assumption_declarations is None
        or semantic_declarations is None
    ):
        return None
    scope_targets = set(scope_model_bindings.target_model_spec_declarations)
    if (
        not scope_targets
        or target_declarations != scope_targets
    ):
        return None
    raw_target_mappings = contract.get("target_result_mappings")
    if not isinstance(raw_target_mappings, list):
        return None
    target_mapping_roots: dict[str, str] = {}
    for raw_mapping in raw_target_mappings:
        if not isinstance(raw_mapping, dict):
            return None
        target = str(raw_mapping.get("target_declaration") or "").strip()
        expected_root = scope_model_bindings.target_model_spec_declarations.get(target)
        mapped_root = str(raw_mapping.get("model_spec_declaration") or "").strip()
        if (
            not target
            or target in target_mapping_roots
            or expected_root is None
            or (mapped_root and mapped_root != expected_root)
            or (not mapped_root and not scope_model_bindings.uses_legacy_scalar)
        ):
            return None
        target_mapping_roots[target] = expected_root
    if set(target_mapping_roots) != scope_targets:
        return None
    covered_declarations = (
        target_declarations | assumption_declarations | semantic_declarations
    )
    if not scope_model_bindings.uses_legacy_scalar:
        # Only target rows have an exact target-to-model assignment in the
        # multi-model schema. Support and assumption rows must earn source
        # treatment through their own route instead of borrowing a sibling
        # target's governing model.
        covered_declarations = target_declarations
    if not covered_declarations:
        return None

    declaration_bindings: dict[
        str, tuple[Path, tuple[CurrentCorrectedModelInputBinding, ...]]
    ] = {}
    for qualified in sorted(covered_declarations):
        item = semantic_by_qualified.get(qualified)
        if item is None:
            return None
        if scope_model_bindings.uses_legacy_scalar:
            permitted_roots = legacy_permitted_roots
        else:
            expected_root = target_mapping_roots.get(qualified)
            if expected_root is None or not target_field_keys.get(qualified):
                return None
            # Do not promote nested roots or a paired wrapper to a governing
            # root for a target that was approved against one exact model.
            permitted_roots = {expected_root}
        expanded_surface = item.get("expanded_lean_surface")
        if not isinstance(expanded_surface, dict):
            return None
        raw_binder_domains = expanded_surface.get("binder_domains")
        raw_surface_roots = expanded_surface.get("record_roots")
        if not isinstance(raw_binder_domains, list) or not isinstance(raw_surface_roots, list):
            return None
        binder_surfaces: set[tuple[str, str]] = set()
        for raw_domain in raw_binder_domains:
            if not isinstance(raw_domain, dict):
                return None
            expanded_type = str(raw_domain.get("expanded_type") or "").strip()
            alpha_normalized_type = str(
                raw_domain.get("alpha_normalized_type") or ""
            ).strip()
            if not expanded_type or not alpha_normalized_type:
                return None
            binder_surfaces.add((expanded_type, alpha_normalized_type))
        surface_roots = {
            str(root).strip()
            for root in raw_surface_roots
            if str(root).strip()
        }
        bindings: list[CurrentCorrectedModelInputBinding] = []
        raw_bindings = item.get("record_input_bindings")
        if not isinstance(raw_bindings, list):
            return None
        for raw_binding in raw_bindings:
            if not isinstance(raw_binding, dict):
                return None
            roots = {
                str(root).strip()
                for root in raw_binding.get("record_roots") or []
                if str(root).strip()
            }
            if not roots & permitted_roots:
                continue
            if len(roots) != 1 or next(iter(roots)) not in permitted_roots:
                return None
            source_type_canonical = str(
                raw_binding.get("source_type_canonical") or ""
            ).strip()
            expanded_type = str(raw_binding.get("expanded_type") or "").strip()
            alpha_normalized_type = str(
                raw_binding.get("alpha_normalized_type") or ""
            ).strip()
            fully_qualified_expanded_type_canonical = str(
                raw_binding.get("fully_qualified_expanded_type_canonical") or ""
            ).strip()
            if (
                not source_type_canonical
                or source_type_canonical
                != canonical_corrected_model_input_type(source_type_canonical)
                or not expanded_type
                or not alpha_normalized_type
                or not fully_qualified_expanded_type_canonical
                or fully_qualified_expanded_type_canonical
                != canonical_corrected_model_input_type(
                    fully_qualified_expanded_type_canonical
                )
                or (expanded_type, alpha_normalized_type) not in binder_surfaces
                or next(iter(roots)) not in surface_roots
            ):
                # Legacy root-only bindings are insufficient for a corrected
                # model waiver.  Regenerate the semantic audit instead of
                # treating an old root match as a full model premise.
                return None
            bindings.append(
                CurrentCorrectedModelInputBinding(
                    governing_model_spec_declaration=next(iter(roots)),
                    source_type_canonical=source_type_canonical,
                    expanded_type=expanded_type,
                    alpha_normalized_type=alpha_normalized_type,
                    fully_qualified_expanded_type_canonical=(
                        fully_qualified_expanded_type_canonical
                    ),
                )
            )
        if bindings:
            declaration_bindings[qualified] = (
                configured_sources[qualified],
                tuple(bindings),
            )
    return (
        CurrentCorrectedModelPremiseBridge(declaration_bindings)
        if declaration_bindings
        else None
    )


def premise_is_current_corrected_model_contract_input(
    premise: str,
    declaration: LeanDeclaration,
    bridge: CurrentCorrectedModelPremiseBridge | None,
    declaration_index: dict[str, list[LeanDeclaration]],
) -> bool:
    """Whether a premise equals an exact generated corrected-model input.

    The declaration is selected by its full identity and source path.  The
    premise type must equal the generated binding's entire canonical type,
    including every model parameter.  `declaration_index` remains in the
    signature for callers but is deliberately unused: resolving a short type
    head is the ambiguity this bridge exists to avoid.
    """

    del declaration_index
    if bridge is None:
        return False
    qualified = qualified_declaration_identity(declaration)
    route = bridge.declaration_bindings.get(qualified)
    if route is None:
        return False
    source_path, bindings = route
    try:
        if declaration.path.resolve() != source_path:
            return False
    except (OSError, RuntimeError):
        return False
    premise_type = canonical_corrected_model_input_type(raw_premise_type_text(premise))
    if not premise_type:
        return False
    return any(
        premise_type
        in {
            binding.source_type_canonical,
            binding.fully_qualified_expanded_type_canonical,
        }
        for binding in bindings
    )


def qualified_declaration_identity(declaration: LeanDeclaration) -> str:
    """Return a declaration's namespace-qualified identity from its own file."""

    if declaration.qualified_name:
        return declaration.qualified_name

    try:
        text = declaration.path.read_text(encoding="utf-8")
    except OSError:
        return ""
    return qualified_review_decl_name(text, declaration.line, declaration.name)


@dataclass(frozen=True)
class CurrentNamedTheorySemanticReviewRow:
    """One receipt-pinned PaperInterface declaration selected in normal mode."""

    source_path: Path
    source_sha256: str
    elaborated_signature_sha256: str
    individual_direct_source_route: bool


@dataclass(frozen=True)
class CurrentNamedTheorySemanticReviewSurface:
    """Exact semantic-model declarations eligible for normal-mode filtering.

    This is deliberately keyed only by fully qualified declarations.  A
    configured short row name, an auxiliary classification, or a source-map
    label cannot select or suppress a hidden-premise audit.
    """

    rows: dict[str, CurrentNamedTheorySemanticReviewRow]


@dataclass(frozen=True)
class TransparentSpecReceiptIdentity:
    """Exact direct-proof and transparent-Spec identities from one receipt."""

    direct_declaration_sha256: str
    direct_elaborated_signature_sha256: str
    spec_qualified_declaration: str
    spec_declaration_sha256: str


def _receipt_declaration_sha_for_qualified(
    raw_identity: object, qualified_declaration: str
) -> str | None:
    """Return one receipt declaration hash only for its exact FQN."""

    if not isinstance(raw_identity, Mapping):
        return None
    qualified = str(raw_identity.get("qualified_declaration") or "").strip()
    declaration_sha = str(raw_identity.get("declaration_sha256") or "").strip().lower()
    if (
        qualified != qualified_declaration
        or not re.fullmatch(r"[0-9a-f]{64}", declaration_sha)
    ):
        return None
    return declaration_sha


def _receipt_signature_sha_for_qualified(
    raw_identity: object, qualified_declaration: str
) -> str | None:
    """Return one receipt elaborated-signature hash only for its exact FQN."""

    if not isinstance(raw_identity, Mapping):
        return None
    qualified = str(raw_identity.get("qualified_declaration") or "").strip()
    signature_sha = str(
        raw_identity.get("elaborated_signature_sha256") or ""
    ).strip().lower()
    if qualified != qualified_declaration or not re.fullmatch(
        r"[0-9a-f]{64}", signature_sha
    ):
        return None
    return signature_sha


def _semantic_contract_source_identity_fingerprints(
    raw_identities: object,
    *,
    direct_declaration: str,
    spec_declaration: str,
) -> tuple[str, ...] | None:
    """Normalize group source pins without relying on source-map storage keys.

    The map's storage key is administrative.  The generated direct/Spec
    association is instead tied to content pins, source location/kind, and its
    exact two declaration identities.
    """

    if not isinstance(raw_identities, list) or not raw_identities:
        return None
    fingerprints: list[str] = []
    for raw_identity in raw_identities:
        if not isinstance(raw_identity, Mapping):
            return None
        source_kind = str(raw_identity.get("source_kind") or "").strip()
        source_location = str(raw_identity.get("source_location") or "").strip()
        source_map_sha = str(raw_identity.get("source_map_item_sha256") or "").strip()
        source_semantic_sha = str(
            raw_identity.get("source_semantic_sha256") or ""
        ).strip()
        semantic_contract = raw_identity.get("semantic_contract")
        if (
            not source_kind
            or not source_location
            or not re.fullmatch(r"[0-9a-f]{64}", source_map_sha)
            or not re.fullmatch(r"[0-9a-f]{64}", source_semantic_sha)
            or not isinstance(semantic_contract, Mapping)
            or str(semantic_contract.get("evidence_declaration") or "").strip()
            != direct_declaration
            or str(semantic_contract.get("spec_declaration") or "").strip()
            != spec_declaration
            or not str(semantic_contract.get("evidence_mode") or "").strip()
            or not str(semantic_contract.get("semantic_shape") or "").strip()
        ):
            return None
        fingerprints.append(
            json.dumps(
                {
                    "semantic_contract": {
                        "evidence_declaration": direct_declaration,
                        "evidence_mode": str(
                            semantic_contract.get("evidence_mode") or ""
                        ).strip(),
                        "semantic_shape": str(
                            semantic_contract.get("semantic_shape") or ""
                        ).strip(),
                        "spec_declaration": spec_declaration,
                    },
                    "source_kind": source_kind,
                    "source_location": source_location,
                    "source_map_item_sha256": source_map_sha,
                    "source_semantic_sha256": source_semantic_sha,
                },
                sort_keys=True,
                separators=(",", ":"),
            )
        )
    return tuple(sorted(fingerprints))


def semantic_model_item_exact_receipt_identity(
    item: Mapping[str, object], *, qualified_declaration: str
) -> tuple[str, str] | None:
    """Return the exact direct declaration/signature pins for one semantic item.

    Most semantic items have a single reviewed declaration.  A generated
    direct/transparent-Spec contract deliberately has two declarations: the
    direct theorem is the paper-facing endpoint, while the transparent Spec
    body supplies the semantic surface.  Both forms are valid only when their
    generated identities, structural equality record, source association, and
    elaborated-signature pins agree exactly.  No row label, short name, or
    source-map storage key participates in this selection.
    """

    if "semantic_contract_group" not in item:
        declaration_sha = _receipt_declaration_sha_for_qualified(
            item.get("reviewed_declaration_identity"), qualified_declaration
        )
        raw_signatures = item.get("reviewed_elaborated_signature_identities")
        if not isinstance(raw_signatures, list) or len(raw_signatures) != 1:
            return None
        signature_sha = _receipt_signature_sha_for_qualified(
            raw_signatures[0], qualified_declaration
        )
        if declaration_sha is None or signature_sha is None:
            return None
        return declaration_sha, signature_sha

    group = item.get("semantic_contract_group")
    if (
        not isinstance(group, Mapping)
        or not schema_version_is_exact(group.get("schema"), 1)
        or group.get("structural_alpha_normalized_equal") is not True
    ):
        return None
    raw_members = group.get("member_rows")
    if not isinstance(raw_members, list) or len(raw_members) != 2:
        return None
    members_by_role: dict[str, Mapping[str, object]] = {}
    for raw_member in raw_members:
        if not isinstance(raw_member, Mapping):
            return None
        role = str(raw_member.get("role") or "").strip()
        member_qualified = str(raw_member.get("qualified_declaration") or "").strip()
        if (
            role not in {"direct_evidence", "transparent_spec"}
            or role in members_by_role
            or not is_fully_qualified_lean_identity(member_qualified)
        ):
            return None
        members_by_role[role] = raw_member
    if set(members_by_role) != {"direct_evidence", "transparent_spec"}:
        return None
    direct_member = members_by_role["direct_evidence"]
    spec_member = members_by_role["transparent_spec"]
    direct_member_qualified = str(
        direct_member.get("qualified_declaration") or ""
    ).strip()
    spec_member_qualified = str(
        spec_member.get("qualified_declaration") or ""
    ).strip()
    if (
        direct_member_qualified != qualified_declaration
        or spec_member_qualified == qualified_declaration
    ):
        return None
    direct_declaration_sha = _receipt_declaration_sha_for_qualified(
        direct_member.get("reviewed_declaration_identity"), qualified_declaration
    )
    spec_declaration_sha = _receipt_declaration_sha_for_qualified(
        spec_member.get("reviewed_declaration_identity"), spec_member_qualified
    )
    if direct_declaration_sha is None or spec_declaration_sha is None:
        return None

    direct_surface = group.get("direct_evidence_type")
    spec_surface = group.get("surface_root")
    if (
        not isinstance(direct_surface, Mapping)
        or not isinstance(spec_surface, Mapping)
        or str(direct_surface.get("qualified_declaration") or "").strip()
        != qualified_declaration
        or str(spec_surface.get("kind") or "").strip()
        != "transparent_spec_body"
        or str(spec_surface.get("qualified_declaration") or "").strip()
        != spec_member_qualified
    ):
        return None
    direct_structure = direct_surface.get("structural_alpha_normalized_surface")
    spec_structure = spec_surface.get("structural_alpha_normalized_surface")
    if (
        not isinstance(direct_structure, Mapping)
        or not isinstance(spec_structure, Mapping)
        or direct_structure != spec_structure
    ):
        return None

    semantic_origin = item.get("semantic_surface_origin")
    if (
        not isinstance(semantic_origin, Mapping)
        or str(semantic_origin.get("kind") or "").strip()
        != "transparent_spec_body"
        or str(semantic_origin.get("qualified_declaration") or "").strip()
        != spec_member_qualified
        # The semantic surface comes from the transparent Spec body, but the
        # audited receipt must remain owned by the direct theorem.  Accepting
        # the Spec identity here would make result-level paths on the direct
        # theorem unjoinable and could let a semantic review drift away from
        # its proof endpoint.
        or _receipt_declaration_sha_for_qualified(
            item.get("reviewed_declaration_identity"), qualified_declaration
        )
        != direct_declaration_sha
    ):
        return None

    # A collapsed direct/Spec item has exactly one proof-target signature:
    # the direct evidence theorem.  The paired transparent Spec is pinned by
    # its declaration identity, source association, and structural equality
    # to the direct theorem; it is semantic surface rather than a second
    # theorem-proof endpoint.
    raw_signatures = item.get("reviewed_elaborated_signature_identities")
    if not isinstance(raw_signatures, list) or len(raw_signatures) != 1:
        return None
    direct_signature_sha = _receipt_signature_sha_for_qualified(
        raw_signatures[0], qualified_declaration
    )
    if direct_signature_sha is None:
        return None

    association = item.get("semantic_contract_source_association")
    if (
        not isinstance(association, Mapping)
        or not schema_version_is_exact(association.get("schema"), 2)
        or str(association.get("role") or "").strip() != "direct_evidence"
        or str(association.get("review_scope") or "").strip()
        != "individual_row_only"
        or str(association.get("structural_pairing") or "").strip()
        != "not_asserted_by_source_association"
        or str(association.get("paired_qualified_declaration") or "").strip()
        != spec_member_qualified
        or _receipt_declaration_sha_for_qualified(
            association.get("reviewed_declaration_identity"), qualified_declaration
        )
        != direct_declaration_sha
        or _receipt_signature_sha_for_qualified(
            association.get("reviewed_elaborated_signature_identity"),
            qualified_declaration,
        )
        != direct_signature_sha
        or not re.fullmatch(
            r"[0-9a-f]{64}",
            str(association.get("semantic_association_sha256") or "").strip(),
        )
    ):
        return None
    group_source_pins = _semantic_contract_source_identity_fingerprints(
        group.get("source_item_identities"),
        direct_declaration=qualified_declaration,
        spec_declaration=spec_member_qualified,
    )
    association_source_pins = _semantic_contract_source_identity_fingerprints(
        association.get("source_item_identities"),
        direct_declaration=qualified_declaration,
        spec_declaration=spec_member_qualified,
    )
    if group_source_pins is None or group_source_pins != association_source_pins:
        return None
    return direct_declaration_sha, direct_signature_sha


def semantic_model_item_transparent_spec_receipt_identity(
    item: Mapping[str, object], *, qualified_declaration: str
) -> TransparentSpecReceiptIdentity | None:
    """Return an exact cross-file transparent-Spec route when one is recorded.

    The ordinary semantic-model receipt is owned by the proof endpoint.  This
    helper does not move that ownership.  It first validates the complete
    generated direct/Spec contract, then returns the transparent Spec identity
    whose Lean-owned structural surface was proved equal to the endpoint.
    """

    direct_identity = semantic_model_item_exact_receipt_identity(
        item, qualified_declaration=qualified_declaration
    )
    if direct_identity is None:
        return None
    group = item.get("semantic_contract_group")
    if not isinstance(group, Mapping):
        return None
    raw_members = group.get("member_rows")
    if not isinstance(raw_members, list):
        return None
    spec_members = [
        member
        for member in raw_members
        if isinstance(member, Mapping)
        and str(member.get("role") or "").strip() == "transparent_spec"
    ]
    if len(spec_members) != 1:
        return None
    spec_member = spec_members[0]
    spec_qualified = str(spec_member.get("qualified_declaration") or "").strip()
    spec_declaration_sha = _receipt_declaration_sha_for_qualified(
        spec_member.get("reviewed_declaration_identity"), spec_qualified
    )
    semantic_origin = item.get("semantic_surface_origin")
    if (
        not is_fully_qualified_lean_identity(spec_qualified)
        or spec_declaration_sha is None
        or not isinstance(semantic_origin, Mapping)
        or str(semantic_origin.get("kind") or "").strip()
        != "transparent_spec_body"
        or str(semantic_origin.get("qualified_declaration") or "").strip()
        != spec_qualified
    ):
        return None
    direct_declaration_sha, direct_signature_sha = direct_identity
    return TransparentSpecReceiptIdentity(
        direct_declaration_sha256=direct_declaration_sha,
        direct_elaborated_signature_sha256=direct_signature_sha,
        spec_qualified_declaration=spec_qualified,
        spec_declaration_sha256=spec_declaration_sha,
    )


def configured_semantic_review_row_identity(
    folder: Path,
    configured_row: Mapping[str, object],
    declaration_index: dict[str, list[LeanDeclaration]],
    *,
    qualified_declaration: str,
    expected_declaration_sha256: str,
    expected_elaborated_signature_sha256: str | None,
) -> tuple[CurrentNamedTheorySemanticReviewRow | None, str]:
    """Validate one configured row against its current exact Lean source."""

    source_path = corrected_model_recorded_source_path(
        folder, configured_row.get("source_file")
    )
    if source_path is None:
        return None, "has no safely resolved configured receipt route"
    source_sha = str(configured_row.get("source_sha256") or "").strip().lower()
    signature_sha = str(
        configured_row.get("elaborated_signature_sha256") or ""
    ).strip().lower()
    declaration_source = configured_row.get("lean_source_declaration")
    if (
        not re.fullmatch(r"[0-9a-f]{64}", source_sha)
        or not re.fullmatch(r"[0-9a-f]{64}", signature_sha)
        or not isinstance(declaration_source, str)
        or hashlib.sha256(declaration_source.encode("utf-8")).hexdigest()
        != expected_declaration_sha256
    ):
        return None, "lacks a complete FQN/source/signature receipt route"
    if (
        expected_elaborated_signature_sha256 is not None
        and signature_sha != expected_elaborated_signature_sha256
    ):
        return None, "elaborated-signature identity does not exactly match its configured FQN route"
    try:
        if hashlib.sha256(source_path.read_bytes()).hexdigest() != source_sha:
            return None, "receipt source bytes are stale"
    except OSError:
        return None, "receipt source file is unavailable"
    try:
        matching_declarations = [
            declaration
            for declaration in declaration_index.get(qualified_declaration, [])
            if declaration.path.resolve() == source_path
            and qualified_declaration_identity(declaration) == qualified_declaration
        ]
    except (OSError, RuntimeError):
        return None, "declaration source cannot be resolved safely"
    if len(matching_declarations) != 1:
        return None, "declaration does not resolve uniquely to its exact receipt source"
    return (
        CurrentNamedTheorySemanticReviewRow(
            source_path=source_path,
            source_sha256=source_sha,
            elaborated_signature_sha256=signature_sha,
            individual_direct_source_route=False,
        ),
        "",
    )


def semantic_model_item_has_individual_direct_source_route(
    item: Mapping[str, object],
    *,
    qualified_declaration: str,
    declaration_sha256: str,
    elaborated_signature_sha256: str,
) -> bool:
    """Require one receipt-pinned named-source route for a paper-facing row.

    This is intentionally stronger than a row label or a source-looking
    declaration name.  It accepts an individual result only when the current
    v10 semantic receipt binds exactly one named source item to the exact
    declaration and elaborated signature through a direct source route.
    """

    association = item.get("source_statement_association")
    if not isinstance(association, Mapping):
        return False
    if (
        not schema_version_is_exact(association.get("schema"), 2)
        or str(association.get("role") or "").strip()
        != EXPLICIT_DIRECT_SOURCE_ROUTE_ROLE
        or str(association.get("association_origin") or "").strip()
        != EXPLICIT_DIRECT_SOURCE_ROUTE_ORIGIN
        or str(association.get("review_scope") or "").strip()
        != "individual_row_only"
        or str(association.get("structural_pairing") or "").strip()
        != "not_applicable_direct_source_route"
    ):
        return False
    association_sha = str(association.get("semantic_association_sha256") or "").strip()
    if not re.fullmatch(r"[0-9a-f]{64}", association_sha):
        return False
    if association.get("reviewed_declaration_identity") != {
        "qualified_declaration": qualified_declaration,
        "declaration_sha256": declaration_sha256,
    }:
        return False
    if association.get("reviewed_elaborated_signature_identity") != {
        "qualified_declaration": qualified_declaration,
        "elaborated_signature_sha256": elaborated_signature_sha256,
    }:
        return False
    source_items = association.get("source_item_identities")
    if not isinstance(source_items, list) or len(source_items) != 1:
        return False
    source_item = source_items[0]
    if not isinstance(source_item, Mapping):
        return False
    required_text = (
        source_item.get("source_key"),
        source_item.get("source_kind"),
        source_item.get("source_location"),
    )
    required_hashes = (
        source_item.get("source_map_item_sha256"),
        source_item.get("source_semantic_sha256"),
    )
    return all(isinstance(value, str) and value.strip() for value in required_text) and all(
        isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value.strip())
        for value in required_hashes
    )


def formalization_scope_target_declarations_for_receipt(
    status_payload: dict[str, object],
) -> tuple[set[str] | None, str]:
    """Return exact governing targets, or an error instead of a name fallback."""

    scope = status_payload.get("formalization_scope")
    if scope is None:
        return set(), ""
    if not isinstance(scope, dict):
        return None, "formalization_scope is not an object"
    raw_targets = scope.get("target_result_declarations")
    if raw_targets is None:
        return set(), ""
    if not isinstance(raw_targets, list):
        return None, "formalization_scope.target_result_declarations is not a list"
    targets = [str(target).strip() for target in raw_targets]
    if (
        any(not is_fully_qualified_lean_identity(target) for target in targets)
        or len(targets) != len(set(targets))
    ):
        return (
            None,
            "formalization_scope.target_result_declarations lacks unique exact "
            "fully qualified declarations",
        )
    return set(targets), ""


def current_named_theory_semantic_review_surface(
    folder: Path,
    status_payload: dict[str, object],
    declaration_index: dict[str, list[LeanDeclaration]],
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> tuple[CurrentNamedTheorySemanticReviewSurface | None, str]:
    """Load a fail-closed normal-mode semantic surface from the raw receipt.

    The hidden-premise pass is broader than ordinary named-theory source
    coverage by default.  It can be narrowed only when the saved current v10
    receipt establishes every selected declaration through its exact FQN,
    source-file bytes, and elaborated signature pin.  The caller treats an
    error as a closeout failure and retains the broad pass.  Deep all-prose
    mode intentionally returns no filter, so it retains every review row.
    """

    if run_context is not None:
        exact_status = run_context.exact_json_payload(folder / "status.json")
        if isinstance(exact_status, dict):
            # Generated repository status is presentation/index data and may
            # lag a paper-local closeout edit. Semantic-lane selection must use
            # the immutable paper-local status captured by this transaction.
            status_payload = exact_status

    review_surface = status_payload.get("review_surface")
    semantic_review_configured = isinstance(
        review_surface, dict
    ) and isinstance(review_surface.get("semantic_model_review"), dict)
    if not isinstance(review_surface, dict):
        return (
            (None, "review_surface is not an object")
            if semantic_review_configured
            else (None, "")
        )
    # A current v11 closeout selects one expanded Lean semantic object per
    # source claim: a Spec plus proof endpoint for results, or the full direct
    # declaration for definitions/models/algorithms. Requiring the older
    # receipt's whole PaperInterface byte hash here would make comments,
    # declaration order, and file moves semantic.
    v11_names = v11_source_claim_review_names(status_payload)
    if (
        run_context is not None
        and run_context.selected_v11_closeout
        and v11_names is not None
    ):
        v11_current = run_context.current_v11_closeout
        v11_error = run_context.v11_direct_semantic_review_error
        if v11_current:
            selected_declarations: dict[str, LeanDeclaration] = {}
            for name in sorted(v11_names):
                resolved = resolve_declaration_name(declaration_index, name)
                if len(resolved) != 1:
                    return None, f"v11 source Spec does not resolve uniquely: {name}"
                selected_declarations[
                    qualified_declaration_identity(resolved[0])
                ] = resolved[0]
            result_routes, direct_routes, route_findings = (
                current_v11_typed_review_routes(
                    folder.name,
                    folder,
                    v11_names,
                    run_context=run_context,
                )
            )
            if route_findings:
                return None, "; ".join(finding.message for finding in route_findings)
            if set(result_routes) | set(direct_routes) != set(v11_names):
                return None, "v11 source claims do not have one typed source-map route each"
            # The builder-issued v11 verdict above has already compared every
            # selected byte-pinned source claim to its current Lean semantic
            # object and reviewed every material paper/library prerequisite.
            # The retained Lean graph separately owns typed proof equality and
            # axiom closure, so this projection does not replay either batch.
            interface_path = review_surface_source_file_path(
                folder, review_surface
            ).resolve()
            try:
                interface_sha256 = hashlib.sha256(
                    interface_path.read_bytes()
                ).hexdigest()
            except OSError:
                return None, "v11 PaperInterface source is unavailable"
            rows: dict[str, CurrentNamedTheorySemanticReviewRow] = {}
            for qualified, declaration in selected_declarations.items():
                if declaration.path.resolve() != interface_path:
                    return None, f"v11 source Spec is outside PaperInterface: {qualified}"
                rows[qualified] = CurrentNamedTheorySemanticReviewRow(
                    source_path=interface_path,
                    source_sha256=interface_sha256,
                    elaborated_signature_sha256="",
                    individual_direct_source_route=True,
                )
            return CurrentNamedTheorySemanticReviewSurface(rows), ""
        return None, "v11 direct semantic review is not current: " + (
            v11_error or "the selected v11 semantic gate did not pass"
        )

    audit_path = source_record_audit_file_path(folder, review_surface)
    try:
        audit_path.resolve().relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return None, "source-record audit path escapes the paper folder"
    payload = (
        run_context.saved_source_record_audit(audit_path)
        if run_context is not None
        else load_json_object(audit_path)
    )
    if payload is None:
        return (
            (None, "current semantic-model review has no saved source-record receipt")
            if semantic_review_configured
            else (None, "")
        )
    prompt_version = str(payload.get("prompt_version") or "").strip()
    if prompt_version != REQUIRED_SOURCE_RECORD_PROMPT_VERSION:
        return (
            (
                None,
                "semantic-model review requires the current v10 source-record receipt",
            )
            if semantic_review_configured
            else (None, "")
        )
    integrity_error = source_record_raw_integrity_error_if_current(payload)
    if integrity_error:
        return None, "source-record receipt is not current: " + integrity_error
    (
        semantic_contract_revalidation,
        semantic_contract_revalidation_error,
    ) = source_record_semantic_contract_revalidation_for_payload(
        folder,
        payload,
        run_context=run_context,
    )
    if semantic_contract_revalidation_error:
        return (
            None,
            "source-record semantic-contract revalidation is invalid: "
            + semantic_contract_revalidation_error,
        )
    semantic_surface_error = source_record_effective_semantic_surface_error(
        payload,
        semantic_contract_revalidation=semantic_contract_revalidation,
    )
    if semantic_surface_error:
        return None, "source-record receipt has invalid semantic surface: " + semantic_surface_error
    target_route_error = source_record_target_route_error(payload)
    if target_route_error:
        return None, "source-record receipt has invalid semantic target routing: " + target_route_error

    coverage_mode = str(payload.get("source_coverage_mode") or "").strip()
    if coverage_mode == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS:
        # Deep mode deliberately receives no scope projection: all review rows
        # remain subject to the hidden-premise pass.
        return None, ""
    if coverage_mode != NAMED_THEORETICAL_STATEMENTS:
        return (
            None,
            "source-record receipt has no valid source_coverage_mode for a "
            "semantic hidden-premise projection",
        )

    raw_semantic_items = payload.get("semantic_model_items")
    if not isinstance(raw_semantic_items, list):
        return (
            (None, "normal named-theory receipt lacks semantic_model_items")
            if semantic_review_configured
            else (None, "")
        )
    if not raw_semantic_items:
        return (
            (None, "normal named-theory semantic review selected no semantic-model rows")
            if semantic_review_configured
            else (None, "")
        )

    raw_expected_keys = payload.get("expected_semantic_model_judgment_keys")
    if not isinstance(raw_expected_keys, list):
        return None, "normal named-theory receipt lacks expected semantic-model judgment keys"
    expected_keys = [str(key).strip() for key in raw_expected_keys]
    if (
        any(not key for key in expected_keys)
        or len(expected_keys) != len(raw_expected_keys)
        or len(expected_keys) != len(set(expected_keys))
    ):
        return None, "normal named-theory receipt has malformed semantic-model judgment keys"

    semantic_by_qualified: dict[str, tuple[str, dict[str, object]]] = {}
    semantic_keys: set[str] = set()
    for raw_item in raw_semantic_items:
        if not isinstance(raw_item, dict):
            return None, "normal named-theory receipt has a malformed semantic-model item"
        judgment_key = str(raw_item.get("judgment_key") or "").strip()
        direct_qualified = str(raw_item.get("qualified_declaration") or "").strip()
        if (
            not judgment_key
            or judgment_key in semantic_keys
            or not is_fully_qualified_lean_identity(direct_qualified)
            or direct_qualified in semantic_by_qualified
        ):
            return None, "semantic-model item has an ambiguous or incomplete FQN identity"
        semantic_keys.add(judgment_key)
        semantic_by_qualified[direct_qualified] = (judgment_key, raw_item)
    if semantic_keys != set(expected_keys):
        return None, "semantic-model items do not exactly match the receipt judgment-key ledger"

    raw_configured_rows = payload.get("configured_review_rows")
    if not isinstance(raw_configured_rows, list):
        return None, "normal named-theory receipt lacks configured review-row identities"
    configured_by_qualified: dict[str, list[dict[str, object]]] = {}
    for raw_row in raw_configured_rows:
        if not isinstance(raw_row, dict):
            continue
        qualified = str(raw_row.get("qualified_declaration") or "").strip()
        if is_fully_qualified_lean_identity(qualified):
            configured_by_qualified.setdefault(qualified, []).append(raw_row)

    interface_path = (folder / "PaperInterface.lean").resolve()
    if not interface_path.exists():
        return None, "PaperInterface.lean is missing while selecting semantic review rows"
    selected_rows: dict[str, CurrentNamedTheorySemanticReviewRow] = {}
    selected_surface_by_direct: dict[str, str] = {}
    for qualified, (_judgment_key, raw_item) in semantic_by_qualified.items():
        configured_rows = configured_by_qualified.get(qualified, [])
        if len(configured_rows) != 1:
            return (
                None,
                "semantic-model declaration has no unique configured receipt route: "
                + qualified,
            )
        configured_row = configured_rows[0]
        direct_source_path = corrected_model_recorded_source_path(
            folder, configured_row.get("source_file")
        )
        if direct_source_path is None:
            return (
                None,
                "semantic-model declaration has no safely resolved configured "
                "receipt route: " + qualified,
            )
        # Only an exact PaperInterface route can narrow this audit. Semantic
        # support rows in Assumptions.lean are audited by the source-record
        # lane, but their intentionally aggregate-only signature metadata must
        # not block the independent PaperInterface projection.
        if direct_source_path != interface_path and "semantic_contract_group" not in raw_item:
            continue
        receipt_identity = semantic_model_item_exact_receipt_identity(
            raw_item, qualified_declaration=qualified
        )
        if receipt_identity is None:
            return (
                None,
                "PaperInterface semantic-model declaration has an ambiguous or "
                "incomplete exact identity: " + qualified,
            )
        declaration_sha, semantic_signature_sha = receipt_identity
        direct_row, direct_row_error = configured_semantic_review_row_identity(
            folder,
            configured_row,
            declaration_index,
            qualified_declaration=qualified,
            expected_declaration_sha256=declaration_sha,
            expected_elaborated_signature_sha256=semantic_signature_sha,
        )
        if direct_row_error or direct_row is None:
            return (
                None,
                "semantic-model declaration " + direct_row_error + ": " + qualified,
            )
        individual_direct_source_route = (
            semantic_model_item_has_individual_direct_source_route(
                raw_item,
                qualified_declaration=qualified,
                declaration_sha256=declaration_sha,
                elaborated_signature_sha256=semantic_signature_sha,
            )
        )
        if direct_source_path == interface_path:
            selected_rows[qualified] = CurrentNamedTheorySemanticReviewRow(
                source_path=direct_row.source_path,
                source_sha256=direct_row.source_sha256,
                elaborated_signature_sha256=direct_row.elaborated_signature_sha256,
                individual_direct_source_route=individual_direct_source_route,
            )
            selected_surface_by_direct[qualified] = qualified
            continue

        transparent_spec = semantic_model_item_transparent_spec_receipt_identity(
            raw_item, qualified_declaration=qualified
        )
        if transparent_spec is None:
            return (
                None,
                "cross-file semantic-model declaration lacks an exact transparent-Spec "
                "receipt route: " + qualified,
            )
        spec_qualified = transparent_spec.spec_qualified_declaration
        spec_configured_rows = configured_by_qualified.get(spec_qualified, [])
        if len(spec_configured_rows) != 1:
            return (
                None,
                "transparent Spec has no unique configured receipt route: "
                + spec_qualified,
            )
        spec_row, spec_row_error = configured_semantic_review_row_identity(
            folder,
            spec_configured_rows[0],
            declaration_index,
            qualified_declaration=spec_qualified,
            expected_declaration_sha256=transparent_spec.spec_declaration_sha256,
            # The receipt-owned proof endpoint supplies the elaborated proof
            # signature.  The Spec row is independently source/declaration
            # pinned and its Lean-generated structural surface is exactly
            # paired with that endpoint by the validated contract above.
            expected_elaborated_signature_sha256=None,
        )
        if spec_row_error or spec_row is None:
            return (
                None,
                "transparent Spec " + spec_row_error + ": " + spec_qualified,
            )
        if spec_row.source_path != interface_path:
            return (
                None,
                "transparent Spec does not resolve to PaperInterface.lean: "
                + spec_qualified,
            )
        if spec_qualified in selected_rows:
            return None, "transparent Spec is selected by multiple semantic receipts: " + spec_qualified
        selected_rows[spec_qualified] = CurrentNamedTheorySemanticReviewRow(
            source_path=spec_row.source_path,
            source_sha256=spec_row.source_sha256,
            elaborated_signature_sha256=spec_row.elaborated_signature_sha256,
            individual_direct_source_route=individual_direct_source_route,
        )
        selected_surface_by_direct[qualified] = spec_qualified

    scope_targets, scope_error = formalization_scope_target_declarations_for_receipt(
        status_payload
    )
    if scope_error:
        return None, scope_error
    for target in scope_targets or set():
        if target not in semantic_by_qualified or target not in selected_surface_by_direct:
            return (
                None,
                "governing formalization-scope target is absent from the exact "
                "PaperInterface semantic receipt surface: " + target,
            )
    if not selected_rows:
        return (
            None,
            "normal named-theory receipt selected no PaperInterface semantic-model "
            "declarations",
        )
    return CurrentNamedTheorySemanticReviewSurface(selected_rows), ""


def declaration_is_on_current_named_theory_semantic_review_surface(
    declaration: LeanDeclaration,
    surface: CurrentNamedTheorySemanticReviewSurface | None,
) -> bool:
    """Return whether a declared PaperInterface row has an exact selected route.

    ``None`` means no safe normal-mode projection is available, so callers
    retain their full audit surface.  The source-byte check is repeated at the
    point of use; an intervening edit cannot convert a previously selected
    declaration into an exemption.
    """

    if surface is None:
        return True
    qualified = qualified_declaration_identity(declaration)
    row = surface.rows.get(qualified)
    if row is None:
        return False
    try:
        return (
            declaration.path.resolve() == row.source_path
            and hashlib.sha256(declaration.path.read_bytes()).hexdigest()
            == row.source_sha256
        )
    except OSError:
        return False


def declaration_has_current_individual_direct_source_route(
    declaration: LeanDeclaration,
    surface: CurrentNamedTheorySemanticReviewSurface | None,
) -> bool:
    """Return whether one current receipt directly ties this row to one source result."""

    if surface is None:
        return False
    qualified = qualified_declaration_identity(declaration)
    row = surface.rows.get(qualified)
    if row is None or not row.individual_direct_source_route:
        return False
    try:
        return (
            declaration.path.resolve() == row.source_path
            and hashlib.sha256(declaration.path.read_bytes()).hexdigest()
            == row.source_sha256
        )
    except OSError:
        return False


def raw_premise_type_head(premise: str) -> str:
    """Return a premise's exact written type head without dequalification.

    ``premise_type_text`` intentionally dequalifies types for ordinary
    assumption-ledger comparisons.  That would be unsafe for generated
    record-model bindings: their exact resolved root or exact generated alias,
    rather than a same-suffix type in another namespace, must be present in
    the reviewed binder.
    """

    normalized = normalize_premise_text(premise)
    if " : " not in normalized:
        return ""
    raw_type = normalized.split(" : ", 1)[1].lstrip()
    raw_type = raw_type.lstrip("([{⦃@")
    head = re.split(r"[\s(\[{⦃]", raw_type, maxsplit=1)[0].strip()
    return head


def raw_qualified_premise_type_head(premise: str) -> str:
    """Return an anonymous premise's fully qualified generated type head."""

    head = raw_premise_type_head(premise)
    return head if is_fully_qualified_lean_identity(head) else ""


def premise_matches_current_model_record_binding(
    premise: str,
    declaration: LeanDeclaration,
    record_bindings: dict[
        str,
        tuple[
            tuple[frozenset[str], str]
            | tuple[frozenset[str], str, frozenset[str]],
            ...,
        ],
    ],
) -> bool:
    """Match a premise only against a generated, exact record binding.

    Both the corrected-scope and ordinary v10 source-record lanes use this
    matcher.  It intentionally consumes a full declaration identity plus the
    generator-resolved record root and binder collection; neither a record tail
    nor a binder/function spelling can create a match by itself.
    """

    qualified = qualified_declaration_identity(declaration)
    bindings = record_bindings.get(qualified, ())
    if not bindings or " : " not in premise:
        return False
    raw_names = premise.split(" : ", 1)[0].strip()
    if raw_names == "anonymous":
        raw_head = raw_qualified_premise_type_head(premise)
        return bool(raw_head) and any(
            binding[1] == raw_head for binding in bindings
        )
    names = set(_binder_names(raw_names))
    if not names:
        return False
    written_type_head = raw_premise_type_head(premise)
    for binding in bindings:
        allowed_names, root = binding[:2]
        if not names.issubset(allowed_names):
            continue
        # The older corrected-scope contract supplied only a root/binder pair,
        # so preserve that lane's pre-existing matching behavior.  The v10
        # source-record projection adds a generator-resolved alias collection
        # and must match the written type root as well as its binder set.
        if len(binding) == 2:
            return True
        aliases = binding[2]
        if written_type_head == root or written_type_head in aliases:
            return True
    return False


def formalized_note_rows_from_payload(payload: dict[str, object]) -> set[str]:
    raw = payload.get("formalized_note_rows")
    if raw is None:
        raw = payload.get("formalized_note_boundary_rows")
    if not isinstance(raw, list):
        return set()
    return {str(item).strip() for item in raw if str(item).strip()}


def repo_display_path(path: Path) -> str:
    """Return a stable repository-relative path string for messages."""

    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        if not path.is_absolute():
            return str(path)
        return str(path)


def current_saved_source_record_audit(
    paper_id: str,
    *,
    payload: dict[str, object] | None = None,
) -> dict[str, object] | None:
    """Load a current canonical v10 raw audit without repeating its Lean scan.

    This is not a generic cache flag.  The evidence-integrity identity replay
    recomputes the source-record producer/input fingerprint and verifies the
    current source-map identity; the raw receipt independently binds every
    serialized audit field.  Any producer, source, Lean-input, semantic-map,
    or raw-payload drift returns ``None`` and the caller takes the ordinary
    full-scan fallback.
    """

    folder = PAPERS / paper_id
    if payload is None:
        payload = load_json_object(folder / DEFAULT_SOURCE_RECORD_AUDIT_FILE)
    if (
        not isinstance(payload, dict)
        or str(payload.get("paper") or "").strip() != paper_id
        or str(payload.get("prompt_version") or "").strip()
        != REQUIRED_SOURCE_RECORD_PROMPT_VERSION
    ):
        return None
    # `source_record_audit_identity_error` validates the aggregate semantic
    # surface and raw serialization receipt before checking the current input
    # fingerprint. Do not canonicalize the same multi-megabyte payload twice.
    identity_error = source_record_audit_identity_error(
        payload,
        expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
            folder
        ),
        folder=folder,
    )
    if identity_error:
        return None
    return payload


def source_record_semantic_contract_revalidation_for_payload(
    folder: Path,
    payload: Mapping[str, object],
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> tuple[object | None, str]:
    """Return only an exact-context or byte-pinned structural replay.

    A closeout transaction may consume the projection minted by its immutable
    evidence context only when the raw payload is that exact object.  Every
    standalone caller replays the fixed artifact against canonical raw/map
    bytes.  Value equality is deliberately insufficient: it could splice a
    copied payload into a different transaction.
    """

    evidence_context = (
        run_context.evidence_context if run_context is not None else None
    )
    if (
        exact_evidence_run_context(evidence_context)
        and payload is _legacy_source_record_audit_payload(evidence_context)
    ):
        legacy_state = _legacy_source_record_state(evidence_context)
        return (
            getattr(legacy_state, "semantic_contract_revalidation", None),
            str(
                getattr(
                    legacy_state,
                    "semantic_contract_revalidation_error",
                    "",
                )
                or ""
            ),
        )
    projection, error = source_record_semantic_contract_revalidation_context(
        folder, payload
    )
    # A standalone full scan may return a newly generated, unsaved payload.
    # Its optional replay artifact is byte-pinned to the canonical receipt and
    # therefore cannot grant it credit.  Keep the raw errors in force without
    # treating the inapplicable optional artifact as a failure of the fresh
    # scan. Builder-issued transactions report any artifact error directly.
    return (projection, error) if not error else (None, "")


def run_source_record_audit_helper(paper_id: str) -> tuple[dict[str, object] | None, str]:
    """Reuse a current canonical raw audit or run the full source-record scan."""

    cached = current_saved_source_record_audit(paper_id)
    if cached is not None:
        return cached, ""

    if not SOURCE_RECORD_AUDIT_HELPER.exists():
        return None, f"missing source-record audit helper `{SOURCE_RECORD_AUDIT_HELPER.relative_to(ROOT)}`"
    with tempfile.NamedTemporaryFile("w", suffix=".json", encoding="utf-8", delete=False) as handle:
        out_path = Path(handle.name)
    try:
        proc = subprocess.run(
            [
                "python3",
                str(SOURCE_RECORD_AUDIT_HELPER),
                "--paper",
                paper_id,
                "--out",
                str(out_path),
                "--max-lean-output-chars",
                "30000",
            ],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        payload = load_json_object(out_path)
        if proc.returncode != 0:
            excerpt = "\n".join(proc.stdout.splitlines()[-30:]) if proc.stdout else ""
            if payload is not None:
                recursion_failures = payload.get("recursion_failures")
                if isinstance(recursion_failures, list) and recursion_failures:
                    excerpt = "; ".join(
                        str(item.get("message") or item)
                        for item in recursion_failures[:5]
                        if isinstance(item, dict)
                    )
                lean_check = payload.get("lean_check")
                if not excerpt and isinstance(lean_check, dict):
                    output = str(lean_check.get("output") or "")
                    if output:
                        excerpt = "\n".join(output.splitlines()[-30:])
            return payload, f"source-record audit helper failed with exit code {proc.returncode}: {excerpt}"
        if payload is None:
            return None, "source-record audit helper did not write a JSON object"
        return payload, ""
    finally:
        try:
            out_path.unlink()
        except FileNotFoundError:
            pass


def _authenticated_overlay_union_module() -> Any:
    """Load the shared current-overlay authority on demand."""

    from scripts import source_record_authenticated_overlay_union as overlay_union

    return overlay_union


def _copy_loaded_source_record_overlay_item(
    value: Mapping[str, Any], updates: Mapping[str, Any] | None = None
) -> dict[str, Any]:
    """Preserve a private overlay-loader token during in-memory normalization."""

    return _authenticated_overlay_union_module().copy_loader_authenticated_or_plain_current_item(
        value, updates
    )


def source_record_judgment_items(
    path: Path,
    paper_id: str,
    *,
    current_raw_audit: dict[str, object] | None = None,
    paper_dir: Path | None = None,
) -> dict[str, dict[str, object]]:
    """Load ordinary judgments plus authenticated narrow-reuse overlays.

    Overlays are loaded only when the caller supplies the current generated raw
    audit and paper directory.  That keeps this parser from granting special
    freshness through a serialized marker while preserving ordinary behavior.
    """

    def normalized_items(
        payload: dict[str, object], *, authenticated_overlay_lane: object | None = None
    ) -> dict[str, dict[str, object]]:
        if not payload or not schema_version_is_exact(payload.get("schema"), 1):
            return {}
        if payload.get("paper") not in {None, paper_id}:
            return {}
        items = payload.get("items")
        if not isinstance(items, dict):
            items = payload.get("field_judgments")
        if not isinstance(items, dict):
            return {}
        overlay_union = None
        if authenticated_overlay_lane is not None:
            overlay_union = _authenticated_overlay_union_module()
            if (
                not isinstance(
                    authenticated_overlay_lane,
                    overlay_union.AuthenticatedCurrentOverlayLane,
                )
                or items is not authenticated_overlay_lane.items
            ):
                return {}
        payload_prompt_version = str(payload.get("prompt_version") or "").strip()
        payload_audit_digest = str(
            payload.get("source_record_audit_sha256") or ""
        ).strip()
        payload_has_validator = bool(
            payload.get("validator")
            or payload.get("model")
            or payload.get("judge")
            or payload.get("agent")
            or payload.get("generator")
        )
        payload_has_validated_at = bool(
            payload.get("validated_at")
            or payload.get("timestamp")
            or payload.get("generated_at")
        )
        formalized_note_rows = formalized_note_rows_from_payload(payload)
        out: dict[str, dict[str, object]] = {}
        for raw_key, raw_item in items.items():
            key = str(raw_key).strip()
            if not key:
                continue
            if archived_source_record_transport_item_field(raw_item):
                continue
            loaded_overlay_item = bool(
                authenticated_overlay_lane is not None
                and overlay_union is not None
                and overlay_union.authenticated_current_overlay_item(
                    authenticated_overlay_lane, raw_item
                )
            )
            if authenticated_overlay_lane is not None and not loaded_overlay_item:
                continue
            if (
                authenticated_overlay_lane is None
                and serialized_source_record_overlay_labels(raw_item)
            ):
                continue
            row_name = key.split(".", 1)[0]
            is_formalized_note = row_name in formalized_note_rows
            if isinstance(raw_item, dict):
                # A loader-authenticated item keeps its private token through
                # this in-memory normalization. A serialized/copied overlay
                # item has provenance but no token and was rejected above.
                item = _copy_loaded_source_record_overlay_item(raw_item)
                classification = str(
                    item.get("classification")
                    or item.get("judgment")
                    or item.get("verdict")
                    or item.get("status")
                    or ""
                ).strip()
                item_prompt_version = str(
                    item.get("prompt_version") or payload_prompt_version
                ).strip()
                item_audit_digest = str(
                    item.get("source_record_audit_sha256")
                    or payload_audit_digest
                ).strip()
                out[key] = _copy_loaded_source_record_overlay_item(
                    item,
                    {
                        "classification": classification,
                        "prompt_version": item_prompt_version,
                        "prompt_version_stale": item_prompt_version
                        != REQUIRED_SOURCE_RECORD_PROMPT_VERSION,
                        "metadata_missing": not bool(
                            (
                                item.get("validator")
                                or item.get("model")
                                or item.get("judge")
                                or item.get("agent")
                                or item.get("generator")
                                or payload_has_validator
                            )
                            and (
                                item.get("validated_at")
                                or item.get("timestamp")
                                or item.get("generated_at")
                                or payload_has_validated_at
                            )
                        ),
                        "source_record_audit_sha256": item_audit_digest,
                        "formalized_note_boundary": bool(
                            is_formalized_note
                            or str(item.get("status_impact") or "").strip()
                            == "formalized_note"
                        ),
                    },
                )
            elif authenticated_overlay_lane is None:
                out[key] = {
                    "classification": str(raw_item).strip(),
                    "prompt_version": payload_prompt_version,
                    "prompt_version_stale": payload_prompt_version
                    != REQUIRED_SOURCE_RECORD_PROMPT_VERSION,
                    "metadata_missing": not bool(
                        payload_has_validator and payload_has_validated_at
                    ),
                    "source_record_audit_sha256": payload_audit_digest,
                    "formalized_note_boundary": is_formalized_note,
                }
        return out

    if paper_dir is not None and archived_source_record_transport_artifacts(paper_dir):
        return {}
    sidecar_payload = load_json_object(path)
    ordinary = normalized_items(sidecar_payload)
    if current_raw_audit is None or paper_dir is None:
        return ordinary
    present_overlay_labels = source_record_overlay_labels_with_artifacts(
        paper_dir, lane_labels=("differential",)
    )
    overlay_current: dict[str, dict[str, dict[str, object]]] = {}
    if present_overlay_labels:
        overlay_union = _authenticated_overlay_union_module()
        try:
            lanes = overlay_union.load_authenticated_current_overlay_lanes(
                paper_dir,
                paper_id,
                current_raw_audit,
                lane_labels=present_overlay_labels,
            )
        except overlay_union.SourceRecordAuthenticatedOverlayUnionError:
            return {}
        for lane in lanes:
            overlay_current[lane.label] = normalized_items(
                {"schema": 1, "paper": paper_id, "items": lane.items},
                authenticated_overlay_lane=lane,
            )
    # A loaded overlay has independently matched this current generated
    # obligation, including any necessary association rebind.  It remains
    # preferred over a stale ordinary response, but an ordinary response bound
    # to the exact current aggregate receipt is newer evidence and wins over
    # every overlay lane.
    current_raw_digest = str(
        current_raw_audit.get("source_record_audit_sha256") or ""
    ).strip()
    ordinary_with_current_receipt = {
        key: value
        for key, value in ordinary.items()
        if current_raw_digest
        and str(value.get("source_record_audit_sha256") or "").strip()
        == current_raw_digest
    }
    composed = {
        **ordinary,
        **overlay_current.get("differential", {}),
        **ordinary_with_current_receipt,
    }
    if canonical_source_record_match_sidecar_path(path, paper_dir):
        coverage_error = canonical_source_record_sidecar_effective_coverage_error(
            current_raw_audit,
            sidecar_payload,
            effective_items=composed,
            paper_dir=paper_dir,
            sidecar_path=path,
        )
        if coverage_error:
            # Do not let a direct repository-audit reader grant credit to an
            # unlabelled fragment. The evidence-integrity path reports the
            # detailed error; this low-level loader fails closed for every
            # standalone consumer as well.
            return {}

    # This exceptional lane has no generated source association to project.
    # Bind only responses that explicitly claim a structural formalization
    # regularity; preserving all other responses here avoids creating a second
    # direct-source normalizer in the repository audit path.
    status_payload = load_json_object(paper_dir / "status.json")
    regularity_context, _regularity_context_error = (
        load_configured_assumption_formalization_regularity_context(
            paper_dir,
            current_raw_audit,
            status_payload=status_payload,
        )
    )
    groups, group_errors = raw_source_record_obligation_groups(current_raw_audit)
    if group_errors:
        return composed
    projected_composed = dict(composed)
    for raw_key, response in composed.items():
        if not response_claims_configured_assumption_formalization_regularity(response):
            continue
        group = groups.get(str(raw_key).strip())
        raw_members = group.get("raw_members") if isinstance(group, Mapping) else None
        projected, projection_error = project_source_record_response_association_pins(
            raw_members,
            response,
            judgment_key=raw_key,
            configured_assumption_formalization_regularity_context=regularity_context,
        )
        if projection_error or projected is None:
            # Keep the response so the shared validator reports the precise
            # ledger/currentness failure instead of disguising it as missing.
            continue
        projected_composed[str(raw_key)] = _copy_loaded_source_record_overlay_item(
            response, projected
        )
    return projected_composed


def source_record_expected_item_digests(
    payload: dict[str, object],
) -> dict[str, str]:
    """Return unambiguous current per-item semantic digests by judgment key.

    When a key has both an ordinary boundary surface and a richer conclusion
    dependency surface with different digests, item-level reuse is ambiguous.
    Only the current aggregate source-record digest may validate that judgment.
    """

    candidate_digests: dict[str, set[str]] = {}
    for item_key in SOURCE_RECORD_JUDGMENT_ITEM_SECTIONS:
        raw_items = payload.get(item_key)
        if not isinstance(raw_items, list):
            continue
        for raw_item in raw_items:
            if not isinstance(raw_item, dict):
                continue
            if not source_record_item_reuse_eligible(
                raw_item,
                expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            ):
                continue
            key = str(raw_item.get("judgment_key") or "").strip()
            item_digest = str(raw_item.get("source_record_item_sha256") or "").strip()
            if key and item_digest:
                candidate_digests.setdefault(key, set()).add(item_digest)
    return {
        key: next(iter(digests))
        for key, digests in candidate_digests.items()
        if len(digests) == 1
    }


def source_record_expected_item_digest_pins(
    payload: dict[str, object],
) -> dict[str, frozenset[tuple[str, int, str]]]:
    """Return every current generated semantic pin for each judgment key.

    One source-record judgment can cover both a visible boundary premise and
    its richer conclusion-dependency projection. A sidecar may survive an
    unrelated aggregate receipt change only by pinning that complete generated
    semantic surface. The comparison is deliberately exact over item kind,
    schema, and digest; generated judgment keys only group the already-pinned
    items and never act as a name-based proof of correspondence.
    """

    candidate_pins: dict[str, set[tuple[str, int, str]]] = {}
    for item_key in SOURCE_RECORD_JUDGMENT_ITEM_SECTIONS:
        raw_items = payload.get(item_key)
        if not isinstance(raw_items, list):
            continue
        for raw_item in raw_items:
            if not isinstance(raw_item, dict):
                continue
            if not source_record_item_reuse_eligible(
                raw_item,
                expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            ):
                continue
            key = str(raw_item.get("judgment_key") or "").strip()
            kind = str(raw_item.get("kind") or "").strip()
            digest = str(raw_item.get("source_record_item_sha256") or "").strip()
            if key and kind and digest:
                candidate_pins.setdefault(key, set()).add(
                    (kind, SOURCE_RECORD_ITEM_DIGEST_SCHEMA, digest)
                )
    return {
        key: frozenset(pins)
        for key, pins in candidate_pins.items()
        if pins
    }


def source_record_judgment_item_digest_pins(
    judgment: dict[str, object],
) -> frozenset[tuple[str, int, str]] | None:
    """Parse a sidecar's complete source-record pin set fail-closed."""

    raw_pins = judgment.get("source_record_item_sha256s")
    if not isinstance(raw_pins, list) or not raw_pins:
        return None
    pins: set[tuple[str, int, str]] = set()
    for raw_pin in raw_pins:
        if not isinstance(raw_pin, dict):
            return None
        kind = str(raw_pin.get("kind") or "").strip()
        schema = raw_pin.get("source_record_item_digest_schema")
        digest = str(raw_pin.get("source_record_item_sha256") or "").strip()
        if (
            not kind
            or not schema_version_is_exact(schema, SOURCE_RECORD_ITEM_DIGEST_SCHEMA)
            or not digest
        ):
            return None
        pins.add((kind, schema, digest))
    if len(pins) != len(raw_pins):
        return None
    return frozenset(pins)


def source_record_judgment_current(
    key: str,
    judgment: dict[str, object],
    *,
    digest: str,
    expected_item_digests: dict[str, str],
    expected_item_digest_pins: dict[str, frozenset[tuple[str, int, str]]] | None = None,
) -> bool:
    """Return true when a judgment matches current aggregate or semantic pins."""

    if archived_source_record_transport_item_field(judgment):
        return False
    loaded_overlay_label = (
        _authenticated_overlay_union_module().loader_authenticated_current_overlay_label(
            judgment
        )
    )
    loaded_overlay_item = loaded_overlay_label == "differential"
    if serialized_source_record_overlay_labels(judgment) and not loaded_overlay_item:
        return False
    if loaded_overlay_item:
        # The overlay loader already recomputed a complete semantic descriptor
        # for this exact current obligation. It is deliberately accepted here
        # without a scalar/pin or name/key remap path.
        return True
    if digest and str(judgment.get("source_record_audit_sha256") or "").strip() == digest:
        return True
    expected_item_digest = expected_item_digests.get(key, "")
    if source_record_item_judgment_current(
        aggregate_current=False,
        expected_item_digest=expected_item_digest,
        judgment_item_digest=judgment.get("source_record_item_sha256"),
        judgment_item_digest_schema=judgment.get(
            "source_record_item_digest_schema"
        ),
    ):
        return True
    expected_pins = (expected_item_digest_pins or {}).get(key)
    judgment_pins = source_record_judgment_item_digest_pins(judgment)
    if not expected_pins or judgment_pins != expected_pins:
        return False
    scalar_digest = str(judgment.get("source_record_item_sha256") or "").strip()
    if not scalar_digest:
        return True
    scalar_schema = judgment.get("source_record_item_digest_schema")
    return bool(
        schema_version_is_exact(scalar_schema, SOURCE_RECORD_ITEM_DIGEST_SCHEMA)
        and any(
            schema == scalar_schema and digest_value == scalar_digest
            for _kind, schema, digest_value in judgment_pins
        )
    )


def current_approved_source_convention_antecedent(
    item: Mapping[str, object],
    judgment: Mapping[str, object],
    *,
    digest: str,
    expected_item_digests: dict[str, str],
    expected_item_digest_pins: dict[str, frozenset[tuple[str, int, str]]],
    statement_map: Mapping[str, object] | None,
    source_proof_fidelity: Mapping[str, object] | None,
    status: object | None,
    administrative_projection_rebind: Any | None = None,
) -> bool:
    """Accept one current, non-result source-model convention premise.

    An ``approved_source_convention`` may justify an explicit paper-facing
    model premise, but it must not turn a result package, a conclusion field,
    or a constructor-derived value into a theorem antecedent.  The decision is
    based on the generated item's current pins and source association, never
    on the binder, declaration, or helper name.
    """

    key = str(item.get("judgment_key") or "").strip()
    if not key or not isinstance(judgment, Mapping):
        return False
    if str(item.get("kind") or "").strip() not in {
        "aliased_conclusion_bridge_input",
        "bool_certificate_input",
        "direct_conclusion_input",
        "selector_certificate_input",
        "unexpanded_local_reducible_type_input",
    }:
        return False
    if item.get("conclusion_fields") or str(item.get("result_relation") or "").strip():
        return False
    if any(
        item.get(field)
        for field in (
            "valid_constructors",
            "conditional_constructors",
            "rejected_constructors",
        )
    ):
        return False
    if str(judgment.get("classification") or "").strip() != (
        "approved_source_convention"
    ):
        return False
    if judgment.get("prompt_version_stale") or judgment.get("metadata_missing"):
        return False
    if not source_record_judgment_current(
        key,
        dict(judgment),
        digest=digest,
        expected_item_digests=expected_item_digests,
        expected_item_digest_pins=expected_item_digest_pins,
    ):
        return False
    location = str(
        judgment.get("source_location") or judgment.get("source_evidence") or ""
    ).strip()
    if not SOURCE_RECORD_EXACT_LOCATOR_RE.search(location):
        return False
    if not isinstance(statement_map, Mapping) or not isinstance(
        source_proof_fidelity, Mapping
    ):
        return False
    return not approved_source_convention_antecedent_errors(
        item,
        judgment,
        statement_map=statement_map,
        source_proof_fidelity=source_proof_fidelity,
        status=status,
        administrative_projection_rebind=administrative_projection_rebind,
    )


def source_record_optional_conclusion_dependency_traceability_keys(
    payload: dict[str, object],
    judgments: Mapping[str, dict[str, object]],
    *,
    digest: str,
    expected_item_digests: dict[str, str],
    expected_item_digest_pins: dict[str, frozenset[tuple[str, int, str]]],
) -> set[str]:
    """Return current aggregate-pinned record containers retained for traceability.

    A generated ``record_conclusion_input`` can be useful evidence even when
    it is not itself a required source-credit decision: the direct record
    judgment documents that its conclusion-bearing fields are separately
    audited.  Do not treat that narrow container receipt as a stale extra, but
    only after checking the complete schema-5 pins generated for the current
    raw item.  This never promotes an optional record to a required judgment
    and does not use the row, binder, or declaration spelling to establish
    correspondence.
    """

    optional: set[str] = set()
    raw_dependencies = payload.get("conclusion_dependency_items")
    if not isinstance(raw_dependencies, list):
        return optional
    for raw_item in raw_dependencies:
        if not isinstance(raw_item, dict):
            continue
        if str(raw_item.get("kind") or "").strip() != "record_conclusion_input":
            continue
        if not source_record_item_reuse_eligible(
            raw_item,
            expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        ):
            continue
        key = str(raw_item.get("judgment_key") or "").strip()
        judgment = judgments.get(key)
        if not key or not isinstance(judgment, dict):
            continue
        # Only container receipts belong in this optional traceability lane.
        # A source-credit classification must stay on the required surface.
        if source_record_classification(judgment) != "container_recursively_audited":
            continue
        expected_pins = expected_item_digest_pins.get(key)
        judgment_pins = source_record_judgment_item_digest_pins(judgment)
        if not expected_pins or judgment_pins != expected_pins:
            continue
        if not source_record_judgment_current(
            key,
            judgment,
            digest=digest,
            expected_item_digests=expected_item_digests,
            expected_item_digest_pins=expected_item_digest_pins,
        ):
            continue
        optional.add(key)
    return optional


def source_theorem_coverage_component_premise_findings(
    paper_id: str,
    folder: Path,
    status: object,
    source_record_payload: dict[str, object],
) -> list[Finding]:
    """Reject source-theorem coverage through a caller-supplied result component.

    Source-map routing necessarily identifies a Lean row by declaration name,
    but the rejection criterion is semantic: the source-record helper compares
    the fully expanded binder proposition with the theorem result and records
    whether it is a logical component.  Thus renaming a certificate, a
    feasibility predicate, a cost bound, or a runtime bound cannot evade this
    guard.  A conditional theorem may still exist as a helper; it simply cannot
    receive direct coverage credit for the source theorem that its premise is
    helping to assert.
    """

    statement_map = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    payload = load_json_object(statement_map)
    items = payload.get("items") if isinstance(payload, dict) else None
    if not isinstance(items, dict):
        return []

    source_keys_by_row: dict[str, set[str]] = {}
    for source_key, raw_item in items.items():
        if not isinstance(raw_item, dict):
            continue
        source_kind = str(raw_item.get("source_kind") or "").strip().lower()
        source_status = str(raw_item.get("source_status") or "").strip().lower()
        if (
            source_kind not in THEOREM_LIKE_SOURCE_INVENTORY_KINDS
            or source_status == QUARANTINED_SOURCE_DEFECT_STATUS
        ):
            continue
        names = source_coverage_declaration_names(raw_item)
        if not names:
            continue
        for name in names:
            for variant in {name, name.rsplit(".", 1)[-1]}:
                source_keys_by_row.setdefault(variant, set()).add(str(source_key))

    if not source_keys_by_row:
        return []

    routed_components: list[tuple[str, str, str, str]] = []
    raw_canonical_items = source_record_payload.get("theorem_facing_input_items")
    raw_boundary_items = (
        raw_canonical_items
        if isinstance(raw_canonical_items, list)
        else source_record_payload.get("boundary_input_items") or []
    )
    if not isinstance(raw_boundary_items, list):
        return []
    for raw_item in raw_boundary_items:
        if not isinstance(raw_item, dict):
            continue
        if str(raw_item.get("result_relation") or "").strip() not in {
            "component_of_target",
            "equivalent",
            "provides_target",
        }:
            continue
        row = str(raw_item.get("row") or "").strip()
        source_keys = source_keys_by_row.get(row) or source_keys_by_row.get(
            row.rsplit(".", 1)[-1]
        )
        if not source_keys:
            continue
        raw_input = raw_item.get("input")
        if not isinstance(raw_input, dict):
            raw_input = {}
        binder = str(raw_input.get("names") or raw_item.get("binder") or "?").strip()
        premise_type = str(raw_input.get("type") or raw_item.get("binder_type") or "?").strip()
        routed_components.append(
            (", ".join(sorted(source_keys)), row, binder, premise_type)
        )

    if not routed_components:
        return []
    examples = "; ".join(
        f"{source_key} -> {row} binder `{binder}` : {premise_type}"
        for source_key, row, binder, premise_type in routed_components[:4]
    )
    return [
        Finding(
            completed_status_finding_severity(status),
            statement_map,
            f"`{paper_id}` theorem-like source item(s) claim direct coverage through "
            "a reviewed row that receives a proposition equivalent to, providing, "
            "or a logical component of its advertised result as a caller-supplied premise: "
            + examples
            + ("; ..." if len(routed_components) > 4 else "")
            + ". This is conditional proof debt, not source-theorem coverage. Route "
            "the source item to a row that derives the feasibility/cost/runtime/"
            "optimality component from paper primitives, or mark the source claim "
            "quarantined/out of scope.",
        )
    ]


def source_theorem_coverage_type_certificate_result_findings(
    paper_id: str,
    folder: Path,
    status: object,
    source_record_payload: dict[str, object],
) -> list[Finding]:
    """Reject direct source credit through hidden Type-certificate wrappers.

    `Nonempty C`, `∃ c : C, ...`, and local proposition wrappers can hide
    actual mathematical obligations behind a Type-valued package witness. The
    source-record helper identifies this from the result wrapper and
    recursively expanded field types, not from names such as ``Certificate``.
    A source map may retain the package as support, but direct theorem coverage
    must point to a paper-facing Prop endpoint exposing the relevant field
    conclusion.
    """

    statement_map = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    payload = load_json_object(statement_map)
    source_items = payload.get("items") if isinstance(payload, dict) else None
    if not isinstance(source_items, dict):
        return []

    # Source maps occasionally classify a mathematical conclusion as a remark
    # or counterexample.  The protocol role is source metadata, while the
    # certificate verdict comes entirely from expanded Lean result/field types.
    source_keys_by_row: dict[str, set[str]] = {}
    for source_key, raw_source_item in source_items.items():
        if not isinstance(raw_source_item, dict):
            continue
        source_kind = str(raw_source_item.get("source_kind") or "").strip().lower()
        source_status = str(raw_source_item.get("source_status") or "").strip().lower()
        protocol_role = str(raw_source_item.get("protocol_role") or "").strip().lower()
        is_result_claim = (
            source_kind in THEOREM_LIKE_SOURCE_INVENTORY_KINDS
            or raw_source_item.get("claim_bearing") is True
            or protocol_role in {"mathematical_result", "runtime_claim", "counterexample"}
        )
        if not is_result_claim or source_status == QUARANTINED_SOURCE_DEFECT_STATUS:
            continue
        names = list(source_coverage_declaration_names(raw_source_item) or [])
        # A semantic contract's evidence endpoint carries direct proof credit too.
        # Check it independently of the presentation route so metadata reshuffling
        # cannot hide a Type-valued package behind an otherwise harmless endpoint.
        semantic_contract = raw_source_item.get("semantic_contract")
        if isinstance(semantic_contract, dict):
            evidence_declaration = str(
                semantic_contract.get("evidence_declaration") or ""
            ).strip()
            if evidence_declaration:
                names.append(evidence_declaration)
        names = list(dict.fromkeys(names))
        if not names:
            continue
        for name in names:
            source_keys_by_row.setdefault(name, set()).add(str(source_key))
            source_keys_by_row.setdefault(name.rsplit(".", 1)[-1], set()).add(
                str(source_key)
            )

    if not source_keys_by_row:
        return []

    raw_certificates = source_record_payload.get(
        "type_valued_certificate_result_items"
    ) or []
    if not isinstance(raw_certificates, list):
        return []
    violations: list[tuple[str, str, str, str, list[str]]] = []
    for raw_certificate in raw_certificates:
        if not isinstance(raw_certificate, dict):
            continue
        row = str(raw_certificate.get("row") or "").strip()
        qualified = str(raw_certificate.get("qualified_declaration") or "").strip()
        source_keys = (
            source_keys_by_row.get(qualified)
            or source_keys_by_row.get(row)
            or source_keys_by_row.get(qualified.rsplit(".", 1)[-1])
        )
        if not row or not source_keys:
            continue
        field_paths = [
            str(field.get("path") or field.get("field") or "").strip()
            for field in raw_certificate.get("proposition_fields") or []
            if isinstance(field, dict)
            and str(field.get("path") or field.get("field") or "").strip()
        ]
        if not field_paths:
            continue
        violations.append(
            (
                ", ".join(sorted(source_keys)),
                qualified or row,
                str(raw_certificate.get("result_wrapper") or "Type witness"),
                str(raw_certificate.get("record") or "record"),
                field_paths,
            )
        )

    if not violations:
        return []
    examples = "; ".join(
        f"{source_key} -> {row} ({wrapper} {record}; hidden Prop field(s): "
        + ", ".join(fields[:4])
        + (")" if len(fields) <= 4 else ", ...)")
        for source_key, row, wrapper, record, fields in violations[:4]
    )
    return [
        Finding(
            completed_status_finding_severity(status),
            statement_map,
            f"`{paper_id}` source result claim(s) use a Type-valued certificate "
            "existence/nonemptiness or proposition wrapper as direct Lean proof evidence: "
            + examples
            + ("; ..." if len(violations) > 4 else "")
            + ". A package witness may be listed only as support. Expose a direct "
            "paper-facing theorem/lemma with the relevant field-level Prop conclusion "
            "and route the source claim to that endpoint; renaming the record or its "
            "fields does not change this requirement.",
        )
    ]


def source_record_required_input_judgment_keys(
    payload: dict[str, object],
    *,
    semantic_contract_revalidation: object | None = None,
) -> set[str]:
    """Return boundary-input judgments not covered by a current direct ledger.

    The source-record artifact retains every boundary input for traceability.
    Its current direct source-to-Lean ledger may discharge ordinary theorem binders
    only after the helper's current-signature, gap-free checks.  Recursive
    record fields and every remaining input still require this lane's own
    provenance judgment.
    """

    return set(
        source_record_effective_input_judgment_keys(
            payload,
            semantic_contract_revalidation=semantic_contract_revalidation,
        )
    )


def source_record_traceability_input_judgment_keys(
    payload: dict[str, object],
) -> set[str]:
    """Return current direct-ledger inputs that may remain as traceability rows.

    The recursive audit deliberately emits every visible input, including an
    ordinary input already discharged by a current source-to-Lean statement
    ledger.  Those retained rows are useful audit history, but they are not
    required provenance evidence a second time.  A conclusion dependency is
    never traceability-only: a direct statement route cannot discharge a
    caller-supplied component of the advertised conclusion.

    This operates entirely on generated key membership, not row, binder, or
    declaration spelling.  Retained traceability rows are still required to
    have a current prompt, metadata, and aggregate-or-item freshness pin when
    a sidecar includes them.
    """

    expected = {
        str(key).strip()
        for key in payload.get("expected_input_judgment_keys") or []
        if str(key).strip()
    }
    covered = {
        str(key).strip()
        for key in payload.get("statement_ledger_covered_boundary_input_keys") or []
        if str(key).strip()
    }
    conclusion_dependency_keys = {
        str(item.get("judgment_key") or "").strip()
        for item in payload.get("conclusion_dependency_items") or []
        if isinstance(item, dict) and str(item.get("judgment_key") or "").strip()
    }
    return (expected & covered) - conclusion_dependency_keys


def incomplete_alias_exposes_complete_terminal_proposition(
    expanded_surface: object,
    alias_expansion: object,
) -> bool:
    """Recognize one already-generated transparent proposition body safely.

    Older raw audits can mistake a bare proposition body for a thin theorem
    alias when that body names a declaration outside the paper-local lexical
    index.  That parser result is harmless only when the same generated item
    independently exposes the bare body as its terminal proposition, retains a
    nonempty binder surface, and records a complete dependency scan with no
    hidden local type or term heads.  This predicate consumes those structural
    receipts; it never recognizes a declaration or proposition by spelling.

    A genuine imported theorem wrapper, an opaque body, a mismatched terminal
    proposition, or an empty wrapper fails closed.  Fresh producer output no
    longer needs this compatibility path because explicit ``: Prop``
    definitions are not classified as thin aliases.
    """

    if not isinstance(expanded_surface, Mapping) or not isinstance(
        alias_expansion, Mapping
    ):
        return False
    if (
        alias_expansion.get("schema") != 1
        or alias_expansion.get("alias_present") is not True
        or alias_expansion.get("complete") is True
        or str(alias_expansion.get("effective_kind") or "").strip()
        not in {"def", "abbrev"}
    ):
        return False

    blocked_routes = alias_expansion.get("blocked_routes")
    if not isinstance(blocked_routes, list) or len(blocked_routes) != 1:
        return False
    blocked_route = blocked_routes[0]
    if not isinstance(blocked_route, Mapping):
        return False
    effective_declaration = str(
        alias_expansion.get("effective_declaration") or ""
    ).strip()
    reference = str(blocked_route.get("reference") or "").strip()
    if (
        str(blocked_route.get("kind") or "").strip()
        != "unresolved_local_target"
        or blocked_route.get("candidates") != []
        or not effective_declaration
        or str(blocked_route.get("from") or "").strip()
        != effective_declaration
        or not reference
    ):
        return False

    terminal_result = expanded_surface.get("terminal_result")
    if (
        expanded_surface.get("terminal_result_origin")
        != "transparent_spec_body"
        or not isinstance(terminal_result, Mapping)
    ):
        return False

    def bare_surface(value: object) -> str:
        text = re.sub(r"\s+", "", str(value or "").strip())
        return text[1:] if text.startswith("@") else text

    expected_terminal = bare_surface(reference)
    if not expected_terminal or any(
        bare_surface(terminal_result.get(field)) != expected_terminal
        for field in ("expanded_type", "alpha_normalized_type")
    ):
        return False

    binder_domains = expanded_surface.get("binder_domains")
    if not isinstance(binder_domains, list) or not binder_domains:
        return False
    if any(
        not isinstance(domain, Mapping)
        or not str(domain.get("expanded_type") or "").strip()
        or not str(domain.get("alpha_normalized_type") or "").strip()
        for domain in binder_domains
    ):
        return False
    if expanded_surface.get("unexpanded_local_type_heads") != []:
        return False

    dependency_surface = expanded_surface.get("terminal_term_dependency_surface")
    if not isinstance(dependency_surface, Mapping):
        return False
    return bool(
        dependency_surface.get("schema") == 1
        and dependency_surface.get("scan_complete") is True
        and dependency_surface.get("incomplete_reasons") == []
        and dependency_surface.get("unexpanded_local_term_heads") == []
    )


def semantic_model_review_findings(
    paper_id: str,
    folder: Path,
    judgment_file: Path,
    items: list[dict[str, object]],
    judgments: dict[str, dict[str, object]],
    *,
    digest: str,
    expected_item_digests: dict[str, str],
    expected_item_digest_pins: dict[str, frozenset[tuple[str, int, str]]] | None = None,
    severity: str,
    target_disposition_statement_map: dict[str, object] | None = None,
    target_disposition_source_proof_fidelity: dict[str, object] | None = None,
    target_disposition_validated_vocabulary_binding_source_item_ids: object | None = None,
    target_disposition_validated_vocabulary_direct_route_source_item_ids: object | None = None,
    target_disposition_administrative_projection_rebind: Any | None = None,
    enforce_target_disposition: bool = False,
) -> list[Finding]:
    """Validate source-vs-Lean model comparisons generated from type shapes.

    This is intentionally separate from the ordinary field classifications.
    A valid source assumption judgment for a PMF field, for example, does not
    establish that its endpoint support, joint law, state recurrence, or rate
    codomain agrees with the paper. The generated item carries an
    alpha-normalized expanded surface so local names cannot be used as the
    comparison evidence.
    """

    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, judgment_file, message))

    for item in items:
        key = str(item.get("judgment_key") or "").strip()
        row = str(item.get("row") or "unknown row").strip()
        # Retain the structural process detector for report diagnostics, but
        # never make it a completeness verdict. Actual theorem-facing fields
        # and premise routes are validated by the generic source/Lean
        # obligation gate; a real checked construction must not be rejected
        # merely because it resembles an IID or endpoint-calculus pattern.
        _diagnostic_process_basis = caller_supplied_model_construction_basis(item)
        expanded_surface = item.get("expanded_lean_surface")
        alias_expansion = (
            expanded_surface.get("review_alias_expansion")
            if isinstance(expanded_surface, dict)
            else None
        )
        if (
            isinstance(alias_expansion, dict)
            and alias_expansion.get("alias_present") is True
            and alias_expansion.get("complete") is not True
            and not incomplete_alias_exposes_complete_terminal_proposition(
                expanded_surface, alias_expansion
            )
        ):
            blocked_routes = alias_expansion.get("blocked_routes")
            blocked_kinds = sorted(
                {
                    str(route.get("kind") or "unknown").strip()
                    for route in blocked_routes
                    if isinstance(route, dict)
                    and str(route.get("kind") or "").strip()
                }
            )
            add(
                f"`{paper_id}` semantic-model audit cannot inspect the actual "
                f"theorem surface for reviewed row `{row}` because its transparent "
                "review-alias route is incomplete"
                + (f" ({', '.join(blocked_kinds)})" if blocked_kinds else "")
                + ". An empty PaperInterface wrapper cannot receive semantic source credit."
            )
            continue
        if not key:
            add(
                f"`{paper_id}` semantic-model audit emitted an item without a judgment key "
                f"for reviewed row `{row}`"
            )
            continue
        judgment = judgments.get(key)
        if not isinstance(judgment, dict):
            add(
                f"`{paper_id}` semantic-model audit is missing the current comparison "
                f"judgment for reviewed row `{row}` ({key})"
            )
            continue
        if str(judgment.get("classification") or "").strip() != SEMANTIC_MODEL_REVIEW_CLASSIFICATION:
            add(
                f"`{paper_id}` semantic-model judgment `{key}` must use classification "
                f"`{SEMANTIC_MODEL_REVIEW_CLASSIFICATION}`, not "
                f"`{str(judgment.get('classification') or 'missing').strip() or 'missing'}`"
            )
        if judgment.get("prompt_version_stale") or judgment.get("metadata_missing"):
            add(
                f"`{paper_id}` semantic-model judgment `{key}` lacks current prompt or "
                "validator/timestamp metadata"
            )
            continue
        if not source_record_judgment_current(
            key,
            judgment,
            digest=digest,
            expected_item_digests=expected_item_digests,
            expected_item_digest_pins=expected_item_digest_pins,
        ):
            add(
                f"`{paper_id}` semantic-model judgment `{key}` is not tied to the current "
                "expanded Lean surface digest"
            )
            continue
        responses = judgment.get("semantic_model_dimensions")
        if not isinstance(responses, dict):
            add(
                f"`{paper_id}` semantic-model judgment `{key}` needs a "
                "semantic_model_dimensions object"
            )
            continue
        dimensions = item.get("dimensions")
        if not isinstance(dimensions, list) or not dimensions:
            add(
                f"`{paper_id}` semantic-model audit item `{key}` has no generated "
                "semantic dimensions; an empty dimension list cannot support a "
                "source-model comparison"
            )
            continue
        for raw_dimension in dimensions:
            if not isinstance(raw_dimension, dict):
                add(
                    f"`{paper_id}` semantic-model audit item `{key}` has a malformed dimension"
                )
                continue
            dimension = str(raw_dimension.get("id") or "").strip()
            if not dimension:
                add(
                    f"`{paper_id}` semantic-model audit item `{key}` has an unnamed dimension"
                )
                continue
            response = responses.get(dimension)
            if not isinstance(response, dict):
                add(
                    f"`{paper_id}` semantic-model judgment `{key}` omits dimension "
                    f"`{dimension}`"
                )
                continue
            if enforce_target_disposition:
                for error in semantic_target_disposition_errors(
                    item,
                    response,
                    statement_map=target_disposition_statement_map,
                    source_proof_fidelity=target_disposition_source_proof_fidelity,
                    validated_vocabulary_binding_source_item_ids=(
                        target_disposition_validated_vocabulary_binding_source_item_ids
                    ),
                    validated_vocabulary_direct_route_source_item_ids=(
                        target_disposition_validated_vocabulary_direct_route_source_item_ids
                    ),
                    administrative_projection_rebind=(
                        target_disposition_administrative_projection_rebind
                    ),
                ):
                    add(
                        f"`{paper_id}` semantic-model judgment `{key}` dimension "
                        f"`{dimension}` has invalid source target disposition: {error}"
                    )
            verdict = str(response.get("verdict") or "").strip()
            if verdict not in SEMANTIC_MODEL_REVIEW_VERDICTS:
                add(
                    f"`{paper_id}` semantic-model judgment `{key}` dimension `{dimension}` "
                    "must use an approved semantic-model verdict, including a "
                    "literal/convention/corrected-target match verdict when applicable"
                )
                continue
            for field in ("source_locator", "semantic_comparison", "lean_evidence"):
                value = str(response.get(field) or "").strip()
                if not value:
                    add(
                        f"`{paper_id}` semantic-model judgment `{key}` dimension "
                        f"`{dimension}` lacks `{field}`"
                    )
            if (
                bool(raw_dimension.get("detected_from_expanded_surface"))
                and raw_dimension.get("requires_parameter_translation_when_detected")
                is True
            ):
                translation = str(response.get("parameter_translation") or "").strip()
                if not translation:
                    add(
                        f"`{paper_id}` semantic-model judgment `{key}` dimension "
                        f"`{dimension}` needs parameter_translation stating the source "
                        "cardinal parameter, expanded Lean expression, and proved bridge"
                    )
                elif NAME_ONLY_SOURCE_COVERAGE_REASON_RE.search(translation):
                    add(
                        f"`{paper_id}` semantic-model judgment `{key}` dimension "
                        f"`{dimension}` uses parameter_translation as name-only evidence; "
                        "state the source-to-Lean cardinal relation structurally"
                    )
            for error in semantic_model_subanalysis_errors(
                raw_dimension,
                response,
                name_only=lambda value: bool(
                    NAME_ONLY_SOURCE_COVERAGE_REASON_RE.search(value)
                ),
            ):
                add(
                    f"`{paper_id}` semantic-model judgment `{key}` dimension "
                    f"`{dimension}` {error}"
                )
            locator = str(response.get("source_locator") or "").strip()
            if locator and not SOURCE_RECORD_EXACT_LOCATOR_RE.search(locator):
                add(
                    f"`{paper_id}` semantic-model judgment `{key}` dimension "
                    f"`{dimension}` lacks an exact source locator"
                )
            detected = bool(raw_dimension.get("detected_from_expanded_surface"))
            if detected and verdict == "not_applicable":
                add(
                    f"`{paper_id}` semantic-model judgment `{key}` marks detected "
                    f"dimension `{dimension}` not_applicable; local names cannot override "
                    "the expanded type shape"
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
                    add(
                        f"`{paper_id}` semantic-model judgment `{key}` dimension "
                        f"`{dimension}` lacks an expanded structural detection basis; "
                        "a declaration, wrapper, or function name is not a semantic trigger"
                    )
                for field in ("semantic_comparison", "lean_evidence"):
                    value = str(response.get(field) or "").strip()
                    if NAME_ONLY_SOURCE_COVERAGE_REASON_RE.search(value):
                        add(
                            f"`{paper_id}` semantic-model judgment `{key}` dimension "
                            f"`{dimension}` uses {field} as name-only evidence; compare "
                            "the expanded source and Lean formulas instead"
                        )
            requires_checked_bridge = bool(
                raw_dimension.get("requires_checked_bridge_when_detected")
            ) or dimension in SEMANTIC_MODEL_BRIDGE_DIMENSIONS
            if detected and requires_checked_bridge:
                bridge = str(response.get("lean_bridge") or "").strip()
                if not bridge:
                    add(
                        f"`{paper_id}` semantic-model judgment `{key}` dimension "
                        f"`{dimension}` needs a checked lean_bridge from source primitives"
                    )
            if verdict in {"mismatch_or_open", "documented_partial_boundary"}:
                add(
                    f"`{paper_id}` semantic-model judgment `{key}` leaves dimension "
                    f"`{dimension}` as `{verdict}`; it cannot support a source-faithful "
                    "closeout until the bridge is proved or the paper remains partial"
                )
    return findings


def _semantic_contract_executable_terminal_source_identity(
    source_key: str,
    raw_item: Mapping[str, object],
    *,
    spec_declaration: str,
    evidence_declaration: str,
    evidence_mode: str,
    semantic_shape: str,
) -> dict[str, object] | None:
    """Return the current source identity for one direct executable terminal route.

    This is a content-pinned source contract, not a declaration-name rule.  The
    source-map key only disambiguates the current serialized source item; the
    equation/formula content, exact Spec/proof endpoints, and source hashes do
    the semantic binding.
    """

    raw_contract = raw_item.get("semantic_contract")
    if not isinstance(raw_contract, Mapping):
        return None
    contract = {
        field: str(raw_contract.get(field) or "").strip()
        for field in (
            "evidence_declaration",
            "spec_declaration",
            "evidence_mode",
            "semantic_shape",
        )
    }
    if contract != {
        "evidence_declaration": evidence_declaration,
        "spec_declaration": spec_declaration,
        "evidence_mode": evidence_mode,
        "semantic_shape": semantic_shape,
    }:
        return None
    source_kind = str(raw_item.get("source_kind") or "").strip()
    source_location = str(raw_item.get("source_location") or "").strip()
    source_map_sha = source_record_source_item_record_sha256(dict(raw_item))
    source_semantic_sha = source_record_source_item_semantic_sha256(
        dict(raw_item), ""
    )
    if (
        not source_key
        or not source_kind
        or not source_location
        or not re.fullmatch(r"[0-9a-f]{64}", source_map_sha)
        or not re.fullmatch(r"[0-9a-f]{64}", source_semantic_sha)
    ):
        return None
    return {
        "source_key": source_key,
        "source_kind": source_kind,
        "source_location": source_location,
        "source_map_item_sha256": source_map_sha,
        "source_semantic_sha256": source_semantic_sha,
        "semantic_contract": contract,
    }


def _semantic_contract_executable_terminal_source_association_matches(
    raw_identities: object,
    expected_identity: Mapping[str, object],
) -> bool:
    """Require the exact generated source identity without name-based routing."""

    if not isinstance(raw_identities, list) or not raw_identities:
        return False
    matches = 0
    for identity in raw_identities:
        if not isinstance(identity, Mapping):
            return False
        if all(
            str(identity.get(field) or "").strip()
            == str(expected_identity.get(field) or "").strip()
            for field in (
                "source_key",
                "source_kind",
                "source_location",
                "source_map_item_sha256",
                "source_semantic_sha256",
            )
        ) and identity.get("semantic_contract") == expected_identity.get(
            "semantic_contract"
        ):
            matches += 1
    return matches == 1


def _semantic_contract_executable_terminal_source_association_exactly_matches(
    raw_identities: object,
    expected_identity: Mapping[str, object],
) -> bool:
    """Require one and only one current source contract for a terminal route.

    A direct executable-terminal route is intentionally narrower than the
    named-source full-Spec lane.  It therefore cannot inherit credit from a
    larger semantic-contract group or from another source presentation that
    happens to use the same Lean declaration pair.
    """

    return (
        isinstance(raw_identities, list)
        and len(raw_identities) == 1
        and _semantic_contract_executable_terminal_source_association_matches(
            raw_identities, expected_identity
        )
    )


def _semantic_contract_executable_terminal_component_receipts(
    audit: Mapping[str, object],
    semantic_item: Mapping[str, object],
    *,
    source_key: str,
    expected_identity: Mapping[str, object],
    spec_declaration: str,
    evidence_declaration: str,
    evidence_signature_sha256: str,
    evidence_dependency_sha256: str,
    terminal_receipt_sha256: str,
) -> tuple[SemanticContractExecutableTerminalComponentReceipt, ...]:
    """Project one validated terminal policy into exact component receipts.

    This projection is intentionally structural.  It begins with a source-map
    item already validated by :func:`semantic_contract_executable_terminal_policy_errors`
    and then checks generated direct/Spec grouping, component association
    records, and occurrence identities.  It never selects a component by
    binder, helper, terminal declaration, source-kind, or function name.
    """

    semantic_key = str(semantic_item.get("judgment_key") or "").strip()
    group = semantic_item.get("semantic_contract_group")
    direct_association = semantic_item.get("semantic_contract_source_association")
    if (
        not semantic_key
        or not isinstance(group, Mapping)
        or not isinstance(direct_association, Mapping)
        or group.get("schema") != 1
        or group.get("structural_alpha_normalized_equal") is not True
        or not _semantic_contract_executable_terminal_source_association_exactly_matches(
            group.get("source_item_identities"), expected_identity
        )
        or direct_association.get("schema") != 2
        or str(direct_association.get("role") or "").strip()
        != "direct_evidence"
        or str(direct_association.get("paired_qualified_declaration") or "").strip()
        != spec_declaration
        or not _semantic_contract_executable_terminal_source_association_exactly_matches(
            direct_association.get("source_item_identities"), expected_identity
        )
    ):
        return ()

    direct_identity = direct_association.get("reviewed_declaration_identity")
    direct_signature = direct_association.get(
        "reviewed_elaborated_signature_identity"
    )
    if (
        not isinstance(direct_identity, Mapping)
        or not isinstance(direct_signature, Mapping)
        or str(direct_identity.get("qualified_declaration") or "").strip()
        != evidence_declaration
        or str(direct_signature.get("qualified_declaration") or "").strip()
        != evidence_declaration
        or str(direct_signature.get("elaborated_signature_sha256") or "")
        .strip()
        .lower()
        != evidence_signature_sha256
    ):
        return ()

    member_pairs: set[tuple[str, str]] = set()
    raw_members = group.get("member_rows")
    if not isinstance(raw_members, list) or len(raw_members) != 2:
        return ()
    for member in raw_members:
        if not isinstance(member, Mapping):
            return ()
        role = str(member.get("role") or "").strip()
        declaration = str(member.get("qualified_declaration") or "").strip()
        if role not in {"direct_evidence", "transparent_spec"} or not declaration:
            return ()
        member_pairs.add((role, declaration))
    if member_pairs != {
        ("direct_evidence", evidence_declaration),
        ("transparent_spec", spec_declaration),
    }:
        return ()

    source_semantic_sha = str(
        expected_identity.get("source_semantic_sha256") or ""
    ).strip().lower()
    source_map_sha = str(
        expected_identity.get("source_map_item_sha256") or ""
    ).strip().lower()
    if not all(
        re.fullmatch(r"[0-9a-f]{64}", value)
        for value in (
            evidence_signature_sha256,
            evidence_dependency_sha256,
            terminal_receipt_sha256,
            source_semantic_sha,
            source_map_sha,
        )
    ):
        return ()

    receipts: set[SemanticContractExecutableTerminalComponentReceipt] = set()
    for _section, raw_component in theorem_realization_components(audit):
        if not isinstance(raw_component, Mapping):
            continue
        if (
            str(raw_component.get("source_claim_component_role") or "").strip()
            != "material"
        ):
            continue
        association = raw_component.get("source_contract_association")
        if (
            not isinstance(association, Mapping)
            or association.get("schema") != 2
            or str(association.get("association_mode") or "").strip()
            != "semantic_contract_group_member"
            or str(association.get("semantic_contract_member_role") or "").strip()
            != "transparent_spec"
            or str(association.get("semantic_model_judgment_key") or "").strip()
            != semantic_key
            or not _semantic_contract_executable_terminal_source_association_exactly_matches(
                association.get("source_item_identities"), expected_identity
            )
        ):
            continue
        association_identity = association.get("reviewed_declaration_identity")
        association_signature = association.get(
            "reviewed_elaborated_signature_identity"
        )
        association_sha = str(association.get("association_sha256") or "").strip().lower()
        if (
            not isinstance(association_identity, Mapping)
            or not isinstance(association_signature, Mapping)
            or str(association_identity.get("qualified_declaration") or "").strip()
            != spec_declaration
            or str(association_signature.get("qualified_declaration") or "").strip()
            != spec_declaration
            or not re.fullmatch(r"[0-9a-f]{64}", association_sha)
            or association_sha != source_contract_association_record_digest(association)
        ):
            continue
        component_key = str(raw_component.get("judgment_key") or "").strip()
        source_judgment_key = str(
            raw_component.get("source_judgment_key")
            or raw_component.get("judgment_key")
            or ""
        ).strip()
        component_sha = source_claim_component_sha256(raw_component)
        structural_sha = str(
            raw_component.get("structural_type_sha256") or ""
        ).strip().lower()
        if (
            not component_key
            or not source_judgment_key
            or not all(
                re.fullmatch(r"[0-9a-f]{64}", value)
                for value in (component_sha, structural_sha)
            )
        ):
            continue
        receipts.add(
            SemanticContractExecutableTerminalComponentReceipt(
                component_key=component_key,
                source_judgment_key=source_judgment_key,
                component_sha256=component_sha,
                structural_type_sha256=structural_sha,
                semantic_model_judgment_key=semantic_key,
                component_source_contract_association_sha256=association_sha,
                source_item_key=source_key,
                source_item_semantic_sha256=source_semantic_sha,
                source_map_item_sha256=source_map_sha,
                spec_declaration=spec_declaration,
                evidence_declaration=evidence_declaration,
                evidence_elaborated_signature_sha256=evidence_signature_sha256,
                evidence_semantic_dependency_sha256=evidence_dependency_sha256,
                terminal_receipt_sha256=terminal_receipt_sha256,
            )
        )
    return tuple(
        sorted(
            receipts,
            key=lambda receipt: (
                receipt.component_key,
                receipt.component_sha256,
            ),
        )
    )


def _recursive_field_explicit_parent_semantic_model_item(
    audit: Mapping[str, object],
    route: Mapping[str, object],
) -> Mapping[str, object] | None:
    """Resolve the one generated semantic parent named by a field route.

    This is a structural join over generator-owned declaration, signature,
    association, source-identity, and record-binding coordinates.  It never
    discovers a parent from a field name, theorem name, source kind, or source
    locator.  A duplicate or partially matching semantic row remains
    unresolved rather than receiving an arbitrary choice.
    """

    semantic_key = str(route.get("parent_semantic_model_judgment_key") or "").strip()
    association_field = str(route.get("parent_association_field") or "").strip()
    expected_identity = route.get("parent_reviewed_declaration_identity")
    expected_signature = route.get("parent_elaborated_signature_identity")
    expected_association_sha = str(
        route.get("parent_source_association_sha256") or ""
    ).strip().lower()
    expected_source_identities = route.get("source_item_identities")
    root_record = str(route.get("root_record") or "").strip()
    root_input_type = str(route.get("root_input_type_canonical") or "").strip()
    if (
        not semantic_key
        or association_field
        not in {
            "source_statement_association",
            "semantic_contract_source_association",
            SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD,
        }
        or not isinstance(expected_identity, Mapping)
        or not isinstance(expected_signature, Mapping)
        or not isinstance(expected_source_identities, list)
        or len(expected_source_identities) != 1
        or not root_record
        or not root_input_type
        or not re.fullmatch(r"[0-9a-f]{64}", expected_association_sha)
    ):
        return None
    raw_semantic_items = audit.get("semantic_model_items")
    if not isinstance(raw_semantic_items, list):
        return None
    candidates = [
        item
        for item in raw_semantic_items
        if isinstance(item, Mapping)
        and str(item.get("judgment_key") or "").strip() == semantic_key
    ]
    if len(candidates) != 1:
        return None
    candidate = candidates[0]
    if candidate.get("reviewed_declaration_identity") != expected_identity:
        return None
    raw_signatures = candidate.get("reviewed_elaborated_signature_identities")
    if not isinstance(raw_signatures, list) or len(raw_signatures) != 1:
        return None
    signature = raw_signatures[0]
    if not isinstance(signature, Mapping) or any(
        str(signature.get(field) or "").strip().lower()
        != str(expected_signature.get(field) or "").strip().lower()
        for field in ("qualified_declaration", "elaborated_signature_sha256")
    ):
        return None
    association = candidate.get(association_field)
    association_is_claim_atom = (
        association_field == SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD
    )
    observed_association_sha = (
        semantic_association_record_digest(
            [
                str(identity.get("source_semantic_sha256") or "").strip().lower()
                for identity in expected_source_identities
                if isinstance(identity, Mapping)
            ],
            expected_signature,
        )
        if association_is_claim_atom
        else str(
            association.get("semantic_association_sha256")
            if isinstance(association, Mapping)
            else ""
        )
        .strip()
        .lower()
    )
    if (
        not isinstance(association, Mapping)
        or association.get("schema") != (1 if association_is_claim_atom else 2)
        or association.get("reviewed_declaration_identity") != expected_identity
        or association.get("reviewed_elaborated_signature_identity")
        != expected_signature
        or association.get("source_item_identities") != expected_source_identities
        or observed_association_sha != expected_association_sha
        or str(association.get("role") or "").strip()
        != str(route.get("parent_source_association_role") or "").strip()
        or str(association.get("association_origin") or "").strip()
        != str(route.get("parent_source_association_origin") or "").strip()
        or (
            association_is_claim_atom
            and (
                str(association.get("association_origin") or "").strip()
                != SOURCE_CLAIM_ATOM_ROUTE_ORIGIN
                or str(association.get("role") or "").strip()
                != SOURCE_CLAIM_ATOM_ROUTE_ROLE
            )
        )
    ):
        return None
    raw_bindings = candidate.get("record_input_bindings")
    if not isinstance(raw_bindings, list):
        return None
    matching_bindings = [
        binding
        for binding in raw_bindings
        if isinstance(binding, Mapping)
        and binding.get("record_roots") == [root_record]
        and str(binding.get("fully_qualified_expanded_type_canonical") or "").strip()
        == root_input_type
    ]
    return candidate if len(matching_bindings) == 1 else None


def _recursive_field_explicit_parent_component_receipts(
    paper_id: str,
    folder: Path,
    audit: Mapping[str, object],
    *,
    run_context: PaperCloseoutRunContext | None,
) -> tuple[RecursiveFieldExplicitParentComponentReceipt, ...]:
    """Mint strict component receipts for exact reviewed source-model fields.

    The only authority is a builder-issued closeout transaction.  In
    particular, this function reselects the raw audit, map, source ledger, and
    judgments from immutable transaction snapshots, validates the field route
    and its parent semantic review, then projects onto generated material
    occurrences.  It intentionally returns no receipt for a malformed,
    stale, ambiguous, or caller-supplied surface; the generic strict gate will
    report the missing component contract.
    """

    if (
        not isinstance(run_context, PaperCloseoutRunContext)
        or not run_context.issued_by_builder
        or run_context.paper_id != paper_id
        or run_context.folder != folder.resolve()
        or not exact_evidence_run_context(run_context.evidence_context)
    ):
        return ()
    exact_audit, audit_error = run_context.current_source_record_audit()
    if audit_error or not isinstance(exact_audit, Mapping) or audit is not exact_audit:
        return ()
    if source_record_raw_integrity_error_if_current(dict(exact_audit)):
        return ()
    if source_record_target_route_error(dict(exact_audit)):
        return ()
    (
        semantic_contract_revalidation,
        semantic_contract_revalidation_error,
    ) = source_record_semantic_contract_revalidation_for_payload(
        folder,
        exact_audit,
        run_context=run_context,
    )
    if semantic_contract_revalidation_error or source_record_effective_semantic_surface_error(
        exact_audit,
        semantic_contract_revalidation=semantic_contract_revalidation,
    ):
        return ()

    review_surface = source_record_audit_surface_view(exact_audit)
    if not isinstance(review_surface, Mapping):
        return ()
    judgment_file = source_record_judgment_file_path(folder, dict(review_surface))
    legacy_inputs = _legacy_source_record_inputs(run_context.evidence_context)
    match_snapshot = getattr(legacy_inputs, "match_snapshot", None)
    if not isinstance(getattr(match_snapshot, "path", None), Path) or (
        match_snapshot.path.resolve() != judgment_file.resolve()
    ):
        return ()
    judgments = run_context.source_record_judgments(judgment_file, exact_audit)
    if not isinstance(judgments, Mapping):
        return ()
    statement_map, source_proof_fidelity = source_record_target_disposition_context(
        folder,
        dict(review_surface),
        run_context=run_context,
    )
    if not isinstance(statement_map, Mapping) or not isinstance(
        source_proof_fidelity, Mapping
    ):
        return ()
    rebind, rebind_error = source_record_target_disposition_rebind_context(
        folder,
        dict(review_surface),
        dict(exact_audit),
        run_context=run_context,
    )
    if rebind_error:
        return ()

    audit_digest = str(exact_audit.get("source_record_audit_sha256") or "").strip()
    expected_item_digests = source_record_expected_item_digests(dict(exact_audit))
    expected_item_digest_pins = source_record_expected_item_digest_pins(
        dict(exact_audit)
    )
    strict_semantic_parent_keys = (
        current_strict_v11_full_spec_source_record_semantic_model_judgment_keys(
            paper_id,
            folder,
            exact_audit,
            run_context=run_context,
        )
    )
    parent_reviewed: dict[str, bool] = {}
    receipts: set[RecursiveFieldExplicitParentComponentReceipt] = set()
    for _section, raw_component in theorem_realization_components(exact_audit):
        if not isinstance(raw_component, Mapping):
            continue
        if (
            str(raw_component.get("source_claim_component_role") or "").strip()
            != "material"
            or str(raw_component.get("source_component_section") or "").strip()
            != "recursive_field_items"
            or str(raw_component.get("source_claim_component_kind") or "").strip()
            != "recursive_record_field"
        ):
            continue
        route = raw_component.get("recursive_field_explicit_parent_route")
        if not isinstance(route, Mapping):
            continue
        # A container route is a traversal aid, never source-credit for a
        # material occurrence.  Leaf classification is validated again below
        # by the target-disposition gate before any receipt is minted.
        if any(
            str(value or "").strip()
            for value in raw_component.get("nested_structures") or []
        ):
            continue
        source_judgment_key = str(
            raw_component.get("source_judgment_key")
            or raw_component.get("judgment_key")
            or ""
        ).strip()
        field_judgment = judgments.get(source_judgment_key)
        if not isinstance(field_judgment, Mapping):
            continue
        if not source_record_judgment_current(
            source_judgment_key,
            # A differential/selected-reuse item carries an in-memory loader
            # capability.  Do not coerce it to ``dict`` here: that would
            # discard the capability and make a semantically revalidated
            # recursive field appear stale.
            field_judgment,
            digest=audit_digest,
            expected_item_digests=expected_item_digests,
            expected_item_digest_pins=expected_item_digest_pins,
        ):
            continue
        if recursive_field_target_disposition_errors(
            raw_component,
            field_judgment,
            statement_map=statement_map,
            source_proof_fidelity=source_proof_fidelity,
            administrative_projection_rebind=rebind,
        ):
            continue
        parent = _recursive_field_explicit_parent_semantic_model_item(
            exact_audit, route
        )
        if parent is None:
            continue
        parent_key = str(parent.get("judgment_key") or "").strip()
        # The route itself carries the exact parent key. Keep this explicit
        # comparison even though the resolver selected by it, so a future
        # projection refactor cannot turn a broad declaration match into
        # parent-review credit.
        if parent_key != str(
            route.get("parent_semantic_model_judgment_key") or ""
        ).strip():
            continue
        if parent_key not in parent_reviewed:
            parent_reviewed[parent_key] = (
                parent_key in strict_semantic_parent_keys
                or not semantic_model_review_findings(
                    paper_id,
                    folder,
                    judgment_file,
                    [dict(parent)],
                    dict(judgments),
                    digest=audit_digest,
                    expected_item_digests=expected_item_digests,
                    expected_item_digest_pins=expected_item_digest_pins,
                    severity="ERROR",
                    target_disposition_statement_map=dict(statement_map),
                    target_disposition_source_proof_fidelity=dict(source_proof_fidelity),
                    target_disposition_validated_vocabulary_binding_source_item_ids=(
                        exact_audit.get(
                            "source_coverage_validated_vocabulary_binding_source_items"
                        )
                    ),
                    target_disposition_validated_vocabulary_direct_route_source_item_ids=(
                        exact_audit.get(
                            "source_coverage_validated_vocabulary_direct_route_source_items"
                        )
                    ),
                    target_disposition_administrative_projection_rebind=rebind,
                    enforce_target_disposition=True,
                )
            )
        if not parent_reviewed[parent_key]:
            continue

        identities = route.get("source_item_identities")
        parent_identity = route.get("parent_reviewed_declaration_identity")
        parent_signature = route.get("parent_elaborated_signature_identity")
        if (
            not isinstance(identities, list)
            or len(identities) != 1
            or not isinstance(identities[0], Mapping)
            or not isinstance(parent_identity, Mapping)
            or not isinstance(parent_signature, Mapping)
        ):
            continue
        source_identity = identities[0]
        component_key = str(raw_component.get("judgment_key") or "").strip()
        component_sha = source_claim_component_sha256(raw_component)
        structural_sha = str(
            raw_component.get("structural_type_sha256") or ""
        ).strip().lower()
        receipt_values = (
            component_key,
            source_judgment_key,
            component_sha,
            structural_sha,
            str(route.get("association_sha256") or "").strip().lower(),
            str(route.get("source_item") or "").strip(),
            str(source_identity.get("source_semantic_sha256") or "").strip().lower(),
            str(source_identity.get("source_map_item_sha256") or "").strip().lower(),
            str(route.get("root_record") or "").strip(),
            str(route.get("field_scope_sha256") or "").strip().lower(),
            str(route.get("convention_id") or "").strip(),
            str(route.get("convention_sha256") or "").strip().lower(),
            parent_key,
            str(parent_identity.get("qualified_declaration") or "").strip(),
            str(parent_identity.get("declaration_sha256") or "").strip().lower(),
            str(parent_signature.get("elaborated_signature_sha256") or "").strip().lower(),
            str(route.get("parent_source_association_sha256") or "").strip().lower(),
        )
        if not all(receipt_values) or not all(
            re.fullmatch(r"[0-9a-f]{64}", value)
            for value in (
                component_sha,
                structural_sha,
                receipt_values[4],
                receipt_values[6],
                receipt_values[7],
                receipt_values[9],
                receipt_values[11],
                receipt_values[14],
                receipt_values[15],
                receipt_values[16],
            )
        ):
            continue
        receipts.add(
            RecursiveFieldExplicitParentComponentReceipt(
                component_key=component_key,
                source_judgment_key=source_judgment_key,
                component_sha256=component_sha,
                structural_type_sha256=structural_sha,
                recursive_field_parent_route_sha256=receipt_values[4],
                source_item_key=receipt_values[5],
                source_item_semantic_sha256=receipt_values[6],
                source_map_item_sha256=receipt_values[7],
                root_record=receipt_values[8],
                field_scope_sha256=receipt_values[9],
                convention_id=receipt_values[10],
                convention_sha256=receipt_values[11],
                parent_semantic_model_judgment_key=parent_key,
                parent_qualified_declaration=receipt_values[13],
                parent_declaration_sha256=receipt_values[14],
                parent_elaborated_signature_sha256=receipt_values[15],
                parent_source_association_sha256=receipt_values[16],
            )
        )
    return tuple(
        sorted(
            receipts,
            key=lambda receipt: (
                receipt.source_item_key,
                receipt.parent_qualified_declaration,
                receipt.component_key,
                receipt.component_sha256,
            ),
        )
    )


def semantic_contract_executable_terminal_policy_errors(
    paper_id: str,
    folder: Path,
    *,
    source_key: str,
    transparency: Mapping[str, object],
    run_context: PaperCloseoutRunContext | None,
) -> list[str]:
    """Validate the narrow terminal bridge for recursive executable model code.

    The bridge is available only inside a builder-issued closeout transaction.
    It never accepts a caller-supplied status, source-map item, raw audit, or
    judgment file: all are reselected from the transaction's immutable
    snapshots. Lean must report a failed generic transparency receipt whose
    complete recursive occurrence set exactly matches a generated raw
    source-model receipt. The direct theorem, source contract, elaborated
    signature, transitive dependency graph, and semantic-model review must all
    agree. No source kind, declaration spelling, or terminal name is an
    approval rule.
    """

    if (
        not isinstance(run_context, PaperCloseoutRunContext)
        or not run_context.issued_by_builder
        or run_context.paper_id != paper_id
        or run_context.folder != folder.resolve()
        or not exact_evidence_run_context(run_context.evidence_context)
    ):
        return [
            "executable-recursion terminal bridge requires one exact builder-issued closeout context"
        ]
    evidence_context = run_context.evidence_context
    assert evidence_context is not None
    exact_status = run_context.exact_json_payload(folder / "status.json")
    exact_map = run_context.exact_json_payload(
        folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    )
    if not isinstance(exact_status, Mapping) or not isinstance(exact_map, Mapping):
        return [
            "executable-recursion terminal bridge lacks an exact status or source-map snapshot"
        ]
    if (
        dict(exact_status) != dict(getattr(evidence_context, "status_payload", {}))
        or dict(exact_map) != dict(getattr(evidence_context, "statement_map", {}) or {})
    ):
        return [
            "executable-recursion terminal bridge snapshot does not match its evidence transaction"
        ]
    raw_source_items = exact_map.get("items")
    raw_item = (
        raw_source_items.get(source_key)
        if isinstance(raw_source_items, Mapping)
        else None
    )
    if not isinstance(raw_item, Mapping):
        return ["exact source-map snapshot has no contract item for this terminal route"]
    raw_contract = raw_item.get("semantic_contract")
    if not isinstance(raw_contract, Mapping):
        return ["exact source-map item has no semantic contract for this terminal route"]
    spec_declaration = str(raw_contract.get("spec_declaration") or "").strip()
    evidence_declaration = str(
        raw_contract.get("evidence_declaration") or ""
    ).strip()
    evidence_mode = str(raw_contract.get("evidence_mode") or "").strip()
    semantic_shape = str(raw_contract.get("semantic_shape") or "").strip()
    if not all(
        (spec_declaration, evidence_declaration, evidence_mode, semantic_shape)
    ):
        return ["exact source-map terminal contract is incomplete"]

    expected_identity = _semantic_contract_executable_terminal_source_identity(
        source_key,
        raw_item,
        spec_declaration=spec_declaration,
        evidence_declaration=evidence_declaration,
        evidence_mode=evidence_mode,
        semantic_shape=semantic_shape,
    )
    if expected_identity is None:
        return ["source contract cannot be bound to one exact source identity"]

    review_surface = exact_status.get("review_surface")
    if not isinstance(review_surface, Mapping):
        return ["exact status snapshot has no source-model review surface"]
    source_path = review_surface_source_file_path(folder, dict(review_surface))
    if run_context.exact_lean_source_text(source_path) is None:
        return [
            "exact closeout transaction does not own the configured review-source bytes"
        ]
    import_module = f"{folder.name}.{source_path.stem}"
    build_input_provider = run_context.build_input_provider
    try:
        from scripts.lean_signature_manifest import (
            paper_local_module_names,
            run_lean_semantic_contract_transparency_checks,
            run_lean_signature_manifests,
            semantic_dependency_manifest,
            signature_manifest_digest,
        )
        paper_modules = paper_local_module_names(
            ROOT, folder, provider=build_input_provider
        )
        exact_transparency = run_lean_semantic_contract_transparency_checks(
            ROOT,
            import_module,
            [spec_declaration],
            paper_modules,
            build_input_provider=build_input_provider,
        ).get(spec_declaration)
    except Exception:  # noqa: BLE001 - no live fallback is allowed here.
        return [
            "could not obtain the exact transaction-owned Lean transparency receipt"
        ]
    if not isinstance(exact_transparency, Mapping):
        return ["exact Lean transparency receipt is unavailable"]
    if not isinstance(transparency, Mapping) or dict(transparency) != dict(
        exact_transparency
    ):
        return [
            "caller-supplied executable-recursion transparency differs from the exact transaction receipt"
        ]

    terminals = canonical_semantic_contract_executable_terminals(
        exact_transparency.get("recursive_executable_terminals")
    )
    terminal_digest = semantic_contract_executable_terminal_receipt_sha256(terminals)
    failure_declaration = str(
        exact_transparency.get("failure_declaration") or ""
    ).strip()
    if (
        exact_transparency.get("passes") is not False
        or str(exact_transparency.get("failure_tag") or "").strip()
        != "recursive_executable_terminal"
        or terminals is None
        or not terminals
        or not terminal_digest
        or failure_declaration
        not in {str(terminal["declaration"]) for terminal in terminals}
    ):
        return [
            "exact Lean transparency did not emit a well-formed executable-recursion occurrence set"
        ]

    audit, audit_error = run_context.current_source_record_audit()
    if audit_error or not isinstance(audit, dict):
        return [
            "exact closeout source-record audit is unavailable"
            + (f": {audit_error}" if audit_error else "")
        ]
    legacy_state = getattr(evidence_context, "legacy_source_record_state", None)
    legacy_inputs = getattr(legacy_state, "inputs", None)
    legacy_audit_snapshot = getattr(legacy_inputs, "audit_snapshot", None)
    if audit is not getattr(legacy_audit_snapshot, "payload", None):
        return [
            "executable-recursion terminal bridge received a non-snapshot source-record audit"
        ]
    if str(audit.get("paper") or "").strip() != paper_id:
        return ["exact closeout source-record audit belongs to another paper"]
    expected_map_sha = str(
        getattr(evidence_context, "paper_statement_map_sha256", "") or ""
    ).strip().lower()
    if (
        not re.fullmatch(r"[0-9a-f]{64}", expected_map_sha)
        or str(audit.get("paper_statement_map_sha256") or "").strip().lower()
        != expected_map_sha
        or str(getattr(legacy_state, "source_record_identity_error", "") or "").strip()
    ):
        return [
            "exact source-record snapshot has no current map/input-fingerprint authorization"
        ]
    (
        semantic_contract_revalidation,
        semantic_contract_revalidation_error,
    ) = source_record_semantic_contract_revalidation_for_payload(
        folder,
        audit,
        run_context=run_context,
    )
    if semantic_contract_revalidation_error:
        return [
            "exact source-record semantic-contract revalidation is invalid: "
            + semantic_contract_revalidation_error
        ]
    surface_error = source_record_effective_semantic_surface_error(
        audit,
        semantic_contract_revalidation=semantic_contract_revalidation,
    )
    if surface_error:
        return [
            "generated source-record semantic surface is not current: " + surface_error
        ]

    semantic_items = [
        item
        for item in audit.get("semantic_model_items") or []
        if isinstance(item, Mapping)
        and str(item.get("qualified_declaration") or "").strip()
        == evidence_declaration
    ]
    if len(semantic_items) != 1:
        return [
            "current source-record audit does not contain exactly one direct semantic-model row"
        ]
    semantic_item = semantic_items[0]
    exact_identity = semantic_model_item_exact_receipt_identity(
        semantic_item, qualified_declaration=evidence_declaration
    )
    if exact_identity is None:
        return ["direct source-model row lacks a valid exact theorem/Spec receipt"]

    raw_signatures = semantic_item.get("reviewed_elaborated_signature_identities")
    if not isinstance(raw_signatures, list) or len(raw_signatures) != 1:
        return ["direct source-model row lacks one elaborated signature/dependency identity"]
    signature_identity = raw_signatures[0]
    if not isinstance(signature_identity, Mapping):
        return ["direct source-model signature/dependency identity is malformed"]
    recorded_signature = str(
        signature_identity.get("elaborated_signature_sha256") or ""
    ).strip().lower()
    recorded_dependency = str(
        signature_identity.get("semantic_dependency_sha256") or ""
    ).strip().lower()
    if (
        str(signature_identity.get("qualified_declaration") or "").strip()
        != evidence_declaration
        or recorded_signature != exact_identity[1]
        or not re.fullmatch(r"[0-9a-f]{64}", recorded_dependency)
    ):
        return ["direct source-model row lacks a current signature/dependency fingerprint"]

    group = semantic_item.get("semantic_contract_group")
    association = semantic_item.get("semantic_contract_source_association")
    if not isinstance(group, Mapping) or not isinstance(association, Mapping):
        return ["direct source-model row lacks the generated direct/Spec source association"]
    if not (
        _semantic_contract_executable_terminal_source_association_matches(
            group.get("source_item_identities"), expected_identity
        )
        and _semantic_contract_executable_terminal_source_association_matches(
            association.get("source_item_identities"), expected_identity
        )
    ):
        return ["direct source-model row is not associated with this exact current source contract"]

    raw_receipts = semantic_item.get(
        SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_RECEIPT_FIELD
    )
    if not isinstance(raw_receipts, list):
        return [
            "direct source-model row has no generated executable-recursion terminal receipt"
        ]
    matching_receipts: list[Mapping[str, object]] = []
    for receipt in raw_receipts:
        if not isinstance(receipt, Mapping) or set(receipt) != {
            "schema",
            "source_item_identity",
            "spec_declaration",
            "evidence_declaration",
            "reviewed_elaborated_signature_identity",
            "transparency",
        }:
            continue
        if (
            receipt.get("schema")
            != SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_RECEIPT_SCHEMA
            or str(receipt.get("spec_declaration") or "").strip()
            != spec_declaration
            or str(receipt.get("evidence_declaration") or "").strip()
            != evidence_declaration
            or not _semantic_contract_executable_terminal_source_association_matches(
                [receipt.get("source_item_identity")], expected_identity
            )
        ):
            continue
        matching_receipts.append(receipt)
    if len(matching_receipts) != 1:
        return [
            "direct source-model row lacks one exact generated executable-recursion receipt for this source contract"
        ]
    receipt = matching_receipts[0]
    receipt_signature = receipt.get("reviewed_elaborated_signature_identity")
    receipt_transparency = receipt.get("transparency")
    receipt_terminals = (
        canonical_semantic_contract_executable_terminals(
            receipt_transparency.get("terminals")
        )
        if isinstance(receipt_transparency, Mapping)
        else None
    )
    receipt_terminal_digest = semantic_contract_executable_terminal_receipt_sha256(
        receipt_terminals
    )
    if (
        not isinstance(receipt_signature, Mapping)
        or not isinstance(receipt_transparency, Mapping)
        or receipt_transparency.get("schema")
        != SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_SCHEMA
        or receipt_transparency.get("passes") is not False
        or str(receipt_transparency.get("failure_tag") or "").strip()
        != "recursive_executable_terminal"
        or str(receipt_transparency.get("failure_declaration") or "").strip()
        != failure_declaration
        or receipt_terminals != terminals
        or not receipt_terminal_digest
        or str(receipt_transparency.get("terminal_receipt_sha256") or "").strip().lower()
        != receipt_terminal_digest
    ):
        return [
            "generated executable-recursion receipt does not bind the exact current terminal occurrence set"
        ]

    try:
        manifests = run_lean_signature_manifests(
            ROOT,
            import_module,
            [evidence_declaration],
            semantic_dependency_modules=paper_modules,
            build_input_provider=build_input_provider,
        )
        manifest = manifests.get(evidence_declaration)
        dependency_manifest = (
            semantic_dependency_manifest(manifest)
            if isinstance(manifest, Mapping)
            else None
        )
        current_dependency = (
            str(dependency_manifest.get("semantic_dependency_sha256") or "")
            .strip()
            .lower()
            if isinstance(dependency_manifest, Mapping)
            else ""
        )
        if (
            not isinstance(manifest, Mapping)
            or signature_manifest_digest(manifest) != recorded_signature
            or current_dependency != recorded_dependency
            or str(receipt_signature.get("qualified_declaration") or "").strip()
            != evidence_declaration
            or str(
                receipt_signature.get("elaborated_signature_sha256") or ""
            ).strip().lower()
            != recorded_signature
            or str(receipt_signature.get("semantic_dependency_sha256") or "").strip().lower()
            != recorded_dependency
        ):
            return [
                "direct source-model signature or transitive dependency fingerprint is stale"
            ]
    except Exception:  # noqa: BLE001 - a missing current Lean receipt fails closed.
        return ["could not revalidate the direct source-model dependency fingerprint"]

    judgment_file = source_record_judgment_file_path(folder, dict(review_surface))
    legacy_inputs = _legacy_source_record_inputs(evidence_context)
    match_snapshot = getattr(legacy_inputs, "match_snapshot", None)
    if not isinstance(getattr(match_snapshot, "path", None), Path) or (
        match_snapshot.path.resolve() != judgment_file.resolve()
    ):
        return [
            "exact closeout transaction does not own the configured source-model judgment snapshot"
        ]
    judgments = run_context.source_record_judgments(judgment_file, audit)
    if not isinstance(judgments, Mapping):
        return ["exact source-model judgment snapshot is malformed"]
    audit_digest = str(audit.get("source_record_audit_sha256") or "").strip()
    (
        target_disposition_statement_map,
        target_disposition_source_proof_fidelity,
    ) = source_record_target_disposition_context(
        folder,
        dict(review_surface),
        run_context=run_context,
    )
    if not isinstance(target_disposition_statement_map, Mapping) or not isinstance(
        target_disposition_source_proof_fidelity, Mapping
    ):
        return [
            "direct source-model review lacks the current source-map or source-proof-fidelity target context"
        ]
    target_disposition_rebind, target_disposition_rebind_error = (
        source_record_target_disposition_rebind_context(
            folder,
            dict(review_surface),
            audit,
            run_context=run_context,
        )
    )
    if target_disposition_rebind_error:
        return [
            "direct source-model review has an invalid target-disposition rebind: "
            + target_disposition_rebind_error
        ]
    # A selected, current v11 source-to-Spec review is the authoritative
    # source-target decision for this exact transaction.  Keep the legacy
    # semantic-model row's dimensional comparison, source locator, and Lean
    # evidence checks, but do not ask it to restate the already-reviewed
    # literal-versus-corrected target disposition.  This is deliberately
    # narrow: an unavailable, stale, or unselected v11 lane leaves the v10
    # disposition gate fully active.
    v11_source_target_current = False
    try:
        from scripts.current_closeout.semantic_review import (
            current_v11_direct_semantic_review_state,
        )

        v11_source_target_current, _v11_source_target_error = (
            current_v11_direct_semantic_review_state(
                ROOT,
                folder,
                context=evidence_context,
            )
        )
    except Exception:
        # The direct v11 lane is an optional replacement only when it can be
        # fully validated from the same immutable evidence transaction.
        v11_source_target_current = False
    review_findings = semantic_model_review_findings(
        paper_id,
        folder,
        judgment_file,
        [dict(semantic_item)],
        dict(judgments),
        digest=audit_digest,
        expected_item_digests=source_record_expected_item_digests(audit),
        expected_item_digest_pins=source_record_expected_item_digest_pins(audit),
        severity="ERROR",
        target_disposition_statement_map=dict(target_disposition_statement_map),
        target_disposition_source_proof_fidelity=dict(
            target_disposition_source_proof_fidelity
        ),
        target_disposition_validated_vocabulary_binding_source_item_ids=(
            audit.get("source_coverage_validated_vocabulary_binding_source_items")
        ),
        target_disposition_validated_vocabulary_direct_route_source_item_ids=(
            audit.get("source_coverage_validated_vocabulary_direct_route_source_items")
        ),
        target_disposition_administrative_projection_rebind=(
            target_disposition_rebind
        ),
        enforce_target_disposition=not v11_source_target_current,
    )
    if review_findings:
        return [
            "direct source-model review is absent, stale, or open: "
            + str(review_findings[0].message)
        ]
    # The direct source contract has now passed every terminal-policy
    # prerequisite using transaction-owned bytes.  Project it onto the exact
    # generated material occurrences rather than returning a root-level
    # waiver.  The strict theorem-realization gate consumes only this
    # runtime-only set, and a malformed/unassociated component simply receives
    # no receipt and remains an error there.
    run_context.record_semantic_contract_executable_terminal_component_receipts(
        _semantic_contract_executable_terminal_component_receipts(
            audit,
            semantic_item,
            source_key=source_key,
            expected_identity=expected_identity,
            spec_declaration=spec_declaration,
            evidence_declaration=evidence_declaration,
            evidence_signature_sha256=recorded_signature,
            evidence_dependency_sha256=recorded_dependency,
            terminal_receipt_sha256=terminal_digest,
        ),
        _issuer=_SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_RECEIPT_ISSUER,
    )
    return []


def source_premise_consistency_findings(
    paper_id: str,
    folder: Path,
    status: object,
    payload: dict[str, object],
) -> list[Finding]:
    """Report elaborated source-record eliminators without trusting names.

    The source-record helper emits this lane only after Lean compares a
    reviewed record domain and a candidate theorem/field by definitional
    equality.  A direct route to ``False`` is therefore incompatible with a
    full closeout.  Data-dependent routes remain visible, but do not claim a
    contradiction until the additional data can be discharged.
    """

    if not schema_version_is_exact(
        payload.get("source_premise_consistency_schema"), 1
    ):
        return []
    severity = (
        "ERROR" if status in {"formalized", "formalized with caveat"} else "WARN"
    )
    audit_path = source_record_audit_file_path(folder, {})
    error = str(payload.get("source_premise_consistency_error") or "").strip()
    if error:
        return [
            Finding(
                severity,
                audit_path,
                f"`{paper_id}` source-premise consistency scan did not complete: {error}",
            )
        ]
    raw_items = payload.get("source_premise_consistency_items")
    if not isinstance(raw_items, list):
        return [
            Finding(
                severity,
                audit_path,
                f"`{paper_id}` source-premise consistency schema is present but its "
                "elaborated result list is missing or malformed",
            )
        ]
    findings: list[Finding] = []
    for raw_item in raw_items:
        if not isinstance(raw_item, dict):
            findings.append(
                Finding(
                    severity,
                    audit_path,
                    f"`{paper_id}` source-premise consistency result contains a malformed item",
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
                    audit_path,
                    f"`{paper_id}` source-premise consistency item lacks a reviewed input "
                    "or well-formed eliminator lists",
                )
            )
            continue
        direct_names = sorted(
            {
                str(candidate.get("candidate") or "").strip()
                for candidate in direct
                if isinstance(candidate, dict)
                and candidate.get("direct_eliminator") is True
                and str(candidate.get("candidate") or "").strip()
            }
        )
        if direct_names:
            findings.append(
                Finding(
                    severity,
                    audit_path,
                    f"`{paper_id}` Lean elaboration found a direct route from reviewed "
                    f"source input `{reviewed}` to `False` via "
                    + ", ".join(direct_names[:4])
                    + ("; ..." if len(direct_names) > 4 else "")
                    + ". The source-facing model premise is inconsistent and cannot "
                    "support a full formalization claim.",
                )
            )
        data_names = sorted(
            {
                str(candidate.get("candidate") or "").strip()
                for candidate in data_dependent
                if isinstance(candidate, dict)
                and candidate.get("direct_eliminator") is False
                and str(candidate.get("candidate") or "").strip()
            }
        )
        if data_names:
            findings.append(
                Finding(
                    "WARN",
                    audit_path,
                    f"`{paper_id}` Lean found a `False` route involving reviewed source "
                    f"input `{reviewed}` plus extra non-proposition data via "
                    + ", ".join(data_names[:4])
                    + ("; ..." if len(data_names) > 4 else "")
                    + ". It remains model-proof debt, not a direct contradiction.",
                )
            )
    return findings


def strict_v11_occurrence_closeout_findings(
    paper_id: str,
    folder: Path,
    payload: Mapping[str, object],
    judgments: Mapping[str, dict[str, object]],
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> tuple[bool, list[Finding]]:
    """Run the authoritative occurrence contract for a strict-v11 closeout.

    The v10 source-record judge classifications remain useful review metadata,
    but they are not a second semantic disposition system once the paper has
    opted into occurrence-indexed contracts.  Return the activation decision
    separately so callers can retire only those legacy heuristics while still
    retaining raw-integrity, freshness, recursion, and semantic-model checks.
    """

    status_payload = (
        run_context.exact_json_payload(folder / "status.json")
        if run_context is not None
        else load_json_object(folder / "status.json")
    ) or {}
    statement_map_path = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    statement_map = (
        run_context.exact_json_payload(statement_map_path)
        if run_context is not None
        else load_json_object(statement_map_path)
    )
    if not source_spec_correspondence_requested(
        status_payload,
        statement_map if isinstance(statement_map, Mapping) else None,
        folder=folder,
    ):
        return False, []

    # Mint scoped source-model field capabilities from the same immutable
    # transaction that will consume them below.  A caller-provided receipt is
    # never accepted here: malformed/stale routes simply yield no capability
    # and the generic occurrence gate retains the component as open.
    if isinstance(run_context, PaperCloseoutRunContext) and run_context.issued_by_builder:
        run_context.record_recursive_field_explicit_parent_component_receipts(
            _recursive_field_explicit_parent_component_receipts(
                paper_id,
                folder,
                payload,
                run_context=run_context,
            ),
            _issuer=_RECURSIVE_FIELD_EXPLICIT_PARENT_RECEIPT_ISSUER,
        )

    try:
        from scripts.audit_conclusion_provenance import (
            theorem_realization_component_contract_findings,
        )
        occurrence_findings = theorem_realization_component_contract_findings(
            paper_id,
            payload,
            judgments,
            status_payload_override=status_payload,
            paper_statement_map_override=(
                statement_map if isinstance(statement_map, Mapping) else None
            ),
            current_source_spec_correspondence_receipts=(
                run_context.current_strict_source_spec_correspondence_receipts()
                if run_context is not None
                else ()
            ),
            semantic_contract_executable_terminal_component_receipts=(
                run_context.current_semantic_contract_executable_terminal_component_receipts()
                if run_context is not None and run_context.issued_by_builder
                else ()
            ),
            recursive_field_explicit_parent_component_receipts=(
                run_context.current_recursive_field_explicit_parent_component_receipts()
                if run_context is not None and run_context.issued_by_builder
                else ()
            ),
            strict_source_scope_item_keys=(
                run_context.current_strict_source_spec_correspondence_scope_keys()
                if run_context is not None
                else None
            ),
        )
    except Exception as exc:  # noqa: BLE001 - a closeout relaxation fails closed.
        return True, [
            Finding(
                "ERROR",
                folder / "PaperInterface.lean",
                f"`{paper_id}` strict-v11 theorem-realization occurrence gate "
                f"could not run: {exc}",
            )
        ]

    converted: list[Finding] = []
    for finding in occurrence_findings:
        fields = f" fields={','.join(finding.fields)}" if finding.fields else ""
        converted.append(
            Finding(
                "ERROR",
                folder / "PaperInterface.lean",
                f"`{paper_id}` strict-v11 theorem-realization occurrence row "
                f"`{finding.row}`, binder `{finding.binder}`{fields}: "
                f"{finding.message}",
            )
        )
    return True, converted


def current_v11_direct_semantic_closeout_state(
    folder: Path,
    status: object,
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> tuple[bool, str]:
    """Return the shared authoritative v11 semantic-lane decision.

    The planner and the evidence-integrity gate already use
    ``v11_direct_semantic_review_state`` to select the exact raw-source to
    expanded-Spec, paper-prerequisite, and material-library review lane.  The
    recursive source-record consumer must use that same decision rather than
    demand a second set of generated binder and semantic-model judgments.

    This does not waive structural or Lean validation: the repository audit
    still checks the source inventory, source/Spec atom correspondence,
    semantic contracts, recursive dependency closure, and focused build.  If
    the v11 evidence is missing or stale, this function returns false and the
    legacy occurrence-indexed lane remains fully active.
    """

    try:
        from scripts.current_closeout.semantic_review import (
            current_v11_direct_semantic_review_state,
        )
        evidence_context = (
            run_context.evidence_context if run_context is not None else None
        )
        return current_v11_direct_semantic_review_state(
            ROOT,
            folder,
            context=evidence_context,
        )
    except Exception as exc:  # noqa: BLE001 - fallback must remain fail closed.
        return False, f"v11 direct semantic-review state is unavailable: {exc}"


@dataclass(frozen=True)
class StrictV11FullSpecSourceRecordCoverage:
    """Current source-record groups discharged by strict full-Spec evidence.

    Both projections are derived from the same runtime-only strict receipt
    transaction.  Keeping them together prevents a manual-complement caller
    from joining a component route minted in one run to semantic-parent credit
    inferred from another run or from persisted JSON.
    """

    component_judgment_keys: frozenset[str] = frozenset()
    semantic_model_judgment_keys: frozenset[str] = frozenset()


class _CurrentStrictV11FullSpecRuntimeIssuerBinding:
    """Object-identity authority for one nonpersistent strict-Spec runtime."""

    __slots__ = ("runtime", "closeout_context")

    def __init__(self) -> None:
        self.runtime: CurrentStrictV11FullSpecSourceRecordRuntime | None = None
        self.closeout_context: PaperCloseoutRunContext | None = None


# A strict-runtime object is valid only when this factory recorded its exact
# object identity.  The closeout context alone is not enough: callers must not
# be able to wrap a real transaction with invented coverage or an invented
# source-record identity capability.
_CURRENT_STRICT_V11_FULL_SPEC_ISSUED_RUNTIMES: weakref.WeakValueDictionary[
    int, object
] = weakref.WeakValueDictionary()


@dataclass(frozen=True)
class CurrentStrictV11FullSpecSourceRecordRuntime:
    """One exact runtime shared by strict coverage and current overlays.

    The source-record identity capability remains process-local and is never
    serialized into a review artifact.  Consumers must use the helpers below,
    which require the same canonical raw payload that the closeout transaction
    validated before exposing either coverage or the opaque capability.
    """

    paper_id: str
    folder: Path
    raw_payload_canonical_sha256: str
    coverage: StrictV11FullSpecSourceRecordCoverage
    _closeout_context: PaperCloseoutRunContext = dataclass_field(
        repr=False, compare=False
    )
    _source_record_identity_context: object = dataclass_field(
        repr=False, compare=False
    )
    _issuer_binding: object = dataclass_field(repr=False, compare=False)

    @property
    def issued_by_factory(self) -> bool:
        """Whether the exact strict-runtime factory issued this object."""

        binding = self._issuer_binding
        context = self._closeout_context
        return (
            _CURRENT_STRICT_V11_FULL_SPEC_ISSUED_RUNTIMES.get(id(self)) is self
            and isinstance(binding, _CurrentStrictV11FullSpecRuntimeIssuerBinding)
            and binding.runtime is self
            and binding.closeout_context is context
            and isinstance(context, PaperCloseoutRunContext)
            and context.issued_by_builder
            and exact_evidence_run_context(context.evidence_context)
        )


def _canonical_payload_sha256(payload: Mapping[str, object]) -> str:
    """Hash a JSON-shaped payload without relying on its object identity."""

    try:
        encoded = json.dumps(
            canonical_digest_payload(payload),
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    except (TypeError, ValueError):
        return ""
    return hashlib.sha256(encoded).hexdigest()


def _strict_v11_full_spec_runtime_context_error(
    runtime: object,
    paper_id: str,
    folder: Path,
    audit_payload: Mapping[str, object],
) -> str:
    """Require the exact canonical raw payload behind a runtime capability."""

    if not isinstance(runtime, CurrentStrictV11FullSpecSourceRecordRuntime):
        return "strict full-Spec runtime is not a factory-issued capability"
    if not runtime.issued_by_factory:
        return "strict full-Spec runtime lacks factory authority"
    try:
        resolved_folder = folder.resolve()
    except (OSError, RuntimeError):
        return "strict full-Spec runtime folder cannot be resolved"
    if runtime.paper_id != paper_id or runtime.folder != resolved_folder:
        return "strict full-Spec runtime belongs to another paper or folder"
    supplied_digest = _canonical_payload_sha256(audit_payload)
    if not supplied_digest or supplied_digest != runtime.raw_payload_canonical_sha256:
        return "strict full-Spec runtime does not match the supplied canonical raw audit"
    exact_audit, audit_error = runtime._closeout_context.current_source_record_audit()
    if audit_error or not isinstance(exact_audit, Mapping):
        return "strict full-Spec runtime no longer has a current canonical raw audit"
    if _canonical_payload_sha256(exact_audit) != supplied_digest:
        return "strict full-Spec runtime canonical raw audit changed"
    return ""


def _mint_current_strict_v11_full_spec_receipts(
    paper_id: str,
    folder: Path,
    context: PaperCloseoutRunContext,
    *,
    status_payload: Mapping[str, object],
    statement_map: Mapping[str, object],
) -> bool:
    """Mint focused strict receipts in an already exact closeout transaction.

    The result of the semantic-contract check is intentionally not itself a
    whole-paper verdict here.  As in the standalone strict-coverage path, only
    individually minted and subsequently selected receipts can remove a source
    record group from the manual queue.
    """

    try:
        paper_statement_map_semantic_contract_findings(
            paper_id,
            folder,
            status_payload.get("status"),
            dict(statement_map),
            context.paper_declaration_index(),
            set(),
            dict(status_payload),
            run_context=context,
        )
    except Exception:
        return False
    return True


def prepare_current_strict_v11_full_spec_source_record_runtime(
    paper_id: str,
    folder: Path,
    audit_payload: Mapping[str, object],
) -> CurrentStrictV11FullSpecSourceRecordRuntime | None:
    """Build one canonical runtime for strict coverage and overlay replays.

    This is intentionally available only for the canonical live paper folder.
    Alternate raw paths, archived audits, and synthetic test folders receive no
    capability and must use their ordinary fail-closed replay paths.  The
    factory runs the external identity helper once through the exact evidence
    transaction, mints the strict source-to-Spec receipts in that transaction,
    and returns only in-memory state.
    """

    try:
        resolved_folder = folder.resolve()
        if resolved_folder != (PAPERS / paper_id).resolve():
            return None
        evidence_context = build_paper_closeout_evidence_context(paper_id)
        context = PaperCloseoutRunContext.from_exact_evidence_context(
            paper_id,
            resolved_folder,
            evidence_context=evidence_context,
        )
    except Exception:
        return None

    exact_audit, audit_error = context.current_source_record_audit()
    if audit_error or not isinstance(exact_audit, Mapping):
        return None
    raw_digest = _canonical_payload_sha256(audit_payload)
    if not raw_digest or raw_digest != _canonical_payload_sha256(exact_audit):
        return None
    identity_context = getattr(
        evidence_context, "source_record_identity_context", None
    )
    if identity_context is None:
        return None

    status_path = resolved_folder / "status.json"
    statement_map_path = resolved_folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    status_payload = context.exact_json_payload(status_path)
    statement_map = context.exact_json_payload(statement_map_path)
    if not isinstance(status_payload, Mapping) or not isinstance(statement_map, Mapping):
        return None
    if not _mint_current_strict_v11_full_spec_receipts(
        paper_id,
        resolved_folder,
        context,
        status_payload=status_payload,
        statement_map=statement_map,
    ):
        return None

    coverage = current_strict_v11_full_spec_source_record_coverage(
        paper_id,
        resolved_folder,
        exact_audit,
        run_context=context,
    )
    binding = _CurrentStrictV11FullSpecRuntimeIssuerBinding()
    runtime = CurrentStrictV11FullSpecSourceRecordRuntime(
        paper_id=paper_id,
        folder=resolved_folder,
        raw_payload_canonical_sha256=raw_digest,
        coverage=coverage,
        _closeout_context=context,
        _source_record_identity_context=identity_context,
        _issuer_binding=binding,
    )
    binding.runtime = runtime
    binding.closeout_context = context
    _CURRENT_STRICT_V11_FULL_SPEC_ISSUED_RUNTIMES[id(runtime)] = runtime
    return runtime


def current_strict_v11_full_spec_source_record_runtime_coverage(
    runtime: object,
    paper_id: str,
    folder: Path,
    audit_payload: Mapping[str, object],
) -> StrictV11FullSpecSourceRecordCoverage | None:
    """Return coverage only when a runtime still matches the canonical raw audit."""

    if _strict_v11_full_spec_runtime_context_error(
        runtime, paper_id, folder, audit_payload
    ):
        return None
    assert isinstance(runtime, CurrentStrictV11FullSpecSourceRecordRuntime)
    return runtime.coverage


def current_strict_v11_full_spec_source_record_runtime_identity_context(
    runtime: object,
    paper_id: str,
    folder: Path,
    audit_payload: Mapping[str, object],
) -> object | None:
    """Expose a validated opaque identity context for the same runtime only."""

    if _strict_v11_full_spec_runtime_context_error(
        runtime, paper_id, folder, audit_payload
    ):
        return None
    assert isinstance(runtime, CurrentStrictV11FullSpecSourceRecordRuntime)
    return runtime._source_record_identity_context


def current_strict_v11_full_spec_source_record_runtime_mutation_findings(
    runtime: object,
) -> list[Finding]:
    """Finalize one manual-complement runtime before it can emit output."""

    if not isinstance(runtime, CurrentStrictV11FullSpecSourceRecordRuntime) or not (
        runtime.issued_by_factory
    ):
        return [
            Finding(
                "ERROR",
                ROOT / "papers",
                "manual-complement strict full-Spec runtime is not factory-issued",
            )
        ]
    return paper_closeout_context_mutation_findings(
        runtime._closeout_context.evidence_context,
        build_input_provider=runtime._closeout_context.build_input_provider,
    )


def current_strict_v11_full_spec_source_record_coverage(
    paper_id: str,
    folder: Path,
    audit_payload: Mapping[str, object],
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> StrictV11FullSpecSourceRecordCoverage:
    """Return groups discharged by one fresh strict full-Spec transaction.

    A strict source-to-Spec receipt is intentionally runtime-only.  During a
    paper closeout this function consumes receipts already minted in the
    shared transaction.  A standalone workflow such as manual-complement
    preparation gets a new exact transaction and reruns just the strict
    source-map contract lane before projecting coverage.  It never accepts a
    checked-in receipt, a route name, or a caller-provided key set as proof.

    The underlying projector requires a one-to-one correspondence between all
    current material component occurrences for a source-record key and the
    fresh full-Spec receipts.  Formula/model/field groups without that exact
    route therefore remain in the ordinary manual queue.
    """

    owned_context = run_context is None
    context = run_context
    if context is None:
        # The standalone capability is intentionally limited to a real paper
        # folder. Test/utility callers without the repository's exact input
        # transaction receive no exemption rather than a live-read shortcut.
        try:
            if folder.resolve() != (PAPERS / paper_id).resolve():
                return StrictV11FullSpecSourceRecordCoverage()
            evidence_context = build_paper_closeout_evidence_context(paper_id)
            context = PaperCloseoutRunContext.from_exact_evidence_context(
                paper_id,
                folder,
                evidence_context=evidence_context,
            )
        except Exception:
            return StrictV11FullSpecSourceRecordCoverage()

    if context.paper_id != paper_id or context.folder != folder.resolve():
        return StrictV11FullSpecSourceRecordCoverage()
    exact_audit, audit_error = context.current_source_record_audit()
    if audit_error or not isinstance(exact_audit, Mapping):
        return StrictV11FullSpecSourceRecordCoverage()
    # The aggregate receipt names the generated semantic surface, not every
    # serialized raw-audit field.  This standalone fallback must bind the same
    # complete canonical payload as the factory-issued runtime before it can
    # project exact-transaction coverage onto the caller's raw object.
    supplied_digest = _canonical_payload_sha256(audit_payload)
    exact_digest = _canonical_payload_sha256(exact_audit)
    if not supplied_digest or supplied_digest != exact_digest:
        return StrictV11FullSpecSourceRecordCoverage()

    status_path = folder / "status.json"
    statement_map_path = folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    status_payload = context.exact_json_payload(status_path)
    statement_map = context.exact_json_payload(statement_map_path)
    if not isinstance(status_payload, Mapping) or not isinstance(statement_map, Mapping):
        return StrictV11FullSpecSourceRecordCoverage()

    # Closeout ordering normally mints the strict receipts before the
    # source-record gate. A standalone manual queue has no such predecessor,
    # so run the same focused Lean contract lane inside this new transaction.
    if owned_context:
        if not _mint_current_strict_v11_full_spec_receipts(
            paper_id,
            folder,
            context,
            status_payload=status_payload,
            statement_map=statement_map,
        ):
            return StrictV11FullSpecSourceRecordCoverage()
        # This focused invocation mints receipt capabilities rather than
        # deciding the whole paper's semantic-contract closeout. A paper map
        # may contain an unrelated failed/refuted/non-strict contract; letting
        # that finding erase every separately current strict receipt would
        # make the manual queue depend on unrelated map rows. The selector
        # below consumes only the scoped, individually minted receipts and
        # rechecks their exact raw association/atom/Spec coordinates. Missing
        # scope or a failed strict item simply leaves its group uncovered.

    rebind_error = str(
        getattr(
            context.evidence_context,
            "administrative_projection_rebind_error",
            "",
        )
        or ""
    )
    if rebind_error:
        return StrictV11FullSpecSourceRecordCoverage()
    rebind = getattr(
        context.evidence_context,
        "administrative_projection_rebind",
        None,
    )
    try:
        from scripts.audit_conclusion_provenance import (
            current_strict_transparent_spec_full_surface_source_record_judgment_keys,
            current_strict_transparent_spec_semantic_parent_judgment_keys,
        )
        component_keys = (
            current_strict_transparent_spec_full_surface_source_record_judgment_keys(
                paper_id,
                exact_audit,
                current_source_spec_correspondence_receipts=(
                    context.current_strict_source_spec_correspondence_receipts()
                ),
                strict_source_scope_item_keys=(
                    context.current_strict_source_spec_correspondence_scope_keys()
                ),
                status_payload_override=status_payload,
                paper_statement_map_override=statement_map,
                administrative_projection_rebind_override=rebind,
            )
        )
        semantic_parent_keys = (
            current_strict_transparent_spec_semantic_parent_judgment_keys(
                paper_id,
                exact_audit,
                current_source_spec_correspondence_receipts=(
                    context.current_strict_source_spec_correspondence_receipts()
                ),
                strict_source_scope_item_keys=(
                    context.current_strict_source_spec_correspondence_scope_keys()
                ),
                status_payload_override=status_payload,
                paper_statement_map_override=statement_map,
                administrative_projection_rebind_override=rebind,
            )
        )
    except Exception:
        return StrictV11FullSpecSourceRecordCoverage()

    # A parent selector returns a route identity, not a permission to invent a
    # source-record key.  Keep only actual current semantic-model rows.  A
    # group shared with a non-semantic raw item is retained later by the manual
    # complement, which has the complete group-membership ledger.
    raw_semantic_items = exact_audit.get("semantic_model_items")
    current_semantic_model_keys: set[str] = set()
    if isinstance(raw_semantic_items, list):
        current_semantic_model_keys = {
            str(item.get("judgment_key") or "").strip()
            for item in raw_semantic_items
            if isinstance(item, Mapping)
            and str(item.get("judgment_key") or "").strip()
        }

    if owned_context and paper_closeout_context_mutation_findings(
        context.evidence_context,
        build_input_provider=context.build_input_provider,
    ):
        return StrictV11FullSpecSourceRecordCoverage()
    return StrictV11FullSpecSourceRecordCoverage(
        component_judgment_keys=frozenset(component_keys),
        semantic_model_judgment_keys=(
            frozenset(semantic_parent_keys) & current_semantic_model_keys
        ),
    )



def current_strict_v11_full_spec_source_record_semantic_model_judgment_keys(
    paper_id: str,
    folder: Path,
    audit_payload: Mapping[str, object],
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> frozenset[str]:
    """Return the semantic-parent half of the strict full-Spec bridge."""

    return current_strict_v11_full_spec_source_record_coverage(
        paper_id,
        folder,
        audit_payload,
        run_context=run_context,
    ).semantic_model_judgment_keys


def source_record_structural_payload_for_closeout(
    run_context: PaperCloseoutRunContext,
) -> tuple[dict[str, object] | None, str]:
    """Return current raw structural inventory for the selected legacy lane.

    Selected v11 closeout exits through its Lean graph before this function is
    called. A stale legacy receipt therefore cannot be revived as merely
    structural input by reading an outer-context compatibility projection.
    """

    return run_context.current_source_record_audit()


@dataclass(frozen=True)
class SourceRecordEvidenceRolePolicy:
    """Which historical raw lanes may contribute to this closeout."""

    raw_semantic_authority: bool
    raw_auxiliary_routing_authority: bool


def source_record_evidence_role_policy(
    *, exact_v11_direct_current: bool
) -> SourceRecordEvidenceRolePolicy:
    """Keep structural reuse distinct from legacy semantic authority."""

    legacy_authority = not exact_v11_direct_current
    return SourceRecordEvidenceRolePolicy(
        raw_semantic_authority=legacy_authority,
        raw_auxiliary_routing_authority=legacy_authority,
    )


def v11_lean_source_structure_findings(
    paper_id: str,
    folder: Path,
    review_surface: Mapping[str, object],
    status: object,
    *,
    run_context: PaperCloseoutRunContext,
) -> list[Finding]:
    """Adapt the current-path structural gate to legacy ``Finding`` output."""

    severity = assumption_finding_severity(
        str(review_surface.get("assumption_policy") or "").strip().lower()
        in ASSUMPTION_POLICY_STRICT_VALUES,
        status,
    )
    gate = run_context.current_v11_primary_gate_result()
    errors = gate.configuration_errors + gate.semantic_errors + gate.structure_errors
    assumption_path = assumption_source_file_path(
        folder, dict(review_surface)
    ).resolve()
    return [
        Finding(
            severity,
            (
                assumption_path
                if "Assumptions.lean support declaration" in message
                else folder / "PaperInterface.lean"
            ),
            message,
        )
        for message in errors
    ]


def check_source_record_audit(
    paper_id: str,
    folder: Path,
    review_surface: dict[str, object],
    status: object,
    strict_assumption_policy: bool,
    *,
    paper_closeout: bool = False,
    prevalidated_strict_v11_occurrence_papers: set[str] | None = None,
    run_context: PaperCloseoutRunContext | None = None,
) -> list[Finding]:
    """Run and validate recursive source-record audit coverage for a paper."""

    severity = assumption_finding_severity(strict_assumption_policy, status)
    selected_v11_closeout = bool(
        paper_closeout
        and run_context is not None
        and run_context.selected_v11_closeout
    )
    exact_v11_direct_current = bool(
        selected_v11_closeout
        and run_context is not None
        and run_context.current_v11_closeout
    )
    evidence_roles = source_record_evidence_role_policy(
        exact_v11_direct_current=selected_v11_closeout
    )
    if selected_v11_closeout:
        assert run_context is not None
        if not exact_v11_direct_current:
            return [
                Finding(
                    severity,
                    folder / "status.json",
                    f"`{paper_id}` selected v11 semantic lane is not current: "
                    + (
                        run_context.v11_direct_semantic_review_error
                        or "the exact v11 semantic gate did not pass"
                    ),
                )
            ]
        findings = v11_lean_source_structure_findings(
            paper_id,
            folder,
            review_surface,
            status,
            run_context=run_context,
        )
        if not findings:
            if prevalidated_strict_v11_occurrence_papers is not None:
                prevalidated_strict_v11_occurrence_papers.add(paper_id)
            run_context.stage_strict_v11_source_record_judgment_handoff()
        return findings
    payload, error = (
        source_record_structural_payload_for_closeout(
            run_context,
        )
        if run_context is not None
        else run_source_record_audit_helper(paper_id)
    )
    if error:
        return [Finding(severity, folder / "PaperInterface.lean", f"`{paper_id}` source-record audit failed: {error}")]
    if payload is None:
        return [Finding(severity, folder / "PaperInterface.lean", f"`{paper_id}` source-record audit produced no payload")]

    semantic_contract_revalidation: object | None = None
    effective_semantic_errors: Mapping[str, object] = {
        # A complete v11 lane owns source-contract association semantics. The
        # historical raw scan may retain obsolete wrapper-pair diagnostics,
        # but those cannot become a second semantic acceptance lane.
        "source_contract_association_errors": [],
    }
    if evidence_roles.raw_semantic_authority:
        (
            semantic_contract_revalidation,
            semantic_contract_revalidation_error,
        ) = source_record_semantic_contract_revalidation_for_payload(
            folder,
            payload,
            run_context=run_context,
        )
        if semantic_contract_revalidation_error:
            return [
                Finding(
                    severity,
                    folder / "PaperInterface.lean",
                    f"`{paper_id}` source-record semantic-contract revalidation is invalid: "
                    + semantic_contract_revalidation_error,
                )
            ]
        semantic_surface_error = source_record_effective_semantic_surface_error(
            payload,
            semantic_contract_revalidation=semantic_contract_revalidation,
        )
        if semantic_surface_error:
            return [
                Finding(
                    severity,
                    folder / "PaperInterface.lean",
                    f"`{paper_id}` source-record audit has an invalid semantic surface: "
                    + semantic_surface_error,
                )
            ]
        effective_semantic_errors = source_record_effective_semantic_errors(
            payload,
            semantic_contract_revalidation=semantic_contract_revalidation,
        )
    findings: list[Finding] = []
    findings.extend(source_premise_consistency_findings(paper_id, folder, status, payload))
    findings.extend(
        source_theorem_coverage_component_premise_findings(
            paper_id,
            folder,
            status,
            payload,
        )
    )
    findings.extend(
        source_theorem_coverage_type_certificate_result_findings(
            paper_id,
            folder,
            status,
            payload,
        )
    )
    missing_configured_rows = sorted(
        {
            str(row).strip()
            for row in payload.get("missing_configured_review_rows") or []
            if isinstance(row, str) and row.strip()
        }
    )
    if missing_configured_rows:
        findings.append(
            Finding(
                "ERROR",
                folder / "PaperInterface.lean",
                f"`{paper_id}` source-record audit omitted "
                f"{len(missing_configured_rows)} configured review row(s); "
                "audit coverage is incomplete: "
                + ", ".join(missing_configured_rows[:8])
                + ("; ..." if len(missing_configured_rows) > 8 else ""),
            )
        )

    # The raw generator parses the Assumptions.lean declaration surface and
    # reports support declarations not selected by the configured review
    # surface.  Treat that semantic inventory as a closeout obligation.  In
    # particular, do not reconstruct this check from declaration spellings:
    # a source-backed premise can be hidden by an arbitrary name.
    unconfigured_assumption_support_rows = {
        str(row).strip()
        for row in payload.get("unconfigured_assumption_support_rows") or []
        if isinstance(row, str) and row.strip()
    }
    configured_support_names: set[str] = set()
    for key in (
        "assumption_names",
        "auxiliary_names",
        "quarantined_auxiliary_names",
    ):
        values = review_surface.get(key) or []
        if isinstance(values, list):
            configured_support_names.update(
                str(value).strip()
                for value in values
                if isinstance(value, str) and value.strip()
            )
    # A saved raw scan may predate a status-only classification of one of the
    # exact support declarations it already inventoried. Resolve that current
    # classification against the raw qualified identities. An ambiguous tail
    # match grants no credit, and the separate status-surface gate still proves
    # that the configured name is declared in Assumptions.lean.
    for configured_name in configured_support_names:
        qualified = (
            configured_name
            if configured_name.startswith(paper_id + ".")
            else paper_id + "." + configured_name
        )
        candidates = {
            row
            for row in unconfigured_assumption_support_rows
            if (
                row == configured_name
                or row == qualified
                or row.endswith("." + configured_name)
            )
        }
        if len(candidates) == 1:
            unconfigured_assumption_support_rows -= candidates
    unconfigured_assumption_support_rows = sorted(unconfigured_assumption_support_rows)
    if unconfigured_assumption_support_rows:
        findings.append(
            Finding(
                severity,
                folder / DEFAULT_ASSUMPTION_SOURCE_FILE,
                f"`{paper_id}` source-record audit found "
                f"{len(unconfigured_assumption_support_rows)} unconfigured "
                "Assumptions.lean support declaration(s). Each must be listed "
                "as an audited source assumption or explicitly classified as "
                "auxiliary/quarantined support: "
                + ", ".join(unconfigured_assumption_support_rows[:8])
                + ("; ..." if len(unconfigured_assumption_support_rows) > 8 else ""),
            )
        )

    # A PaperInterface declaration remains semantically relevant when a
    # selected theorem/assumption reaches it through its type or proof graph.
    # `auxiliary_names` is a presentation classification, never a waiver. The
    # shared context accepts either the generated raw ledger or a narrow,
    # raw-bound issued routing supplement. The latter is intentionally only a
    # reachability transport: it cannot supply source/proof credit below.
    # A complete v11 lane instead validates Lean's current expanded paper-
    # prerequisite graph directly against its raw-source ledger, so the
    # historical raw-routing supplement is neither needed nor authoritative.
    unresolved_auxiliaries: list[dict[str, object]] = []
    if (
        evidence_roles.raw_auxiliary_routing_authority
        and str(payload.get("prompt_version") or "").strip()
        == REQUIRED_SOURCE_RECORD_PROMPT_VERSION
    ):
        # A real v10 raw receipt always names its paper. Small historical
        # diagnostic fixtures predate that identity field, so retain their
        # direct-ledger behavior rather than pretending they can authenticate
        # a canonical supplement.
        use_authenticated_routing_context = (
            str(payload.get("paper") or "").strip() == paper_id
        )
        routing_context = None
        routing_context_error = ""
        if use_authenticated_routing_context:
            if run_context is not None:
                routing_context = getattr(
                    run_context.evidence_context,
                    "auxiliary_routing_context",
                    None,
                )
                routing_context_error = str(
                    getattr(
                        run_context.evidence_context,
                        "auxiliary_routing_context_error",
                        "",
                    )
                    or ""
                )
            else:
                (
                    routing_context,
                    routing_context_error,
                ) = current_auxiliary_routing_context(
                    root=ROOT,
                    paper_dir=folder,
                    paper=paper_id,
                    audit_payload=payload,
                )
        if use_authenticated_routing_context and routing_context is None:
            findings.append(
                Finding(
                    severity,
                    folder / "PaperInterface.lean",
                    f"`{paper_id}` reachable PaperInterface auxiliary routing evidence "
                    "is unavailable: "
                    + (routing_context_error or "unknown validation error")
                    + ". Auxiliary names cannot suppress transitive proof/type "
                    "dependencies.",
                )
            )
        elif use_authenticated_routing_context:
            (
                augmented_payload,
                augmented_payload_error,
            ) = routing_context.audit_payload_with_authenticated_ledger(payload)
            if augmented_payload is None:
                findings.append(
                    Finding(
                        severity,
                        folder / "PaperInterface.lean",
                        f"`{paper_id}` reachable PaperInterface auxiliary routing evidence "
                        "cannot be bound to the raw audit: "
                        + (augmented_payload_error or "unknown validation error"),
                    )
                )
                augmented_payload = None
            quarantine_configuration_errors = (
                routing_context.quarantine_configuration_errors()
            )
            for error in quarantine_configuration_errors:
                findings.append(
                    Finding(
                        severity,
                        folder / "status.json",
                        f"`{paper_id}` reachable auxiliary quarantine configuration is invalid: "
                        + error,
                    )
                )
            if augmented_payload is not None:
                unresolved_auxiliaries = list(
                    routing_context.unresolved_auxiliaries()
                )
            ambiguous_auxiliary_references = list(
                routing_context.ambiguous_references()
            )
            for item in ambiguous_auxiliary_references:
                candidates = ", ".join(
                    str(candidate).strip()
                    for candidate in item.get("candidate_auxiliaries") or []
                    if str(candidate).strip()
                )
                findings.append(
                    Finding(
                        severity,
                        folder / "PaperInterface.lean",
                        f"`{paper_id}` cannot resolve a transitive local reference from a "
                        "selected review root that may target PaperInterface auxiliary "
                        f"declaration(s): {candidates or 'unknown'}. Use an exact qualified "
                        "reference and then provide a source-map route/support or explicit "
                        "quarantine reason; suffix matching is not audit evidence.",
                    )
                )
        else:
            # Fixture/legacy compatibility only. Current evidence reaches the
            # branch above and cannot bypass its shared authenticated context.
            quarantine_configuration_errors = [
                str(error).strip()
                for error in payload.get(
                    "reachable_paper_interface_auxiliary_quarantine_configuration_errors"
                )
                or []
                if str(error).strip()
            ]
            for error in quarantine_configuration_errors:
                findings.append(
                    Finding(
                        severity,
                        folder / "status.json",
                        f"`{paper_id}` reachable auxiliary quarantine configuration is invalid: "
                        + error,
                    )
                )
            unresolved_auxiliaries = [
                item
                for item in payload.get(
                    "unresolved_reachable_paper_interface_auxiliaries"
                )
                or []
                if isinstance(item, dict)
            ]
            ambiguous_auxiliary_references = [
                item
                for item in payload.get(
                    "ambiguous_reachable_paper_interface_auxiliary_references"
                )
                or []
                if isinstance(item, dict)
            ]
            for item in ambiguous_auxiliary_references:
                candidates = ", ".join(
                    str(candidate).strip()
                    for candidate in item.get("candidate_auxiliaries") or []
                    if str(candidate).strip()
                )
                findings.append(
                    Finding(
                        severity,
                        folder / "PaperInterface.lean",
                        f"`{paper_id}` cannot resolve a transitive local reference from a "
                        "selected review root that may target PaperInterface auxiliary "
                        f"declaration(s): {candidates or 'unknown'}. Use an exact qualified "
                        "reference and then provide a source-map route/support or explicit "
                        "quarantine reason; suffix matching is not audit evidence.",
                    )
                )

    semantic_model_config_errors = [
        str(error).strip()
        for error in payload.get("semantic_model_review_configuration_errors") or []
        if str(error).strip()
    ]
    for error in semantic_model_config_errors:
        findings.append(
            Finding(
                severity,
                folder / "status.json",
                f"`{paper_id}` semantic-model review configuration is invalid: {error}",
            )
        )
    semantic_model_target_route_errors = [
        str(error).strip()
        for error in payload.get("semantic_model_target_route_errors") or []
        if str(error).strip()
    ]
    for error in semantic_model_target_route_errors:
        findings.append(
            Finding(
                severity,
                folder / "status.json",
                f"`{paper_id}` semantic-model target routing is invalid: {error}",
            )
        )
    source_contract_association_errors = [
        str(error).strip()
        for error in effective_semantic_errors.get(
            "source_contract_association_errors",
            payload.get("source_contract_association_errors") or [],
        )
        if str(error).strip()
    ]
    for error in source_contract_association_errors:
        findings.append(
            Finding(
                severity,
                folder / "PaperInterface.lean",
                f"`{paper_id}` generated source-contract association is invalid: {error}",
            )
        )
    semantic_model_items = [
        item
        for item in payload.get("semantic_model_items") or []
        if isinstance(item, dict)
    ]

    field_count = int(payload.get("recursive_field_count") or 0)
    input_count = int(payload.get("boundary_input_count") or 0)
    row_count = len(payload.get("rows_with_record_premises") or [])
    conclusion_dependencies = [
        item
        for item in payload.get("conclusion_dependency_items") or []
        if isinstance(item, dict)
    ]
    recursion_failures = [
        item for item in payload.get("recursion_failures") or []
        if isinstance(item, dict)
    ]
    if recursion_failures:
        return findings + [
            Finding(
                severity,
                folder / "PaperInterface.lean",
                f"`{paper_id}` source-record recursion failed before reaching source-backed leaves: "
                + "; ".join(
                    str(item.get("path") or item.get("structure") or item)
                    + ": "
                    + str(item.get("message") or item.get("kind") or "unexplained recursion failure")
                    for item in recursion_failures[:5]
                )
                + ("; ..." if len(recursion_failures) > 5 else ""),
            )
        ]
    if (
        field_count <= 0
        and input_count <= 0
        and row_count <= 0
        and not conclusion_dependencies
        and not semantic_model_items
    ):
        empty_source_record_surface = True
    else:
        empty_source_record_surface = False

    digest = str(payload.get("source_record_audit_sha256") or "").strip()
    raw_integrity_error = source_record_raw_integrity_error_if_current(payload)
    if raw_integrity_error:
        findings.append(
            Finding(
                severity,
                folder / "PaperInterface.lean",
                f"`{paper_id}` source-record helper returned an unauthenticated raw "
                "audit surface: " + raw_integrity_error,
            )
        )
    expected_keys = {
        str(key).strip()
        for key in payload.get("expected_field_judgment_keys") or []
        if str(key).strip()
    }
    expected_input_keys = source_record_required_input_judgment_keys(
        payload,
        semantic_contract_revalidation=semantic_contract_revalidation,
    )
    traceability_input_keys = source_record_traceability_input_judgment_keys(
        payload
    )
    # The structural replay removes only an independent duplicate human
    # judgment. A current sidecar may still retain that raw group member for
    # aggregate coverage, but it can never become an extra source premise.
    replay_traceability_input_keys = (
        source_record_required_input_judgment_keys(payload) - expected_input_keys
    )
    traceability_input_keys.update(replay_traceability_input_keys)
    # Covered inputs remain in the generated audit surface for traceability.
    expected_keys.update(expected_input_keys)
    expected_semantic_model_keys = {
        str(key).strip()
        for key in payload.get("expected_semantic_model_judgment_keys") or []
        if str(key).strip()
    }
    # Older payloads can still carry the generated items without the explicit
    # expected-key ledger. Do not let an incomplete migration make them optional.
    expected_semantic_model_keys.update(
        str(item.get("judgment_key") or "").strip()
        for item in semantic_model_items
        if str(item.get("judgment_key") or "").strip()
    )
    all_expected_keys = expected_keys | expected_semantic_model_keys
    # A current sidecar may retain source-to-Lean-ledger-covered ordinary
    # inputs. They are not required a second time, but treating their generated
    # structural keys as stale extras would make the traceability policy
    # self-contradictory. Aggregate-pinned record containers are added only
    # after their loaded sidecar receipt has passed the stricter schema-5
    # currentness test below.
    allowed_judgment_keys = all_expected_keys | traceability_input_keys
    expected_item_digests = source_record_expected_item_digests(payload)
    expected_item_digest_pins = source_record_expected_item_digest_pins(payload)
    # `PaperInterface` owns the one human semantic surface.  The raw
    # source-record scan may instead enter through the configured proof
    # module, provided Lean's pinned import closure contains that semantic
    # surface and its explicitly paired endpoints.  This is deliberately a
    # closure relation, not a filename waiver: an implementation module that
    # merely happens to be paper-local remains inadmissible.
    expected_import_module = f"{paper_id}.PaperInterface"
    configured_proof_module = str(review_surface.get("proof_module") or "").strip()
    configured_proof_path = proof_endpoint_source_file_path(
        folder, review_surface
    ).resolve()
    configured_source_path = review_surface_source_file_path(
        folder, review_surface
    ).resolve()
    has_configured_spec_proof_pairs = isinstance(
        review_surface.get("proposition_spec_proofs"), dict
    ) and bool(review_surface.get("proposition_spec_proofs"))

    def repository_lean_module(path: Path) -> str:
        relative = path.relative_to(ROOT).with_suffix("")
        parts = list(relative.parts)
        if parts[:1] == ["papers"]:
            parts = parts[1:]
        return ".".join(parts)

    try:
        actual_proof_module = repository_lean_module(configured_proof_path)
    except ValueError:
        actual_proof_module = ""

    def source_record_import_is_admissible(record: Mapping[str, object]) -> bool:
        import_module = str(record.get("import_module") or "").strip()
        if not import_module or import_module == expected_import_module:
            return True
        admissible_proof_modules = {
            module
            for module in (configured_proof_module, actual_proof_module)
            if module
        }
        if (
            not actual_proof_module
            or import_module not in admissible_proof_modules
            or not has_configured_spec_proof_pairs
        ):
            return False
        closure = record.get(SOURCE_RECORD_LEAN_IMPORT_CLOSURE_FIELD)
        if not isinstance(closure, Mapping):
            return False
        if str(closure.get("entry_module") or "").strip() != import_module:
            return False
        loaded = closure.get("lean_loaded_modules")
        if not isinstance(loaded, list) or expected_import_module not in loaded:
            return False
        sources = closure.get("sources")
        if not isinstance(sources, list):
            return False
        try:
            expected_paths = {
                expected_import_module: str(configured_source_path.relative_to(ROOT)),
                actual_proof_module: str(configured_proof_path.relative_to(ROOT)),
            }
            if import_module == configured_proof_module and (
                configured_proof_module != actual_proof_module
            ):
                configured_path = (
                    ROOT
                    / "papers"
                    / Path(*configured_proof_module.split("."))
                ).with_suffix(".lean")
                expected_paths[configured_proof_module] = str(
                    configured_path.relative_to(ROOT)
                )
        except ValueError:
            return False
        seen = {
            str(source.get("module") or "").strip(): str(
                source.get("path") or ""
            ).strip()
            for source in sources
            if isinstance(source, Mapping)
        }
        return all(seen.get(module) == path for module, path in expected_paths.items())

    if "import_module" in payload:
        current_import_module = str(payload.get("import_module") or "").strip()
        if not source_record_import_is_admissible(payload):
            findings.append(
                Finding(
                    severity,
                    folder / "PaperInterface.lean",
                    f"`{paper_id}` source-record audit helper imported "
                    f"`{current_import_module or 'missing'}`; recursive provenance audits "
                    f"must build `{expected_import_module}` or the configured proof module "
                    "with a pinned Lean closure containing both the semantic Specs and their "
                    "explicitly paired endpoints.",
                )
            )
    audit_file = source_record_audit_file_path(folder, review_surface)
    judgment_file = source_record_judgment_file_path(folder, review_surface)
    saved_audit = (
        run_context.saved_source_record_audit(audit_file)
        if run_context is not None
        else load_json_object(audit_file)
    )
    if not saved_audit:
        findings.append(
            Finding(
                severity,
                audit_file,
                f"`{paper_id}` source-record audit found {input_count} boundary-shaped input(s), "
                f"{row_count} record-backed row(s), and {field_count} recursive field(s), but "
                f"`{repo_display_path(audit_file)}` is missing. Run the source-record audit helper "
                "and feed the generated Lean-checked input/field payload to the LLM judge.",
            )
        )
    else:
        saved_integrity_error = source_record_raw_integrity_error_if_current(
            saved_audit
        )
        if saved_integrity_error:
            findings.append(
                Finding(
                    severity,
                    audit_file,
                    f"`{paper_id}` saved source-record audit cannot provide evidence: "
                    + saved_integrity_error,
                )
            )
        saved_digest = str(saved_audit.get("source_record_audit_sha256") or "").strip()
        if digest and saved_digest != digest:
            findings.append(
                Finding(
                    severity,
                    audit_file,
                    f"`{paper_id}` source-record audit payload is stale: saved digest "
                    f"`{saved_digest or 'missing'}` but current digest is `{digest}`.",
                )
            )
        saved_prompt_version = str(saved_audit.get("prompt_version") or "").strip()
        if saved_prompt_version != REQUIRED_SOURCE_RECORD_PROMPT_VERSION:
            findings.append(
                Finding(
                    severity,
                    audit_file,
                    f"`{paper_id}` source-record audit payload prompt version is stale or missing: "
                    f"`{saved_prompt_version or 'missing'}`.",
                )
            )
        if "import_module" in saved_audit:
            saved_import_module = str(saved_audit.get("import_module") or "").strip()
            if not source_record_import_is_admissible(saved_audit):
                findings.append(
                    Finding(
                        severity,
                        audit_file,
                        f"`{paper_id}` saved source-record audit imported "
                        f"`{saved_import_module or 'missing'}`; regenerate the payload from "
                        f"`{expected_import_module}` or the configured proof module with "
                        "a pinned closure tying endpoints back to PaperInterface.",
                    )
                )

    corrected_scope_current = False
    try:
        status_payload = (
            run_context.exact_json_payload(folder / "status.json")
            if run_context is not None
            else load_json_object(folder / "status.json")
        ) or {}
        corrected_scope_current = (
            run_context.corrected_scope_current(
                status_payload,
                raise_on_error=True,
            )
            if run_context is not None
            else evaluate_author_approved_corrected_scope(
                folder, status_payload
            )
        )
        if (
            corrected_scope_current
            and not unresolved_auxiliaries
            and not paper_closeout
        ):
            return findings
    except Exception as exc:  # noqa: BLE001 - continue into fail-closed legacy checks.
        findings.append(
            Finding(
                severity,
                folder / "status.json",
                f"`{paper_id}` corrected-model scope contract could not run: {exc}",
            )
        )

    if (
        empty_source_record_surface
        and not unresolved_auxiliaries
        and not paper_closeout
    ):
        return findings

    judgments = (
        run_context.source_record_judgments(judgment_file, payload)
        if run_context is not None
        else source_record_judgment_items(
            judgment_file,
            paper_id,
            current_raw_audit=payload,
            paper_dir=folder,
        )
    )
    strict_v11_occurrence_closeout = False
    v11_direct_current = exact_v11_direct_current
    if paper_closeout:
        if not v11_direct_current:
            v11_direct_current, _v11_direct_error = (
                current_v11_direct_semantic_closeout_state(
                    folder,
                    status,
                    run_context=run_context,
                )
            )
        if v11_direct_current:
            # The exact source/Spec, paper-prerequisite, and library ledgers
            # are the selected semantic-review lane.  The repository audit
            # independently checks their source atoms, Lean contracts, proof
            # closure, and build, so generated v10 binder/model rows would be
            # duplicate judgments over the same expanded propositions.
            strict_v11_occurrence_closeout = True
            occurrence_closeout_findings: list[Finding] = []
        else:
            (
                strict_v11_occurrence_closeout,
                occurrence_closeout_findings,
            ) = strict_v11_occurrence_closeout_findings(
                paper_id,
                folder,
                payload,
                judgments,
                run_context=run_context,
            )
        if (
            strict_v11_occurrence_closeout
            and not occurrence_closeout_findings
            and prevalidated_strict_v11_occurrence_papers is not None
        ):
            prevalidated_strict_v11_occurrence_papers.add(paper_id)
        findings.extend(occurrence_closeout_findings)
    optional_conclusion_dependency_keys = (
        source_record_optional_conclusion_dependency_traceability_keys(
            payload,
            judgments,
            digest=digest,
            expected_item_digests=expected_item_digests,
            expected_item_digest_pins=expected_item_digest_pins,
        )
    )
    allowed_judgment_keys.update(optional_conclusion_dependency_keys)
    enforce_target_disposition = (
        str(payload.get("prompt_version") or "").strip()
        == REQUIRED_SOURCE_RECORD_PROMPT_VERSION
    )
    target_disposition_statement_map: dict[str, object] | None = None
    target_disposition_source_proof_fidelity: dict[str, object] | None = None
    target_disposition_administrative_projection_rebind: Any | None = None
    target_disposition_formalization_regularity_context = None
    target_disposition_rebind_error = ""
    if enforce_target_disposition:
        (
            target_disposition_statement_map,
            target_disposition_source_proof_fidelity,
        ) = source_record_target_disposition_context(
            folder,
            review_surface,
            run_context=run_context,
        )
        if run_context is not None and payload is _legacy_source_record_audit_payload(
            run_context.evidence_context
        ):
            legacy_state = _legacy_source_record_state(
                run_context.evidence_context
            )
            target_disposition_formalization_regularity_context = getattr(
                legacy_state,
                "configured_assumption_regularity_context",
                None,
            )
        else:
            target_disposition_formalization_regularity_context, _regularity_context_error = (
                load_configured_assumption_formalization_regularity_context(
                    folder,
                    payload,
                    status_payload=(
                        run_context.exact_json_payload(folder / "status.json")
                        if run_context is not None
                        else load_json_object(folder / "status.json")
                    ),
                )
            )
        if isinstance(saved_audit, dict):
            (
                target_disposition_administrative_projection_rebind,
                target_disposition_rebind_error,
            ) = source_record_target_disposition_rebind_context(
                folder,
                review_surface,
                saved_audit,
                run_context=run_context,
            )
            if target_disposition_rebind_error:
                findings.append(
                    Finding(
                        severity,
                        audit_file,
                        f"`{paper_id}` administrative source-status projection rebind is invalid: "
                        + target_disposition_rebind_error,
                    )
                )

    # Under the v11 lane the exact expanded Specs, every material paper
    # prerequisite, and every material library declaration have already been
    # reviewed from their semantic contents, while Lean checks the paired proof
    # endpoints and their recursive derivations.  Requiring the same reachable
    # helper to acquire another source-map route merely because its declaration
    # happens to live in PaperInterface would make code location semantic.  The
    # location-independent v11 review therefore supersedes this legacy
    # PaperInterface-only auxiliary-routing diagnostic.
    if unresolved_auxiliaries and not v11_direct_current:
        for item in unresolved_auxiliaries:
            declaration = str(item.get("declaration") or "unknown declaration").strip()
            disposition = str(item.get("disposition") or "unresolved").strip()
            findings.append(
                Finding(
                    severity,
                    folder / "PaperInterface.lean",
                    f"`{paper_id}` selected review roots transitively reach PaperInterface "
                    f"auxiliary `{declaration}` without an admissible semantic route "
                    f"({disposition}). Add an exact fully-qualified source-map route/support, "
                    "or put it in quarantined_auxiliary_names with a documented source "
                    "reason. Lean's elaborated dependency graph discovers reachability; "
                    "separate derivational or lexical receipts cannot grant closeout credit.",
                )
            )

    if corrected_scope_current or empty_source_record_surface:
        return findings

    # A record-valued conclusion input cannot be discharged by field labels or
    # by a fresh builder alone.  It is resolved only through the same complete
    # generated semantic binding that the later hidden-premise lane consumes.
    # The saved payload must be the current helper snapshot before the shared
    # binding reader is allowed to expose anything from it.
    complete_record_model_bindings: dict[
        str, tuple[tuple[frozenset[str], str, frozenset[str]], ...]
    ] = {}
    source_record_snapshot_current = (
        isinstance(saved_audit, dict)
        and bool(digest)
        and str(saved_audit.get("source_record_audit_sha256") or "").strip()
        == digest
        and str(payload.get("prompt_version") or "").strip()
        == REQUIRED_SOURCE_RECORD_PROMPT_VERSION
        and str(saved_audit.get("prompt_version") or "").strip()
        == REQUIRED_SOURCE_RECORD_PROMPT_VERSION
        and source_record_import_is_admissible(payload)
        and source_record_import_is_admissible(saved_audit)
        and not missing_configured_rows
        and not semantic_model_config_errors
        and not semantic_model_target_route_errors
        and not source_contract_association_errors
        and not source_record_target_route_error(saved_audit)
        and not source_record_raw_integrity_error_if_current(saved_audit)
    )
    if source_record_snapshot_current and not strict_v11_occurrence_closeout:
        complete_record_model_bindings = (
            source_record_complete_model_record_bindings(
                paper_id,
                folder,
                review_surface,
                status,
                run_context=run_context,
            )
        )

    def record_dependency_has_complete_model_binding(item: dict[str, object]) -> bool:
        """Match only one *caller* record dependency to a full binding.

        A manifest-pinned result-domain record is intentionally excluded here:
        it is not an external certificate merely because its transition
        closure has record fields.  It must satisfy the stricter operational
        outcome-domain route below, including an existential nonvacuity proof.
        """

        if str(item.get("kind") or "").strip() != "record_conclusion_input":
            return False
        if item.get("elaborated_result_path") is not None:
            return False
        qualified = _generated_item_qualified_declaration(item)
        binder_names = _generated_dependency_binder_names(item)
        root = str(item.get("record") or "").strip()
        if not qualified or not binder_names or not is_fully_qualified_lean_identity(root):
            return False
        return any(
            binding_root == root and binder_names == binding_names
            for binding_names, binding_root, _aliases in complete_record_model_bindings.get(
                qualified, ()
            )
        )

    source_input_items_by_key: dict[str, list[dict[str, object]]] = {}
    for raw_input_item in (
        list(payload.get("theorem_facing_input_items") or [])
        + list(payload.get("boundary_input_items") or [])
        + conclusion_dependencies
        + list(payload.get("type_valued_certificate_result_items") or [])
    ):
        if not isinstance(raw_input_item, dict):
            continue
        input_key = str(raw_input_item.get("judgment_key") or "").strip()
        if input_key:
            source_input_items_by_key.setdefault(input_key, []).append(raw_input_item)

    def input_target_disposition_is_valid(
        key: str, judgment: dict[str, object]
    ) -> bool:
        if not enforce_target_disposition:
            return True
        return not any(
            source_input_target_disposition_errors(
                item,
                judgment,
                statement_map=target_disposition_statement_map,
                source_proof_fidelity=target_disposition_source_proof_fidelity,
                status=status,
                administrative_projection_rebind=(
                    target_disposition_administrative_projection_rebind
                ),
                configured_assumption_formalization_regularity_context=(
                    target_disposition_formalization_regularity_context
                ),
            )
            for item in source_input_items_by_key.get(key, [])
        )

    def exact_source_antecedent(key: str) -> bool:
        judgment = judgments.get(key, {})
        if str(judgment.get("classification") or "").strip() != "validated_source_assumption":
            return False
        if judgment.get("prompt_version_stale") or judgment.get("metadata_missing"):
            return False
        if not source_record_judgment_current(
            key,
            judgment,
            digest=digest,
            expected_item_digests=expected_item_digests,
            expected_item_digest_pins=expected_item_digest_pins,
        ):
            return False
        if not input_target_disposition_is_valid(key, judgment):
            return False
        location = str(
            judgment.get("source_location")
            or judgment.get("source_evidence")
            or ""
        ).strip()
        return bool(location and SOURCE_RECORD_EXACT_LOCATOR_RE.search(location))

    exact_source_antecedent_keys = {
        key for key in expected_keys if exact_source_antecedent(key)
    }

    def dependency_has_resolved_constructor(item: dict[str, object]) -> bool:
        """Accept non-record constructors only through checked sidecar contracts.

        A fresh builder of a record type does not identify the arbitrary record
        binder supplied to the reviewed declaration.
        """

        if item.get("kind") == "record_conclusion_input":
            return False
        if item.get("valid_constructors"):
            return True
        key = str(item.get("judgment_key") or "").strip()
        return checked_projection_result(
            item,
            judgments.get(key),
            exact_source_antecedent_keys,
        ).accepted

    def dependency_checked_projection_error(item: dict[str, object]) -> str:
        """Return the fail-closed reason for this dependency's projection route."""

        key = str(item.get("judgment_key") or "").strip()
        return checked_projection_result(
            item,
            judgments.get(key),
            exact_source_antecedent_keys,
        ).reason

    def conclusion_input_is_exact_source_antecedent(item: dict[str, object]) -> bool:
        if item.get("conclusion_fields"):
            return False
        if str(item.get("kind") or "").strip() not in {
            "aliased_conclusion_bridge_input",
            "bool_certificate_input",
            "direct_conclusion_input",
            "selector_certificate_input",
            "unexpanded_local_reducible_type_input",
        }:
            return False
        key = str(item.get("judgment_key") or "").strip()
        return bool(key and exact_source_antecedent(key))

    def conclusion_input_is_current_source_convention(item: dict[str, object]) -> bool:
        key = str(item.get("judgment_key") or "").strip()
        judgment = judgments.get(key)
        return bool(
            key
            and isinstance(judgment, dict)
            and current_approved_source_convention_antecedent(
                item,
                judgment,
                digest=digest,
                expected_item_digests=expected_item_digests,
                expected_item_digest_pins=expected_item_digest_pins,
                statement_map=target_disposition_statement_map,
                source_proof_fidelity=target_disposition_source_proof_fidelity,
                status=status,
                administrative_projection_rebind=(
                    target_disposition_administrative_projection_rebind
                ),
            )
        )

    def conclusion_dependency_is_unresolved(item: dict[str, object]) -> bool:
        return not (
            conclusion_input_is_exact_source_antecedent(item)
            or conclusion_input_is_current_source_convention(item)
            or dependency_has_resolved_constructor(item)
            or record_dependency_has_complete_model_binding(item)
        )

    unresolved_conclusion_dependencies = (
        []
        if strict_v11_occurrence_closeout
        else [
            item
            for item in conclusion_dependencies
            if conclusion_dependency_is_unresolved(item)
        ]
    )

    for item in unresolved_conclusion_dependencies:
        row = str(item.get("row") or "unknown row")
        binder = str(item.get("binder") or "unknown binder")
        kind = str(item.get("kind") or "conclusion dependency")
        fields = [
            str(field.get("judgment_key") or field.get("path") or "")
            for field in item.get("conclusion_fields") or []
            if isinstance(field, dict)
            and str(field.get("judgment_key") or field.get("path") or "")
            and not (
                field.get("source_antecedent_eligible")
                and exact_source_antecedent(
                    str(field.get("judgment_key") or field.get("path") or "")
                )
            )
        ]
        rejected_reasons: list[str] = []
        for candidate in item.get("rejected_constructors") or []:
            if not isinstance(candidate, dict):
                continue
            declaration = str(candidate.get("declaration") or "unnamed constructor")
            circular_inputs = [
                str(value) for value in candidate.get("circular_inputs") or [] if str(value)
            ]
            rejected_reasons.append(
                declaration
                + (": " + "; ".join(circular_inputs[:2]) if circular_inputs else "")
            )
        conditional_reasons: list[str] = []
        for candidate in item.get("conditional_constructors") or []:
            if not isinstance(candidate, dict):
                continue
            declaration = str(candidate.get("declaration") or "unnamed constructor")
            conditional_inputs = [
                str(value) for value in candidate.get("conditional_inputs") or [] if str(value)
            ]
            conditional_reasons.append(
                declaration
                + (": " + "; ".join(conditional_inputs[:2]) if conditional_inputs else "")
            )
        details = f"reviewed row `{row}` binder `{binder}` ({kind})"
        if fields:
            details += " consumes conclusion field(s) " + ", ".join(fields[:6])
            if len(fields) > 6:
                details += ", ..."
        if rejected_reasons:
            details += "; circular constructor candidate(s): " + " | ".join(rejected_reasons[:3])
        elif conditional_reasons:
            details += "; constructor candidate(s) require exact source antecedents: " + " | ".join(
                conditional_reasons[:3]
            )
            projection_error = dependency_checked_projection_error(item)
            if projection_error:
                details += "; " + projection_error
        elif kind == "record_conclusion_input" and item.get("valid_constructors"):
            builders = ", ".join(
                str(candidate.get("declaration") or "unnamed builder")
                for candidate in item.get("valid_constructors") or []
                if isinstance(candidate, dict)
            )
            details += (
                "; fresh-record builder candidate(s) "
                + (builders or "were found")
                + " do not identify the caller-supplied record"
            )
        else:
            details += "; no paper-local constructor returning the proposition/record was found"
        findings.append(
            Finding(
                severity,
                folder / "PaperInterface.lean",
                f"`{paper_id}` has an unresolved conclusion-bearing theorem input: {details}. "
                "Derive it from paper source primitives or classify each true antecedent with an "
                "exact source locator; a renamed premise, alias, or record repackaging does not "
                "discharge the mathematical obligation.",
            )
        )

    for item in (() if strict_v11_occurrence_closeout else conclusion_dependencies):
        rejected_names = {
            str(candidate.get("declaration") or "").strip()
            for candidate in item.get("rejected_constructors") or []
            if isinstance(candidate, dict) and str(candidate.get("declaration") or "").strip()
        }
        if not rejected_names:
            continue
        keys = {
            str(item.get("judgment_key") or "").strip(),
            *{
                str(field.get("judgment_key") or "").strip()
                for field in item.get("conclusion_fields") or []
                if isinstance(field, dict)
            },
        } - {""}
        for key in sorted(keys & set(judgments)):
            judgment = judgments[key]
            if str(judgment.get("classification") or "").strip() != "proved_from_primitives":
                continue
            derivation = _source_record_lean_derivation(judgment)
            cited_rejected = sorted(
                name
                for name in rejected_names
                if re.search(rf"\b{re.escape(name)}\b", derivation)
            )
            if cited_rejected:
                findings.append(
                    Finding(
                        severity,
                        judgment_file,
                        f"`{paper_id}` source-record judgment `{key}` cites circular constructor "
                        f"{', '.join(cited_rejected)} as `proved_from_primitives`; the constructor "
                        "accepts the same conclusion/record fields and only repackages them.",
                    )
                )
    # A strict root can discharge its generated direct-evidence semantic row
    # without duplicating the same source-to-Spec audit in a sidecar.  The
    # selector is runtime-only and checks the exact source scope, current Lean
    # receipt, parent association, and atom route; it is not a source-kind or
    # declaration-name exception. Formula/model rows outside that selector
    # retain the ordinary semantic-model journal requirement.
    strict_parent_semantic_keys: frozenset[str] = frozenset()
    strict_component_source_judgment_keys: frozenset[str] = frozenset()
    if v11_direct_current:
        # The current v11 ledger reviewed every selected expanded Spec and its
        # paper-local and reusable-library prerequisites.  All generated v10
        # component/model keys are therefore compatibility metadata, not a
        # second semantic-review obligation.  Static source/Spec receipts and
        # Lean realization contracts are still validated independently by the
        # current closeout transaction.
        strict_parent_semantic_keys = expected_semantic_model_keys
        strict_component_source_judgment_keys = expected_keys
    elif strict_v11_occurrence_closeout and not target_disposition_rebind_error:
        try:
            strict_coverage = current_strict_v11_full_spec_source_record_coverage(
                paper_id,
                folder,
                payload,
                run_context=run_context,
            )
            strict_parent_semantic_keys = (
                strict_coverage.semantic_model_judgment_keys
                & expected_semantic_model_keys
            )
            strict_component_source_judgment_keys = (
                strict_coverage.component_judgment_keys & expected_keys
            )
        except Exception:
            # This is a narrow alternate receipt lane.  Any unavailable
            # projector leaves the ordinary journal requirement intact.
            strict_parent_semantic_keys = frozenset()
            strict_component_source_judgment_keys = frozenset()

    required_semantic_model_keys = (
        expected_semantic_model_keys - strict_parent_semantic_keys
    )
    required_expected_keys = expected_keys - strict_component_source_judgment_keys
    required_judgment_keys = required_expected_keys | required_semantic_model_keys
    if not judgments and required_judgment_keys:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge has {input_count} boundary input(s) and "
                f"{field_count} field(s) plus {len(required_semantic_model_keys)} semantic-model "
                "comparison item(s) requiring LLM provenance judgments, "
                f"but `{repo_display_path(judgment_file)}` is missing or invalid.",
            )
        )
        return findings

    field_items = {
        str(item.get("judgment_key") or "").strip(): item
        for item in payload.get("recursive_field_items") or []
        if isinstance(item, dict) and str(item.get("judgment_key") or "").strip()
    }
    nested_children: dict[str, set[str]] = {}
    for key, item in field_items.items():
        children: set[str] = set()
        for nested_name in item.get("nested_structures") or []:
            nested = str(nested_name).strip()
            if not nested:
                continue
            children.update(
                child_key for child_key, child in field_items.items()
                if str(child.get("structure") or "").strip() == nested
            )
        nested_children[key] = children

    semantic_items_requiring_journal = [
        item
        for item in semantic_model_items
        if str(item.get("judgment_key") or "").strip()
        not in strict_parent_semantic_keys
    ]
    findings.extend(
        semantic_model_review_findings(
            paper_id,
            folder,
            judgment_file,
            semantic_items_requiring_journal,
            judgments,
            digest=digest,
            expected_item_digests=expected_item_digests,
            expected_item_digest_pins=expected_item_digest_pins,
            severity=severity,
            target_disposition_statement_map=target_disposition_statement_map,
            target_disposition_source_proof_fidelity=(
                target_disposition_source_proof_fidelity
            ),
            target_disposition_validated_vocabulary_binding_source_item_ids=(
                payload.get(
                    "source_coverage_validated_vocabulary_binding_source_items"
                )
            ),
            target_disposition_validated_vocabulary_direct_route_source_item_ids=(
                payload.get(
                    "source_coverage_validated_vocabulary_direct_route_source_items"
                )
            ),
            target_disposition_administrative_projection_rebind=(
                target_disposition_administrative_projection_rebind
            ),
            enforce_target_disposition=enforce_target_disposition,
        )
    )

    missing = sorted(required_expected_keys - set(judgments))
    # A current v11 direct source-to-expanded-Spec review owns the complete
    # semantic disposition surface.  Unselected v10 rows are historical input
    # data only: they cannot grant current credit and therefore are neither an
    # error nor an operator-facing closeout warning.  The legacy lane retains
    # its exact extra-row diagnostic whenever v11 is unavailable or stale.
    extra = (
        []
        if v11_direct_current
        else sorted(set(judgments) - allowed_judgment_keys)
    )
    unresolved = (
        []
        if strict_v11_occurrence_closeout
        else sorted(
            key
            for key, item in judgments.items()
            if key in required_expected_keys
            and str(item.get("classification") or "").strip()
            not in APPROVED_SOURCE_RECORD_CLASSIFICATIONS
        )
    )
    optional_strict_receipt_keys = (
        strict_parent_semantic_keys | strict_component_source_judgment_keys
    )
    stale_prompt = sorted(
        key
        for key, item in judgments.items()
        if key in (allowed_judgment_keys - optional_strict_receipt_keys)
        and item.get("prompt_version_stale")
    )
    missing_metadata = sorted(
        key
        for key, item in judgments.items()
        if key in (allowed_judgment_keys - optional_strict_receipt_keys)
        and item.get("metadata_missing")
    )
    stale_judgment_digest = sorted(
        key
        for key, item in judgments.items()
        if key in (allowed_judgment_keys - optional_strict_receipt_keys)
        and digest
        and not source_record_judgment_current(
            key,
            item,
            digest=digest,
            expected_item_digests=expected_item_digests,
            expected_item_digest_pins=expected_item_digest_pins,
        )
    )
    invalid_context: list[str] = []
    if enforce_target_disposition and not strict_v11_occurrence_closeout:
        for key, source_items in sorted(source_input_items_by_key.items()):
            if key not in expected_input_keys:
                continue
            judgment = judgments.get(key)
            if not isinstance(judgment, dict):
                continue
            for source_item in source_items:
                for error in source_input_target_disposition_errors(
                    source_item,
                    judgment,
                    statement_map=target_disposition_statement_map,
                    source_proof_fidelity=target_disposition_source_proof_fidelity,
                    status=status,
                    administrative_projection_rebind=(
                        target_disposition_administrative_projection_rebind
                    ),
                    configured_assumption_formalization_regularity_context=(
                        target_disposition_formalization_regularity_context
                    ),
                ):
                    invalid_context.append(
                        f"{key} has invalid source input target disposition: {error}"
                    )
    for key in (
        ()
        if strict_v11_occurrence_closeout
        else sorted((expected_keys - expected_input_keys) & set(judgments))
    ):
        classification = str(judgments[key].get("classification") or "").strip()
        field_item = field_items.get(key, {})
        if enforce_target_disposition:
            for error in recursive_field_target_disposition_errors(
                field_item,
                judgments[key],
                statement_map=target_disposition_statement_map,
                source_proof_fidelity=target_disposition_source_proof_fidelity,
                administrative_projection_rebind=(
                    target_disposition_administrative_projection_rebind
                ),
            ):
                invalid_context.append(
                    f"{key} has invalid recursive-field source target disposition: {error}"
                )
        nested = [str(name).strip() for name in field_item.get("nested_structures") or [] if str(name).strip()]
        if (
            classification == "approved_external_boundary"
            and status in {"formalized", "formalized with caveat"}
        ):
            invalid_context.append(
                f"{key} classified `approved_external_boundary` but paper status is `{status}`"
            )
        fieldless_nested_data = (
            classification == "nonpropositional_witness_data"
            and not nested_children.get(key, set())
        )
        if nested and not fieldless_nested_data and classification not in {
            "container_recursively_audited",
            "approved_external_boundary",
            "derived_consequence_record",
        }:
            invalid_context.append(
                f"{key} classified `{classification or 'missing'}` but points to nested source record(s) "
                + ", ".join(nested)
            )
        if classification == "container_recursively_audited":
            children = nested_children.get(key, set())
            if not nested or not children:
                invalid_context.append(
                    f"{key} classified `container_recursively_audited` but no nested audited field judgments were found"
                )
                continue
            bad_children = sorted(
                child
                for child in children
                if child not in judgments
                or not str(
                    judgments[child].get("classification") or ""
                ).strip()
            )
            if bad_children:
                invalid_context.append(
                    f"{key} classified `container_recursively_audited` but nested field(s) are missing: "
                    + ", ".join(bad_children[:5])
                    + ("; ..." if len(bad_children) > 5 else "")
                )
        if (
            classification in VISIBLE_BOUNDARY_SOURCE_RECORD_CLASSIFICATIONS
            and not _source_record_lean_derivation(judgments[key])
        ):
            invalid_context.append(
                f"{key} classified `{classification}` but gives no visible boundary projection/derivation"
            )
    for key in (
        ()
        if strict_v11_occurrence_closeout
        else sorted(expected_input_keys & set(judgments))
    ):
        classification = str(judgments[key].get("classification") or "").strip()
        source_location = str(
            judgments[key].get("source_location")
            or judgments[key].get("source_evidence")
            or judgments[key].get("source_key")
            or judgments[key].get("paper_statement_key")
            or ""
        ).strip()
        lean_derivation = str(
            judgments[key].get("lean_derivation")
            or judgments[key].get("constructor")
            or judgments[key].get("derived_from")
            or judgments[key].get("derivation")
            or ""
        ).strip()
        if classification in {"container_recursively_audited", "nonpropositional_witness_data"}:
            invalid_context.append(
                f"{key} classified `{classification}` but boundary-shaped theorem inputs need "
                "source evidence, a Lean derivation, approved external-boundary status, or unresolved status"
            )
        if classification in VISIBLE_BOUNDARY_SOURCE_RECORD_CLASSIFICATIONS:
            invalid_context.append(
                f"{key} classified `{classification}` but theorem-boundary inputs are the visible "
                "proof debt; use this classification only for recursive fields unpacked from them"
            )
        if classification == "validated_source_assumption" and not source_location:
            invalid_context.append(
                f"{key} classified `validated_source_assumption` but gives no source key/location/evidence"
            )
        if classification == "proved_from_primitives" and not lean_derivation:
            invalid_context.append(
                f"{key} classified `proved_from_primitives` but gives no Lean constructor/derivation"
            )
        if (
            classification == "approved_external_boundary"
            and status in {"formalized", "formalized with caveat"}
        ):
            invalid_context.append(
                f"{key} classified `approved_external_boundary` but paper status is `{status}`"
            )
    for item in (() if strict_v11_occurrence_closeout else conclusion_dependencies):
        if not item.get("conditional_constructors"):
            continue
        key = str(item.get("judgment_key") or "").strip()
        judgment = judgments.get(key)
        if source_record_classification(judgment) != "proved_from_primitives":
            continue
        projection_error = dependency_checked_projection_error(item)
        if projection_error:
            invalid_context.append(
                f"{key} classified `proved_from_primitives` but its checked_projection is invalid: "
                + projection_error
            )
    if missing:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge is missing {len(missing)} boundary/source-record judgment(s): "
                + ", ".join(missing[:8])
                + ("; ..." if len(missing) > 8 else ""),
            )
        )
    if extra:
        findings.append(
            Finding(
                "WARN",
                judgment_file,
                f"`{paper_id}` source-record judge has {len(extra)} stale/extra boundary/source-record judgment(s): "
                + ", ".join(extra[:8])
                + ("; ..." if len(extra) > 8 else ""),
            )
        )
    if unresolved:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge marks {len(unresolved)} boundary/source-record item(s) as unresolved or unapproved: "
                + ", ".join(unresolved[:8])
                + ("; ..." if len(unresolved) > 8 else ""),
            )
        )
    if stale_prompt:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge uses stale or missing prompt version for "
                f"{len(stale_prompt)} item(s): "
                + ", ".join(stale_prompt[:8])
                + ("; ..." if len(stale_prompt) > 8 else ""),
            )
        )
    if missing_metadata:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge lacks validator/timestamp success metadata for "
                f"{len(missing_metadata)} item(s): "
                + ", ".join(missing_metadata[:8])
                + ("; ..." if len(missing_metadata) > 8 else ""),
            )
        )
    if stale_judgment_digest:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge has {len(stale_judgment_digest)} item(s) "
                "not tied to the current source_record_audit_sha256: "
                + ", ".join(stale_judgment_digest[:8])
                + ("; ..." if len(stale_judgment_digest) > 8 else ""),
            )
        )
    if invalid_context:
        findings.append(
            Finding(
                severity,
                judgment_file,
                f"`{paper_id}` source-record judge has {len(invalid_context)} context-invalid classification(s): "
                + "; ".join(invalid_context[:5])
                + ("; ..." if len(invalid_context) > 5 else ""),
            )
        )
    if (
        paper_closeout
        and strict_v11_occurrence_closeout
        and (
            strict_parent_semantic_keys
            or strict_component_source_judgment_keys
        )
        and run_context is not None
        and not any(finding.severity == "ERROR" for finding in findings)
    ):
        # This only stages a runtime capability. The consolidated owner waits
        # until the whole primary paper gate is error-free before exposing it
        # to deferred evidence integrity.
        run_context.stage_strict_v11_source_record_judgment_handoff()
    return findings


def _source_record_source_location(judgment: dict[str, object]) -> str:
    return str(
        judgment.get("source_location")
        or judgment.get("source_evidence")
        or judgment.get("source_key")
        or judgment.get("paper_statement_key")
        or ""
    ).strip()


def _source_record_lean_derivation(judgment: dict[str, object]) -> str:
    return str(
        judgment.get("lean_derivation")
        or judgment.get("constructor")
        or judgment.get("derived_from")
        or judgment.get("derivation")
        or ""
    ).strip()


def _source_record_formalized_note_boundary(judgment: dict[str, object]) -> bool:
    return bool(judgment.get("formalized_note_boundary")) or str(
        judgment.get("status_impact") or ""
    ).strip() == "formalized_note"


def _source_record_boundary_input_is_validated(
    judgment: dict[str, object],
    *,
    key: str,
    digest: str,
    expected_item_digests: dict[str, str],
    expected_item_digest_pins: dict[str, frozenset[tuple[str, int, str]]] | None,
    status: object,
) -> bool:
    """Return true only for current source-record judgments that route theorem inputs.

    Source-record inputs are an alternate explicit provenance lane for visible
    source-model/source-row premises.  This should not weaken the hidden-premise
    audit: missing metadata, stale prompts, unresolved judgments, partial
    external boundaries in completed papers, or missing source/derivation
    evidence all fail closed here and remain hidden-premise findings.
    """

    classification = str(judgment.get("classification") or "").strip()
    # This lane records an audited Lean representation regularity.  It may
    # resolve its own raw review item, but must never be projected into the
    # source/model theorem-premise set used by hidden-premise or provenance
    # checks.
    if classification == FORMALIZATION_REGULARITY_CLASSIFICATION:
        return False
    if classification not in APPROVED_SOURCE_RECORD_CLASSIFICATIONS:
        return False
    if judgment.get("prompt_version_stale") or judgment.get("metadata_missing"):
        return False
    if not source_record_judgment_current(
        key,
        judgment,
        digest=digest,
        expected_item_digests=expected_item_digests,
        expected_item_digest_pins=expected_item_digest_pins,
    ):
        return False
    if classification in {"container_recursively_audited", "nonpropositional_witness_data"}:
        return False
    if classification in VISIBLE_BOUNDARY_SOURCE_RECORD_CLASSIFICATIONS:
        return False
    if (
        classification == "approved_external_boundary"
        and status in {"formalized", "formalized with caveat"}
    ):
        return False
    if classification == "validated_source_assumption" and not _source_record_source_location(judgment):
        return False
    if classification == "proved_from_primitives" and not _source_record_lean_derivation(judgment):
        return False
    return True


def source_record_validated_boundary_premises(
    paper_id: str,
    folder: Path,
    review_surface: dict[str, object],
    status: object,
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> set[str]:
    """Return visible theorem premises routed through current source-record judgments."""

    audit_file = source_record_audit_file_path(folder, review_surface)
    saved_audit = (
        run_context.saved_source_record_audit(audit_file)
        if run_context is not None
        else load_json_object(audit_file)
    )
    if not saved_audit:
        return set()
    digest = str(saved_audit.get("source_record_audit_sha256") or "").strip()
    if str(saved_audit.get("prompt_version") or "").strip() != REQUIRED_SOURCE_RECORD_PROMPT_VERSION:
        return set()
    (
        semantic_contract_revalidation,
        semantic_contract_revalidation_error,
    ) = source_record_semantic_contract_revalidation_for_payload(
        folder,
        saved_audit,
        run_context=run_context,
    )
    if semantic_contract_revalidation_error or source_record_effective_semantic_surface_error(
        saved_audit,
        semantic_contract_revalidation=semantic_contract_revalidation,
    ):
        return set()
    effective_input_keys = source_record_required_input_judgment_keys(
        saved_audit,
        semantic_contract_revalidation=semantic_contract_revalidation,
    )

    judgment_file = source_record_judgment_file_path(folder, review_surface)
    judgments = (
        run_context.source_record_judgments(judgment_file, saved_audit)
        if run_context is not None
        else source_record_judgment_items(
            judgment_file,
            paper_id,
            current_raw_audit=saved_audit,
            paper_dir=folder,
        )
    )
    if not judgments:
        return set()
    expected_item_digests = source_record_expected_item_digests(saved_audit)
    expected_item_digest_pins = source_record_expected_item_digest_pins(saved_audit)
    (
        target_disposition_statement_map,
        target_disposition_source_proof_fidelity,
    ) = source_record_target_disposition_context(
        folder,
        review_surface,
        run_context=run_context,
    )
    target_disposition_rebind, rebind_error = (
        source_record_target_disposition_rebind_context(
            folder,
            review_surface,
            saved_audit,
            run_context=run_context,
        )
    )
    if rebind_error:
        return set()
    if run_context is not None and saved_audit is _legacy_source_record_audit_payload(
        run_context.evidence_context
    ):
        legacy_state = _legacy_source_record_state(run_context.evidence_context)
        regularity_context = getattr(
            legacy_state,
            "configured_assumption_regularity_context",
            None,
        )
    else:
        regularity_context, _regularity_context_error = (
            load_configured_assumption_formalization_regularity_context(
                folder,
                saved_audit,
                status_payload=(
                    run_context.exact_json_payload(folder / "status.json")
                    if run_context is not None
                    else load_json_object(folder / "status.json")
                ),
            )
        )
    source_input_items_by_key: dict[str, list[dict[str, object]]] = {}
    for raw_item in (
        list(saved_audit.get("theorem_facing_input_items") or [])
        + list(saved_audit.get("boundary_input_items") or [])
        + list(saved_audit.get("conclusion_dependency_items") or [])
        + list(saved_audit.get("type_valued_certificate_result_items") or [])
    ):
        if not isinstance(raw_item, dict):
            continue
        item_key = str(raw_item.get("judgment_key") or "").strip()
        if item_key:
            source_input_items_by_key.setdefault(item_key, []).append(raw_item)

    def current_input_target_disposition_is_valid(
        key: str, judgment: dict[str, object]
    ) -> bool:
        return not any(
            source_input_target_disposition_errors(
                item,
                judgment,
                statement_map=target_disposition_statement_map,
                source_proof_fidelity=target_disposition_source_proof_fidelity,
                status=status,
                administrative_projection_rebind=target_disposition_rebind,
                configured_assumption_formalization_regularity_context=(
                    regularity_context
                ),
            )
            for item in source_input_items_by_key.get(key, [])
        )

    source_antecedent_eligible_keys = effective_input_keys | {
        str(key).strip()
        for key in saved_audit.get("expected_field_judgment_keys") or []
        if str(key).strip()
    }
    exact_source_antecedent_keys = {
        key
        for key, judgment in judgments.items()
        if key in source_antecedent_eligible_keys
        if source_record_classification(judgment) == "validated_source_assumption"
        and not judgment.get("prompt_version_stale")
        and not judgment.get("metadata_missing")
        and source_record_judgment_current(
            key,
            judgment,
            digest=digest,
            expected_item_digests=expected_item_digests,
            expected_item_digest_pins=expected_item_digest_pins,
        )
        and current_input_target_disposition_is_valid(key, judgment)
        and bool(SOURCE_RECORD_EXACT_LOCATOR_RE.search(_source_record_source_location(judgment)))
    }
    conclusion_dependencies_by_key = {
        str(item.get("judgment_key") or "").strip(): item
        for item in saved_audit.get("conclusion_dependency_items") or []
        if isinstance(item, dict) and str(item.get("judgment_key") or "").strip()
    }

    routed: set[str] = set()
    raw_theorem_facing_items = saved_audit.get("theorem_facing_input_items")
    input_surface = (
        raw_theorem_facing_items
        if isinstance(raw_theorem_facing_items, list)
        else saved_audit.get("boundary_input_items") or []
    )
    for raw_item in input_surface:
        if not isinstance(raw_item, dict):
            continue
        key = str(raw_item.get("judgment_key") or "").strip()
        if not key or key not in effective_input_keys:
            continue
        judgment = judgments.get(key)
        if not isinstance(judgment, dict):
            continue
        if not current_input_target_disposition_is_valid(key, judgment):
            continue
        dependency = conclusion_dependencies_by_key.get(key)
        if (
            isinstance(dependency, dict)
            and dependency.get("conditional_constructors")
            and source_record_classification(judgment) == "proved_from_primitives"
            and not checked_projection_result(
                dependency,
                judgment,
                exact_source_antecedent_keys,
            ).accepted
        ):
            continue
        if not _source_record_boundary_input_is_validated(
            judgment,
            key=key,
            digest=digest,
            expected_item_digests=expected_item_digests,
            expected_item_digest_pins=expected_item_digest_pins,
            status=status,
        ):
            continue
        raw_input = raw_item.get("input")
        if not isinstance(raw_input, dict):
            continue
        names = str(raw_input.get("names") or "").strip()
        type_text = str(raw_input.get("type") or "").strip()
        if names and type_text:
            routed.add(normalize_premise_text(f"{names} : {type_text}"))
            routed.add(premise_type_text(f"{names} : {type_text}"))
    return routed


# These are the only field classifications that can close a record-valued
# paper-interface binder.  In particular, a visible-boundary projection,
# partial/external status, or unresolved label cannot turn a record package
# into a source-model premise.  Raw non-Prop witness data and recursively
# audited containers are allowed only after their entire generated field closure
# has been checked below.
COMPLETE_SOURCE_RECORD_MODEL_FIELD_CLASSIFICATIONS = frozenset(
    {
        "validated_source_assumption",
        "approved_source_convention",
        "approved_corrected_condition",
        "proved_from_primitives",
        "nonpropositional_witness_data",
        "container_recursively_audited",
        "derived_consequence_record",
    }
)
COMPLETE_SOURCE_RECORD_MODEL_PROPOSITION_FIELD_CLASSIFICATIONS = frozenset(
    {
        "validated_source_assumption",
        "approved_source_convention",
        "approved_corrected_condition",
        "proved_from_primitives",
    }
)

_FIELD_PAYLOAD_SAFETY_VALUES = frozenset(
    {
        "structural_data",
        "proof_payload",
        "requires_source_or_lean_closure",
        "requires_semantic_route",
        "unknown",
    }
)
_FIELD_PROOF_GRADE_CLASSIFICATIONS = (
    COMPLETE_SOURCE_RECORD_MODEL_PROPOSITION_FIELD_CLASSIFICATIONS
)
_FIELD_RAW_DATA_CLASSIFICATIONS = frozenset(
    {
        "nonpropositional_witness_data",
        "container_recursively_audited",
        "derived_consequence_record",
    }
)


def _sha256_hex(value: object) -> bool:
    text = str(value or "").strip().lower()
    return len(text) == 64 and all(character in "0123456789abcdef" for character in text)


def _source_record_field_payload_receipt(
    field_item: Mapping[str, object],
) -> tuple[str, str] | None:
    """Validate one generated Lean-owned field-safety receipt.

    The source parser may retain field spelling for navigation, but neither a
    field label nor `proposition_sort: false` grants raw-data credit.  This
    checks the exact constructor/projection locator, its content-bound identity
    and the elaborated Lean receipt before either record-closure path uses the
    item.  It intentionally accepts no hand-written fallback representation.
    """

    raw_locator = field_item.get("elaborated_field_safety_locator")
    raw_receipt = field_item.get("elaborated_field_safety_receipt")
    if not isinstance(raw_locator, Mapping) or not isinstance(raw_receipt, Mapping):
        return None
    locator = canonical_recursive_field_safety_locator(raw_locator)
    if locator is None or dict(locator) != dict(raw_locator):
        return None
    identity = str(locator.get("field_identity_sha256") or "").strip().lower()
    if (
        not schema_version_is_exact(
            raw_receipt.get("schema"), RECURSIVE_FIELD_SAFETY_RECEIPT_SCHEMA
        )
        or str(raw_receipt.get("field_identity_sha256") or "").strip().lower()
        != identity
        or not _sha256_hex(raw_receipt.get("normalized_type_sha256"))
        or str(raw_receipt.get("foundation_allowlist_sha256") or "").strip().lower()
        != FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_SHA256
        or str(raw_receipt.get("foundation_allowlist_version") or "").strip()
        != FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_VERSION
    ):
        return None
    value_sort = str(raw_receipt.get("value_sort") or "").strip()
    payload_safety = str(raw_receipt.get("payload_safety") or "").strip()
    if (
        value_sort not in {"true", "false"}
        or payload_safety not in _FIELD_PAYLOAD_SAFETY_VALUES
        or str(raw_receipt.get("status") or "").strip() != "ok"
        or not str(raw_receipt.get("route") or "").strip()
        or not isinstance(raw_receipt.get("reason_codes"), list)
        or any(
            not isinstance(code, str) or not code.strip()
            for code in raw_receipt.get("reason_codes") or []
        )
        or str(field_item.get("proposition_sort") or "").strip() != value_sort
        or str(field_item.get("payload_safety") or "").strip() != payload_safety
    ):
        return None
    if value_sort == "true":
        if payload_safety != "proof_payload":
            return None
    elif payload_safety == "proof_payload":
        return None
    foundation_head = str(raw_receipt.get("foundation_head") or "").strip()
    foundation_module = str(raw_receipt.get("foundation_module") or "").strip()
    if payload_safety == "structural_data":
        if FOUNDATION_STRUCTURAL_DATA_MODULE_BY_HEAD.get(foundation_head) != foundation_module:
            return None
    elif foundation_head or foundation_module:
        return None
    return value_sort, payload_safety


def _source_record_field_allows_fieldless_data(
    field_item: Mapping[str, object],
) -> bool:
    """Allow a fieldless nested carrier only for trusted structural data."""

    return _source_record_field_payload_receipt(field_item) == (
        "false",
        "structural_data",
    )


def _generated_item_qualified_declaration(item: dict[str, object]) -> str:
    """Return a generator-pinned declaration identity, never a short row name."""

    identity = item.get("reviewed_declaration_identity")
    if isinstance(identity, dict):
        qualified = str(identity.get("qualified_declaration") or "").strip()
        if is_fully_qualified_lean_identity(qualified):
            return qualified
    qualified = str(item.get("qualified_declaration") or "").strip()
    return qualified if is_fully_qualified_lean_identity(qualified) else ""


def _generated_dependency_binder_names(item: dict[str, object]) -> frozenset[str]:
    """Return the exact Lean binder group recorded for one generated dependency.

    The source-record producer records the source spelling for a whole Lean
    binder group (for example, ``S S'``), while semantic-model bindings retain
    the resolved individual names. Match those two representations as one
    group. This uses only generator-produced binder syntax or an explicit
    generator-produced ``binder_names`` list; it is not a declaration-name
    heuristic.
    """

    raw_names = item.get("binder_names")
    if raw_names is not None:
        if not isinstance(raw_names, list):
            return frozenset()
        names = [str(name).strip() for name in raw_names if str(name).strip()]
        return frozenset(names) if len(names) == len(set(names)) else frozenset()
    return frozenset(_binder_names(str(item.get("binder") or "")))


def _source_record_recursive_field_closure(
    field_items: dict[str, dict[str, object]],
    root: str,
    *,
    fieldless_nested_data_keys: frozenset[str] = frozenset(),
) -> set[str] | None:
    """Return every generated field reachable from one exact record root.

    The scan follows the generator's ``nested_structures`` relation, rather
    than a structure-name suffix or source-looking field label.  An unknown
    nested root or a cycle fails closed because it would leave part of the
    source-model carrier unaudited. The sole exception is an explicitly
    audited non-propositional field whose generated nested structure has no
    generated fields. That represents fieldless data such as a finite enum,
    not a hidden source proposition; callers must supply the exact field keys
    for this exception.
    """

    by_structure: dict[str, set[str]] = {}
    for key, item in field_items.items():
        structure = str(item.get("structure") or "").strip()
        if structure:
            by_structure.setdefault(structure, set()).add(key)

    seen_structures: set[str] = set()
    visiting: set[str] = set()
    closure: set[str] = set()

    def visit(structure: str) -> bool:
        if structure in visiting:
            return False
        if structure in seen_structures:
            return True
        keys = by_structure.get(structure)
        if not keys:
            return False
        visiting.add(structure)
        for key in keys:
            closure.add(key)
            nested = field_items[key].get("nested_structures") or []
            if not isinstance(nested, list):
                return False
            for raw_nested in nested:
                nested_structure = str(raw_nested or "").strip()
                if not nested_structure:
                    return False
                if nested_structure not in by_structure:
                    if (
                        key not in fieldless_nested_data_keys
                        or not _source_record_field_allows_fieldless_data(
                            field_items[key]
                        )
                    ):
                        return False
                    continue
                if not visit(nested_structure):
                    return False
        visiting.remove(structure)
        seen_structures.add(structure)
        return True

    return closure if visit(root) else None


def _source_record_model_field_is_current(
    key: str,
    judgment: dict[str, object],
    *,
    field_item: Mapping[str, object],
    digest: str,
    expected_item_digests: dict[str, str],
    expected_item_digest_pins: dict[str, frozenset[tuple[str, int, str]]] | None,
    proposition_field: bool,
) -> bool:
    """Validate one recursive field for a complete source-model record.

    This is the final data-credit boundary for both ordinary caller records
    and atom-pinned operational model roots.  The Lean receipt decides whether
    a field is a proof payload, trusted structural data, a wrapper requiring a
    closure, or a predicate needing a semantic route.  A raw non-Proposition
    classification cannot override that receipt.
    """

    classification = source_record_classification(judgment)
    if classification not in COMPLETE_SOURCE_RECORD_MODEL_FIELD_CLASSIFICATIONS:
        return False
    payload_receipt = _source_record_field_payload_receipt(field_item)
    if payload_receipt is None:
        return False
    value_sort, payload_safety = payload_receipt
    if (
        proposition_field
        and value_sort != "true"
    ):
        return False
    if value_sort == "true":
        if classification not in _FIELD_PROOF_GRADE_CLASSIFICATIONS:
            return False
    elif payload_safety == "structural_data":
        # Structural data may retain the ordinary raw-data/container routes.
        pass
    elif payload_safety == "requires_source_or_lean_closure":
        # A local/imported wrapper can only be admitted through direct
        # source/Lean evidence, or through an actual generated nested closure.
        # The latter is intentionally unavailable to fieldless data.
        nested = field_item.get("nested_structures")
        has_generated_nested_route = isinstance(nested, list) and any(
            str(child or "").strip() for child in nested
        )
        if classification in _FIELD_RAW_DATA_CLASSIFICATIONS and not (
            classification == "container_recursively_audited"
            and has_generated_nested_route
        ):
            return False
        if (
            classification not in _FIELD_PROOF_GRADE_CLASSIFICATIONS
            and classification != "container_recursively_audited"
        ):
            return False
    elif payload_safety == "requires_semantic_route":
        # Predicates/relations (`X -> Prop`) are not data containers.  Until
        # a dedicated semantic-route certificate is supplied, they must have
        # direct source or Lean evidence.
        if classification not in _FIELD_PROOF_GRADE_CLASSIFICATIONS:
            return False
    else:
        return False
    if judgment.get("prompt_version_stale") or judgment.get("metadata_missing"):
        return False
    if _source_record_formalized_note_boundary(judgment):
        return False
    if not source_record_judgment_current(
        key,
        judgment,
        digest=digest,
        expected_item_digests=expected_item_digests,
        expected_item_digest_pins=expected_item_digest_pins,
    ):
        return False
    if classification in {
        "validated_source_assumption",
        "approved_source_convention",
        "approved_corrected_condition",
    } and not SOURCE_RECORD_EXACT_LOCATOR_RE.search(
        _source_record_source_location(judgment)
    ):
        return False
    if classification == "proved_from_primitives" and not _source_record_lean_derivation(
        judgment
    ):
        return False
    return True


def _source_record_complete_model_record_bindings_uncached(
    paper_id: str,
    folder: Path,
    review_surface: dict[str, object],
    status: object,
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> dict[
    str,
    tuple[tuple[frozenset[str], str, frozenset[str]], ...],
]:
    """Return only fully audited record binders for the hidden-premise lane.

    A source-record audit can show that a caller-supplied record is a genuine
    model carrier rather than a package holding the theorem conclusion.  That
    is not established by its record or binder name.  This helper requires all
    of the following generated, current evidence before exposing one binding:

    * the v10 semantic row pins the exact reviewed declaration and an exact
      record root/binder binding;
    * one matching generated record-conclusion dependency has only
      source-antecedent-eligible fields with no result relation or rejected
      circular constructor;
    * every recursively reachable field from that root has a current approved
      source-record judgment, with proposition fields receiving source/Lean
      evidence rather than raw witness-data treatment; and
    * the owning semantic-model judgment passes the same current dimension and
      source-target-disposition validation as the ordinary source-record audit.

    ``check_source_record_audit`` may call it after confirming that its saved
    payload is the current helper snapshot; the later hidden-premise lane uses
    the same reader only after that audit has no errors.  Its own checks still
    bind every sidecar response to the saved aggregate or unambiguous item
    digest.
    """

    audit_file = source_record_audit_file_path(folder, review_surface)
    payload = (
        run_context.saved_source_record_audit(audit_file)
        if run_context is not None
        else load_json_object(audit_file)
    )
    if not payload:
        return {}
    if source_record_raw_integrity_error_if_current(payload):
        return {}
    if source_record_target_route_error(payload):
        return {}
    (
        semantic_contract_revalidation,
        semantic_contract_revalidation_error,
    ) = source_record_semantic_contract_revalidation_for_payload(
        folder,
        payload,
        run_context=run_context,
    )
    if semantic_contract_revalidation_error or source_record_effective_semantic_surface_error(
        payload,
        semantic_contract_revalidation=semantic_contract_revalidation,
    ):
        return {}
    digest = str(payload.get("source_record_audit_sha256") or "").strip()
    if (
        not digest
        or str(payload.get("prompt_version") or "").strip()
        != REQUIRED_SOURCE_RECORD_PROMPT_VERSION
    ):
        return {}
    judgment_file = source_record_judgment_file_path(folder, review_surface)
    judgments = (
        run_context.source_record_judgments(judgment_file, payload)
        if run_context is not None
        else source_record_judgment_items(
            judgment_file,
            paper_id,
            current_raw_audit=payload,
            paper_dir=folder,
        )
    )
    if not judgments:
        return {}
    expected_item_digests = source_record_expected_item_digests(payload)
    expected_item_digest_pins = source_record_expected_item_digest_pins(payload)
    statement_map, source_proof_fidelity = source_record_target_disposition_context(
        folder,
        review_surface,
        run_context=run_context,
    )
    target_disposition_rebind, rebind_error = (
        source_record_target_disposition_rebind_context(
            folder,
            review_surface,
            payload,
            run_context=run_context,
        )
    )
    if rebind_error:
        return {}

    field_items = {
        str(item.get("judgment_key") or "").strip(): item
        for item in payload.get("recursive_field_items") or []
        if isinstance(item, dict) and str(item.get("judgment_key") or "").strip()
    }
    structures_with_generated_fields = {
        str(item.get("structure") or "").strip()
        for item in field_items.values()
        if str(item.get("structure") or "").strip()
    }
    fieldless_nested_data_keys: set[str] = set()
    for key, item in field_items.items():
        nested = item.get("nested_structures")
        if not isinstance(nested, list):
            continue
        nested_structures = {
            str(raw_nested or "").strip()
            for raw_nested in nested
            if str(raw_nested or "").strip()
        }
        if (
            nested_structures
            and not nested_structures & structures_with_generated_fields
            and source_record_classification(judgments.get(key, {}))
            == "nonpropositional_witness_data"
            and _source_record_field_allows_fieldless_data(item)
        ):
            fieldless_nested_data_keys.add(key)
    expected_field_keys = {
        str(key).strip()
        for key in payload.get("expected_field_judgment_keys") or []
        if str(key).strip()
    }
    dependencies_by_declaration: dict[str, list[dict[str, object]]] = {}
    for raw_dependency in payload.get("conclusion_dependency_items") or []:
        if not isinstance(raw_dependency, dict):
            continue
        qualified = _generated_item_qualified_declaration(raw_dependency)
        if qualified:
            dependencies_by_declaration.setdefault(qualified, []).append(
                raw_dependency
            )

    bindings_by_declaration: dict[
        str, tuple[tuple[frozenset[str], str, frozenset[str]], ...]
    ] = {}
    for raw_semantic_item in payload.get("semantic_model_items") or []:
        if not isinstance(raw_semantic_item, dict):
            continue
        qualified = _generated_item_qualified_declaration(raw_semantic_item)
        semantic_key = str(raw_semantic_item.get("judgment_key") or "").strip()
        semantic_judgment = judgments.get(semantic_key)
        if not qualified or not semantic_key or not isinstance(semantic_judgment, dict):
            continue
        # Reuse the full semantic-model validator rather than treating a row
        # label or a bare semantic-review classification as sufficient.
        semantic_findings = semantic_model_review_findings(
            paper_id,
            folder,
            judgment_file,
            [raw_semantic_item],
            judgments,
            digest=digest,
            expected_item_digests=expected_item_digests,
            expected_item_digest_pins=expected_item_digest_pins,
            severity="ERROR",
            target_disposition_statement_map=statement_map,
            target_disposition_source_proof_fidelity=source_proof_fidelity,
            target_disposition_validated_vocabulary_binding_source_item_ids=(
                payload.get(
                    "source_coverage_validated_vocabulary_binding_source_items"
                )
            ),
            target_disposition_validated_vocabulary_direct_route_source_item_ids=(
                payload.get(
                    "source_coverage_validated_vocabulary_direct_route_source_items"
                )
            ),
            target_disposition_administrative_projection_rebind=(
                target_disposition_rebind
            ),
            enforce_target_disposition=True,
        )
        if semantic_findings:
            continue
        accepted: list[tuple[frozenset[str], str, frozenset[str]]] = []
        for raw_binding in raw_semantic_item.get("record_input_bindings") or []:
            if not isinstance(raw_binding, dict):
                continue
            binder_names = frozenset(
                str(name).strip()
                for name in raw_binding.get("binder_names") or []
                if str(name).strip()
            )
            roots = {
                str(root).strip()
                for root in raw_binding.get("record_roots") or []
                if str(root).strip()
            }
            if not binder_names or len(roots) != 1:
                continue
            root = next(iter(roots))
            if not is_fully_qualified_lean_identity(root):
                continue
            dependencies = [
                dependency
                for dependency in dependencies_by_declaration.get(qualified, [])
                if str(dependency.get("kind") or "").strip()
                == "record_conclusion_input"
                and str(dependency.get("record") or "").strip() == root
                and _generated_dependency_binder_names(dependency) == binder_names
            ]
            # Multiple generated dependencies would make this structural
            # projection ambiguous; do not select one by a shorter name.
            if len(dependencies) != 1:
                continue
            dependency = dependencies[0]
            if dependency.get("rejected_constructors"):
                continue
            conclusion_fields = dependency.get("conclusion_fields")
            if not isinstance(conclusion_fields, list) or not conclusion_fields:
                continue
            proposition_field_keys: set[str] = set()
            malformed_or_result_related = False
            for raw_field in conclusion_fields:
                if not isinstance(raw_field, dict):
                    malformed_or_result_related = True
                    break
                field_key = str(raw_field.get("judgment_key") or "").strip()
                if (
                    not field_key
                    or raw_field.get("source_antecedent_eligible") is not True
                    or str(raw_field.get("relation_to_row_result") or "").strip()
                ):
                    malformed_or_result_related = True
                    break
                semantic_kind = str(raw_field.get("semantic_kind") or "").strip()
                if semantic_kind not in {"proposition", "unknown_nondata"}:
                    malformed_or_result_related = True
                    break
                if semantic_kind == "proposition":
                    proposition_field_keys.add(field_key)
            if malformed_or_result_related:
                continue
            closure = _source_record_recursive_field_closure(
                field_items,
                root,
                fieldless_nested_data_keys=frozenset(fieldless_nested_data_keys),
            )
            if not closure or not closure.issubset(expected_field_keys):
                continue
            if not proposition_field_keys.issubset(closure):
                continue
            if any(
                not isinstance(judgments.get(field_key), dict)
                or not _source_record_model_field_is_current(
                    field_key,
                    judgments[field_key],
                    field_item=field_items[field_key],
                    digest=digest,
                    expected_item_digests=expected_item_digests,
                    expected_item_digest_pins=expected_item_digest_pins,
                    proposition_field=field_key in proposition_field_keys,
                )
                for field_key in closure
            ):
                continue
            # `record_aliases` comes from the generator's Lean resolution of
            # this exact dependency.  It permits a source declaration's local
            # spelling while rejecting a same-named record from another
            # namespace; no suffix/name heuristic is used here.
            aliases = frozenset(
                str(alias).strip()
                for alias in dependency.get("record_aliases") or []
                if str(alias).strip()
            )
            accepted.append((binder_names, root, aliases))
        if accepted:
            # Deduplicate while retaining a stable order for diagnostics/tests.
            bindings_by_declaration[qualified] = tuple(
                dict.fromkeys(accepted)
            )
    return bindings_by_declaration


def source_record_complete_model_record_bindings(
    paper_id: str,
    folder: Path,
    review_surface: dict[str, object],
    status: object,
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> dict[
    str,
    tuple[tuple[frozenset[str], str, frozenset[str]], ...],
]:
    """Return complete model bindings, reusing one exact closeout derivation."""

    if run_context is None:
        return _source_record_complete_model_record_bindings_uncached(
            paper_id,
            folder,
            review_surface,
            status,
        )
    surface_identity = hashlib.sha256(
        json.dumps(
            review_surface,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        ).encode("utf-8")
    ).hexdigest()
    value = run_context.cached_result(
        "complete_model_record_bindings",
        (surface_identity, str(status)),
        lambda: _source_record_complete_model_record_bindings_uncached(
            paper_id,
            folder,
            review_surface,
            status,
            run_context=run_context,
        ),
    )
    assert isinstance(value, dict)
    return value


def current_statement_conditional_boundary_rows(
    folder: Path,
    *,
    review_items_provider: Callable[[], tuple[Any, ...]] | None = None,
    run_context: PaperCloseoutRunContext | None = None,
) -> set[str]:
    """Return only v6 boundaries validated against current Lean manifests."""

    try:
        audit_inputs = (
            run_context.dashboard_audit_inputs()
            if run_context is not None and run_context.evidence_context is not None
            else None
        )
        from scripts.review_dashboard import (
            _is_conditional_boundary_judgment,
            load_llm_statement_judgments,
        )

        review_items = (
            review_items_provider()
            if review_items_provider is not None
            else strict_review_items_for_paper(
                folder,
                build_input_provider=(
                    run_context.build_input_provider
                    if run_context is not None
                    else None
                ),
                audit_inputs=audit_inputs,
            )
        )
        manifests = {
            item.name: item.lean_signature_manifest
            for item in review_items
            if isinstance(item.lean_signature_manifest, dict)
        }
        judgments = load_llm_statement_judgments(
            folder,
            manifests,
            audit_inputs=audit_inputs,
        )
    except Exception:  # noqa: BLE001 - missing Lean evidence fails closed.
        return set()
    return {
        name
        for name, judgment in judgments.items()
        if _is_conditional_boundary_judgment(judgment)
    }


def assumption_premises_from_text(
    source_text: str,
    declared_names: set[str] | None = None,
) -> dict[str, set[str]]:
    """Parse `-- audit-premise:` comments from caller-owned Lean text."""

    lines = source_text.splitlines()
    pending: list[str] = []
    block_depth = 0
    out: dict[str, set[str]] = {}
    structure = _legacy_review_surface_structure_module()
    for line in lines:
        premise_match = ASSUMPTION_AUDIT_PREMISE_RE.match(line)
        if premise_match:
            pending.append(normalize_premise_text(premise_match.group(1)))
            continue
        declaration_match = structure.REVIEW_DECL_KIND_RE.match(line)
        if not declaration_match:
            stripped = line.strip()
            if "/-" in line:
                block_depth += line.count("/-")
            if "-/" in line:
                block_depth = max(0, block_depth - line.count("-/"))
            if (
                pending
                and stripped
                and block_depth == 0
                and not line.lstrip().startswith(("--", "/--", "/-", "*", "-/"))
            ):
                pending = []
            continue
        name = declaration_match.group(2)
        is_declared_assumption = (
            name in declared_names
            if declared_names is not None
            else structure.is_assumption_decl_name(name)
        )
        if is_declared_assumption and pending:
            out.setdefault(name, set()).update(pending)
        pending = []
    return out


def normalize_assumption_judgment(raw: object) -> str:
    """Normalize source-assumption judge verdicts."""

    if isinstance(raw, bool):
        return "paper_assumption" if raw else "not_paper_assumption"
    value = str(raw or "").strip().lower()
    if value in {
        "paper_assumption",
        "paper assumption",
        "matches",
        "match",
        "yes",
        "true",
        "source_assumption",
        "source assumption",
        "model_assumption",
        "model assumption",
    }:
        return "paper_assumption"
    if value in {
        "source_text",
        "source text",
        "source_text_assumption",
        "source text assumption",
        "source_text_condition",
        "source text condition",
    }:
        return "source_text"
    if value in {
        "source_text_model_primitive",
        "source text model primitive",
        "source_model_primitive",
        "source model primitive",
        "model_primitive",
        "model primitive",
    }:
        return "source_text_model_primitive"
    if value in {
        "derived_from_source_primitives",
        "derived from source primitives",
        "derived_in_lean",
        "derived in lean",
        "derived",
    }:
        return "derived_from_source_primitives"
    if value in {
        "paper_condition",
        "paper condition",
        "source_condition",
        "source condition",
        "statement_condition",
        "statement condition",
        "theorem_condition",
        "theorem condition",
        "paper_statement_condition",
        "paper statement condition",
    }:
        return "paper_condition"
    if value in {
        "documented_additional_assumption",
        "documented additional assumption",
        "additional_assumption",
        "additional assumption",
        "human_approved_additional_assumption",
        "human approved additional assumption",
    }:
        return "documented_additional_assumption"
    if value in {
        "documented_caveat",
        "documented caveat",
        "paper_caveat",
        "paper caveat",
        "source_caveat",
        "source caveat",
        "repair_condition",
        "repair condition",
    }:
        return "documented_caveat"
    if value in {
        "partial_boundary",
        "partial boundary",
        "partial_formalization_boundary",
        "partial formalization boundary",
        "unresolved_boundary",
        "unresolved boundary",
        "needs_derivation",
        "needs derivation",
    }:
        return "partial_boundary"
    if value in {
        "not_paper_assumption",
        "not paper assumption",
        "proof_assumption",
        "proof assumption",
        "not_in_paper",
        "not in paper",
        "not_source_text",
        "not source text",
        "not_source",
        "not source",
        "mismatch",
        "no",
        "false",
    }:
        return "not_paper_assumption"
    if value in {"uncertain", "unknown", "unsure", "needs_review", "needs review", "partial"}:
        return "uncertain"
    return value


def normalize_premise_text(text: str) -> str:
    """Normalize a theorem-premise string for assumption-ledger matching."""

    return re.sub(r"\s+", " ", str(text or "").strip())


def premise_type_text(premise: str) -> str:
    """Return the normalized type side of a premise string.

    Lean pretty-prints unused proof arguments in expanded `#check` output as
    anonymous arrows (`SomeRows ... → ...`) rather than named binders.  The
    assumption ledger records the corresponding `-- audit-premise:` comments
    with human-readable names.  Matching on the type side lets the audit route
    those anonymous arrows through the same explicit source-assumption rows.
    """

    normalized = normalize_premise_text(premise)
    def dequalify(text: str) -> str:
        return re.sub(
            r"\b(?:[A-Za-z_][A-Za-z0-9_']*\.)+([A-Za-z_][A-Za-z0-9_']*)",
            r"\1",
            text,
        )

    if " : " in normalized:
        return dequalify(normalized.split(" : ", 1)[1].strip())
    if normalized.startswith("anonymous : "):
        return dequalify(normalized.split(" : ", 1)[1].strip())
    return dequalify(normalized)


def is_review_explicit_boundary_premise(premise: str) -> bool:
    """Return true when a premise's type head is a source/proof boundary.

    This intentionally looks at the type head rather than the full expression:
    ordinary source formulas can mention helper constants whose names contain
    `Certificate` without themselves being certificate assumptions.
    The head check is case-sensitive for suffixes such as `Table`; otherwise
    ordinary source predicates such as `stable` or `AllPairsAcceptable` are
    misclassified because they end in the letters "table".
    """

    type_text = premise_type_text(premise)
    head = type_text.strip().split(None, 1)[0].strip("(){}[]")
    short_head = head.rsplit(".", 1)[-1]
    boundary_suffixes = (
        "Certificate",
        "Oracle",
        "External",
        "Boundary",
        "Bridge",
        "SourceModel",
        "SourceFamilyRows",
        "SourceRows",
        "SourceTable",
        "Rows",
        "Table",
        "Package",
        "Window",
        "Windows",
        "Replay",
        "Process",
    )
    return short_head.endswith(boundary_suffixes) or re.search(
        r"\b(?:source[-_ ]?rows?|source[-_ ]?table|row[-_ ]?package)\b",
        type_text,
        re.I,
    ) is not None


def _premises_from_raw_value(raw_value: object) -> set[str]:
    """Extract exact theorem-premise strings from an assumption judgment item."""

    premises: set[str] = set()
    if not isinstance(raw_value, dict):
        return premises
    raw_premises = (
        raw_value.get("premises")
        or raw_value.get("lean_premises")
        or raw_value.get("audit_premises")
        or raw_value.get("theorem_premises")
    )
    if isinstance(raw_premises, str):
        raw_premises = [raw_premises]
    if isinstance(raw_premises, list):
        for premise in raw_premises:
            normalized = normalize_premise_text(str(premise))
            if normalized:
                premises.add(normalized)
    return premises


def _premise_judgments_from_raw_value(raw_value: object) -> dict[str, dict[str, object]]:
    """Extract per-premise source/provenance judgments from an assumption item."""

    if not isinstance(raw_value, dict):
        return {}
    raw_items = (
        raw_value.get("premise_judgments")
        or raw_value.get("premise_items")
        or raw_value.get("premise_validations")
        or raw_value.get("premises_judged")
    )
    out: dict[str, dict[str, object]] = {}

    def add_item(premise: object, raw_item: object) -> None:
        normalized_premise = normalize_premise_text(str(premise or ""))
        if not normalized_premise:
            return
        if isinstance(raw_item, dict):
            raw_judgment = (
                raw_item.get("judgment")
                or raw_item.get("verdict")
                or raw_item.get("status")
                or raw_item.get("source_text_judgment")
            )
            out[normalized_premise] = {
                "judgment": normalize_assumption_judgment(raw_judgment),
                "reason": str(
                    raw_item.get("reason")
                    or raw_item.get("notes")
                    or raw_item.get("explanation")
                    or ""
                ).strip(),
                "source_location": str(raw_item.get("source_location") or "").strip(),
            }
        else:
            out[normalized_premise] = {
                "judgment": normalize_assumption_judgment(raw_item),
                "reason": "",
                "source_location": "",
            }

    if isinstance(raw_items, dict):
        for premise, raw_item in raw_items.items():
            add_item(premise, raw_item)
    elif isinstance(raw_items, list):
        for raw_item in raw_items:
            if isinstance(raw_item, dict):
                add_item(raw_item.get("premise"), raw_item)
            else:
                add_item(raw_item, "uncertain")
    return out


def assumption_judgments_from_payload(
    payload: object,
    paper_id: str,
) -> dict[str, dict[str, object]]:
    """Parse paper-assumption judgments from caller-owned JSON data."""

    if not isinstance(payload, dict) or not schema_version_is_exact(
        payload.get("schema"), 1
    ):
        return {}
    if payload.get("paper") not in {None, paper_id}:
        return {}
    items = payload.get("items")
    if not isinstance(items, dict):
        return {}
    out: dict[str, dict[str, object]] = {}
    for raw_name, raw_value in items.items():
        name = str(raw_name).strip()
        if not name:
            continue
        if isinstance(raw_value, dict):
            raw_judgment = (
                raw_value.get("judgment")
                or raw_value.get("verdict")
                or raw_value.get("status")
                or raw_value.get("paper_assumption")
            )
            out[name] = {
                "judgment": normalize_assumption_judgment(raw_judgment),
                "reason": str(
                    raw_value.get("reason")
                    or raw_value.get("notes")
                    or raw_value.get("explanation")
                    or ""
                ).strip(),
                "premises": sorted(_premises_from_raw_value(raw_value)),
                "premise_judgments": _premise_judgments_from_raw_value(raw_value),
            }
        else:
            out[name] = {
                "judgment": normalize_assumption_judgment(raw_value),
                "reason": "",
                "premises": [],
                "premise_judgments": {},
            }
    return out



def load_expanded_review_statements(folder: Path) -> dict[str, tuple[str, int]]:
    """Load dashboard-expanded Lean statements keyed by review row name."""

    path = folder / REVIEW_TRACE_CACHE
    if not path.exists() or not path.is_file():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if not isinstance(payload, dict):
        return {}
    rows = payload.get("rows")
    if not isinstance(rows, list):
        return {}
    expanded: dict[str, tuple[str, int]] = {}
    for raw_row in rows:
        if not isinstance(raw_row, dict):
            continue
        name = str(raw_row.get("name") or "").strip()
        lean_statement = str(raw_row.get("lean_statement") or "").strip()
        if not name or not lean_statement:
            continue
        raw_line = raw_row.get("line_number")
        line_number = raw_line if isinstance(raw_line, int) else 0
        expanded[name] = (lean_statement, line_number)
    return expanded


def expanded_statement_boundary_premises(
    lean_statement: str, assumption_names: set[str]
) -> list[str]:
    """Return source-boundary binders visible only after Lean `#check` expansion."""

    hidden: list[str] = []
    for match in LEAN_BINDER_RE.finditer(lean_statement):
        names = _binder_names(match.group(1))
        type_text = match.group(2).strip()
        if not names:
            continue
        if any(name in assumption_names for name in names):
            continue
        if any(assumption in type_text for assumption in assumption_names):
            continue
        premise = normalize_premise_text(f"{' '.join(names)} : {type_text}")
        if is_review_explicit_boundary_premise(premise):
            hidden.append(premise)
    hidden.extend(expanded_statement_anonymous_boundary_premises(lean_statement))
    return list(dict.fromkeys(hidden))


def expanded_statement_anonymous_boundary_premises(lean_statement: str) -> list[str]:
    """Return anonymous top-level proof-boundary arrows in expanded output.

    Lean omits binder names for proof arguments that are not referenced in the
    theorem's result type, printing them as top-level arrows:

        SomeSourceRows ... → OtherRows ... → conclusion

    These are still theorem premises and must route through `Assumptions.lean`
    when they are source-row/certificate boundaries.
    """

    text = normalize_premise_text(lean_statement)
    pieces: list[str] = []
    current: list[str] = []
    depth = 0
    for char in text:
        if char in "([{⦃":
            depth += 1
        elif char in ")]}⦄" and depth > 0:
            depth -= 1
        if char == "→" and depth == 0:
            pieces.append("".join(current).strip())
            current = []
            continue
        current.append(char)
    hidden: list[str] = []
    for piece in pieces:
        candidate = piece.rsplit(",", 1)[-1].strip()
        if not candidate or " : " in candidate:
            continue
        if is_review_explicit_boundary_premise(candidate):
            hidden.append(normalize_premise_text(f"anonymous : {candidate}"))
    return hidden


def declaration_header(source: str) -> str:
    """Return the declaration signature before the proof/body."""

    marker = top_level_declaration_body_marker(source)
    head = source if marker is None else source[:marker]
    head = head.split(" where", 1)[0]
    return re.sub(r"\s+", " ", head).strip()


def declaration_explicit_binder_prefix(source: str) -> str:
    """Return only the caller-visible telescope before a declaration result.

    In a theorem such as ``theorem t (h : P) : ∃ (M : Model), Q M``, ``M`` is
    a conclusion witness, not a premise.  The textual audit deliberately
    derives caller premises from the top-level binder telescope only.  This is
    a small Lean-syntax scan rather than a declaration-name convention.
    """

    header = declaration_header(source)
    depth = 0
    quote: str | None = None
    escaped = False
    for index, char in enumerate(header):
        if quote is not None:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == quote:
                quote = None
            continue
        if char in {'"', "'"}:
            quote = char
            continue
        if char in "([{":
            depth += 1
            continue
        if char in ")]}":
            depth = max(depth - 1, 0)
            continue
        if char == ":" and depth == 0:
            return header[:index].rstrip()
    return header


def _binder_names(raw_names: str) -> list[str]:
    """Split Lean binder name groups, dropping common binder modifiers."""

    names = []
    for chunk in re.split(r"\s+", raw_names.strip()):
        name = chunk.strip()
        if not name or name in {"_", "inst"}:
            continue
        if name.startswith("[") or name.endswith("]"):
            continue
        names.append(name)
    return names


def _is_hypothesis_binder(names: list[str], type_text: str) -> bool:
    """Heuristic for binders that represent assumptions/proof boundaries."""

    normalized_type = f" {type_text.strip()} "
    non_arrow_proposition_like = (
        any(marker in normalized_type for marker in NON_ARROW_PROPOSITION_TYPE_MARKERS)
        or PREDICATE_TYPE_WORD_RE.search(type_text) is not None
    )
    if "→" in type_text and not type_text.strip().endswith("Prop") and not non_arrow_proposition_like:
        return False
    proposition_like = (
        any(marker in normalized_type for marker in PROPOSITION_TYPE_MARKERS)
        or PREDICATE_TYPE_WORD_RE.search(type_text) is not None
    )
    if any(HYPOTHESIS_NAME_RE.match(name) for name in names):
        return proposition_like or PROOF_BOUNDARY_TYPE_RE.search(type_text) is not None
    if PROOF_BOUNDARY_TYPE_RE.search(type_text):
        return not DATA_PARAMETER_TYPE_RE.match(type_text)
    return False


def hidden_premise_binders(source: str, assumption_names: set[str]) -> list[str]:
    """Return theorem binders that do not route through explicit assumption rows."""

    header = declaration_explicit_binder_prefix(source)
    hidden: list[str] = []
    for match in LEAN_BINDER_RE.finditer(header):
        names = _binder_names(match.group(1))
        type_text = match.group(2).strip()
        if not names or not _is_hypothesis_binder(names, type_text):
            continue
        if any(name in assumption_names for name in names):
            continue
        if any(assumption in type_text for assumption in assumption_names):
            continue
        hidden.append(normalize_premise_text(f"{' '.join(names)} : {type_text}"))
    return hidden


def explicit_boundary_premises(premises: list[str]) -> list[str]:
    """Return visible premises that are still proof/provenance boundaries."""

    return [
        premise
        for premise in premises
        if is_review_explicit_boundary_premise(premise)
        or LIBRARY_EXTERNAL_BOUNDARY_RE.search(premise)
    ]


def library_boundary_binders(source: str) -> list[tuple[str, str]]:
    """Return certificate/source-boundary-shaped binders from a library declaration.

    Library theorem hypotheses are usually legitimate mathematical preconditions.
    This classifier intentionally reports only certificate-like, source-row-like,
    or external-boundary-like parameters that paper wrappers must discharge before
    being called fully formalized.
    """

    header = declaration_explicit_binder_prefix(source)
    boundaries: list[tuple[str, str]] = []
    for match in LEAN_BINDER_RE.finditer(header):
        names = _binder_names(match.group(1))
        type_text = match.group(2).strip()
        if not names:
            continue
        premise = normalize_premise_text(f"{' '.join(names)} : {type_text}")
        joined_names = " ".join(names)
        haystack = f"{joined_names} {type_text}"
        if LIBRARY_EXTERNAL_BOUNDARY_RE.search(haystack):
            boundaries.append(("external", premise))
            continue
        if LIBRARY_BOUNDARY_TYPE_RE.search(type_text) or LIBRARY_CERTIFICATE_BOUNDARY_RE.search(joined_names):
            boundaries.append(("certificate", premise))
            continue
        if re.search(r"\bsource\b", haystack, re.I) and re.search(r"\b(?:row|table|formula|equation|surface)\b", haystack, re.I):
            boundaries.append(("source-row", premise))
            continue
    return boundaries


def resolve_library_target(
    declaration_index: dict[str, list[LeanDeclaration]], target_name: str | None
) -> list[LeanDeclaration]:
    """Resolve a thin alias target against reusable-library declarations."""

    if not target_name:
        return []
    candidates: list[LeanDeclaration] = []
    if target_name in declaration_index:
        candidates.extend(declaration_index[target_name])
    unqualified = target_name.rsplit(".", 1)[-1]
    candidates.extend(declaration_index.get(unqualified, []))
    seen: set[tuple[Path, int, str]] = set()
    out: list[LeanDeclaration] = []
    for declaration in candidates:
        key = (declaration.path, declaration.line, declaration.name)
        if key in seen:
            continue
        seen.add(key)
        out.append(declaration)
    return out


def _boundary_dependency_key(
    dependency: BoundaryDependency,
) -> tuple[str, str, Path, int, str]:
    declaration = dependency.declaration
    return (
        dependency.category,
        dependency.premise,
        declaration.path,
        declaration.line,
        declaration.name,
    )


def dedupe_boundary_dependencies(
    dependencies: list[BoundaryDependency],
) -> list[BoundaryDependency]:
    seen: set[tuple[str, str, Path, int, str]] = set()
    out: list[BoundaryDependency] = []
    for dependency in dependencies:
        key = _boundary_dependency_key(dependency)
        if key in seen:
            continue
        seen.add(key)
        out.append(dependency)
    return out


def library_reference_target_map(
    declarations: list[LeanDeclaration],
    library_declaration_index: dict[str, list[LeanDeclaration]],
) -> dict[tuple[Path, int, str], list[LeanDeclaration]]:
    """Resolve reusable-library declaration references once for fixed-point scans."""

    out: dict[tuple[Path, int, str], list[LeanDeclaration]] = {}
    for declaration in declarations:
        targets: list[LeanDeclaration] = []
        seen: set[tuple[Path, int, str]] = set()
        for reference in declaration_reference_names(declaration.source):
            for target in resolve_library_target(library_declaration_index, reference):
                key = declaration_key(target)
                if key == declaration_key(declaration) or key in seen:
                    continue
                seen.add(key)
                targets.append(target)
        out[declaration_key(declaration)] = targets
    return out


def declaration_result_type_text(source: str) -> str:
    header = declaration_header(source)
    if " : " not in header:
        return ""
    return normalize_premise_text(header.rsplit(" : ", 1)[1])


def declaration_result_type_head(declaration: LeanDeclaration) -> str:
    result = declaration_result_type_text(declaration.source)
    if not result:
        return ""
    return result.strip().split(None, 1)[0].strip("(){}[]").rsplit(".", 1)[-1]


def boundary_type_alias_map(declarations: list[LeanDeclaration]) -> dict[str, set[str]]:
    """Discover transparent boundary aliases from declarations.

    Standard/template: a boundary alias is a declaration of the form
    `def Alias ... : Prop := Target ...`, where both `Alias` and `Target` have
    certificate/source-boundary-shaped heads. This lets the audit recognize
    closed constructors for definitionally equivalent certificate types without
    naming paper- or library-specific functions.
    """

    aliases: dict[str, set[str]] = {}
    for declaration in declarations:
        if declaration.kind != "def":
            continue
        if declaration_result_type_text(declaration.source) != "Prop":
            continue
        alias_head = declaration.name.rsplit(".", 1)[-1]
        if not LIBRARY_BOUNDARY_TYPE_RE.fullmatch(alias_head):
            continue
        body = lean_code_text(declaration_body(declaration.source)).strip()
        match = DECLARATION_REFERENCE_RE.search(body)
        if not match:
            continue
        target_head = match.group(0).rsplit(".", 1)[-1]
        if not LIBRARY_BOUNDARY_TYPE_RE.fullmatch(target_head):
            continue
        aliases.setdefault(alias_head, set()).add(target_head)

    changed = True
    while changed:
        changed = False
        for alias, targets in list(aliases.items()):
            expanded = set(targets)
            for target in list(targets):
                expanded.update(aliases.get(target, set()))
            if not expanded.issubset(targets):
                aliases[alias] = targets | expanded
                changed = True
    return aliases


def boundary_type_heads_for_premise(
    premise: str,
    boundary_aliases: dict[str, set[str]] | None = None,
) -> set[str]:
    type_text = premise_type_text(premise)
    head = type_text.strip().split(None, 1)[0].strip("(){}[]")
    unqualified = head.rsplit(".", 1)[-1]
    heads = {unqualified}
    if boundary_aliases:
        heads.update(boundary_aliases.get(unqualified, set()))
    return heads


def references_discharge_boundary(
    referenced_targets: list[LeanDeclaration],
    dependency_indexes: list[dict[tuple[Path, int, str], list[BoundaryDependency]]],
    premise: str,
    boundary_aliases: dict[str, set[str]],
) -> bool:
    """Return true when references include a closed constructor for `premise`.

    Standard/template: a constructor discharges a boundary only when it returns
    the same boundary type head (modulo transparent boundary aliases) and the
    constructor itself has no currently known boundary dependencies.
    """

    type_heads = boundary_type_heads_for_premise(premise, boundary_aliases)
    for target in referenced_targets:
        target_key = declaration_key(target)
        if any(target_key in dependency_index for dependency_index in dependency_indexes):
            continue
        if declaration_result_type_head(target) in type_heads:
            return True
    return False


def referenced_library_boundary_dependencies(
    referenced_targets: list[LeanDeclaration],
    library_boundary_dependency_index: dict[tuple[Path, int, str], list[BoundaryDependency]],
    boundary_aliases: dict[str, set[str]],
) -> list[BoundaryDependency]:
    """Return certificate dependencies of referenced reusable-library declarations."""

    dependencies: list[BoundaryDependency] = []
    seen_targets: set[tuple[Path, int, str]] = set()
    for target in referenced_targets:
        target_key = declaration_key(target)
        if target_key in seen_targets:
            continue
        seen_targets.add(target_key)
        for dependency in library_boundary_dependency_index.get(target_key, []):
            if references_discharge_boundary(
                referenced_targets,
                [library_boundary_dependency_index],
                dependency.premise,
                boundary_aliases,
            ):
                continue
            dependencies.append(
                BoundaryDependency(
                    category=dependency.category,
                    premise=dependency.premise,
                    declaration=dependency.declaration,
                    via=target.name,
                )
            )
    return dedupe_boundary_dependencies(dependencies)


def library_boundary_dependency_index(
    declaration_index: dict[str, list[LeanDeclaration]],
) -> dict[tuple[Path, int, str], list[BoundaryDependency]]:
    """Propagate reusable-library certificate/source boundaries through calls.

    Direct boundary binders mark a declaration immediately.  A fixed point over
    lexical declaration references then marks reusable helpers that call such
    APIs.  The index is rebuilt from current Lean files on each audit run, so it
    cannot go stale like a checked-in dependency manifest.
    """

    declarations = unique_declarations(declaration_index)
    reference_targets = library_reference_target_map(declarations, declaration_index)
    boundary_aliases = boundary_type_alias_map(declarations)
    dependencies: dict[tuple[Path, int, str], list[BoundaryDependency]] = {}
    for declaration in declarations:
        direct = [
            BoundaryDependency(
                category=category,
                premise=premise,
                declaration=declaration,
                via=declaration.name,
            )
            for category, premise in library_boundary_binders(declaration.source)
        ]
        if direct:
            dependencies[declaration_key(declaration)] = direct

    changed = True
    while changed:
        changed = False
        for declaration in declarations:
            key = declaration_key(declaration)
            current = dependencies.get(key, [])
            propagated = referenced_library_boundary_dependencies(
                reference_targets.get(key, []),
                dependencies,
                boundary_aliases,
            )
            merged = dedupe_boundary_dependencies(current + propagated)
            if len(merged) != len(current):
                dependencies[key] = merged
                changed = True
    return dependencies




def source_specific_library_smells(declaration: LeanDeclaration) -> list[str]:
    """Heuristically flag source-shaped formulas living in the reusable library."""

    reasons: list[str] = []
    name = declaration.name
    header = declaration_header(declaration.source)
    if SOURCE_SHAPED_LIBRARY_NAME_RE.search(name):
        reasons.append("source/paper-shaped reusable declaration name")
    if re.search(r"(?:^|_)(?:paper|displayed|appendix)(?:_|$)", name, re.I):
        reasons.append("paper/displayed-shaped declaration name")
    if re.search(r"(?:^|_)source(?:_|$).*(?:row|formula|equation|surface|displayed|paper)", name, re.I):
        reasons.append("source-row/formula-shaped declaration name")
    if re.search(r"(?:^|_)(?:theorem|thm|lemma|lem|proposition|prop|corollary|claim)[A-Z]?\d+", name, re.I):
        reasons.append("numbered-paper-result-shaped declaration name")
    if re.search(r"\bSource status\s*:", declaration.source, re.I):
        reasons.append("paper-review provenance text appears inside library declaration")
    if re.search(r"\b(?:paper|displayed)\b", header, re.I) and FORMULA_SPECIFIC_NAME_RE.search(header):
        reasons.append("source-shaped formula appears in declaration signature")
    return reasons


def check_library_source_assumption_standards() -> list[Finding]:
    """Reject source assumptions as reusable-library API objects.

    Reusable code may expose explicit certificates/oracles for external
    mathematical facts.  It should not define reusable `Assumption` or
    `Hypothesis` records: those are paper-local provenance objects and must live
    in a paper folder where the source text and LLM/human judgments can validate
    them directly.
    """

    findings: list[Finding] = []
    seen: set[tuple[Path, int, str]] = set()
    for declaration in unique_declarations(library_lean_declaration_index()):
        key = declaration_key(declaration)
        if key in seen:
            continue
        seen.add(key)
        if re.match(r"\s*private\s+", declaration.source):
            continue
        if LIBRARY_FORBIDDEN_SOURCE_ASSUMPTION_RE.search(declaration.name):
            findings.append(
                Finding(
                    "ERROR",
                    declaration.path,
                    f"library `{declaration.name}` at line {declaration.line} uses "
                    "`Assumption`/`Hypothesis` naming; paper assumptions must live in "
                    "paper-local `Assumptions.lean`, and reusable APIs should require "
                    "generic certificates or derived proofs instead",
                )
            )
        if ASSUMPTION_AUDIT_PREMISE_RE.search(declaration.source):
            findings.append(
                Finding(
                    "ERROR",
                    declaration.path,
                    f"library `{declaration.name}` at line {declaration.line} contains "
                    "`audit-premise`; source-premise validation belongs in paper-local "
                    "`Assumptions.lean`, not reusable library code",
                )
            )
    return sorted(findings, key=lambda finding: (str(finding.path), finding.message))


def check_library_reusable_provenance_language() -> list[Finding]:
    """Reject paper/source-provenance wording in reusable Lean modules."""

    findings: list[Finding] = []
    for path in library_lean_files():
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            continue
        for line_no, line in enumerate(text.splitlines(), start=1):
            match = REUSABLE_LIBRARY_PROVENANCE_TEXT_RE.search(line)
            if not match:
                continue
            findings.append(
                Finding(
                    "ERROR",
                    path,
                    f"reusable library line {line_no} uses paper/source-provenance "
                    f"wording `{match.group(0)}`; put source-text provenance in "
                    "paper-local files and describe shared declarations as generic "
                    "mathematical APIs",
                )
            )
    return sorted(findings, key=lambda finding: (str(finding.path), finding.message))


def check_library_standard_definition_audits() -> list[Finding]:
    """Require Lean-checked audit lemmas for standard-name definitions."""

    findings: list[Finding] = []
    audit_file = LIBRARY_STANDARD_DEFINITION_AUDIT_FILE
    if not audit_file.exists():
        return [
            Finding(
                "ERROR",
                audit_file,
                "missing reusable definition audit module; standard mathematical "
                "wrappers need build-checked equivalence lemmas",
            )
        ]

    text = audit_file.read_text(encoding="utf-8")
    root_module = ROOT / "AppliedModelingLib.lean"
    if root_module.exists() and "import AppliedModelingLib.LibraryDefinitionAudit" not in root_module.read_text(
        encoding="utf-8"
    ):
        findings.append(
            Finding(
                "ERROR",
                root_module,
                "`AppliedModelingLib.LibraryDefinitionAudit` should be imported by the root "
                "library target so CI builds the standard-definition checks",
            )
        )

    for decl_name, description in REQUIRED_LIBRARY_STANDARD_AUDITS.items():
        if not re.search(rf"^\s*(?:theorem|lemma)\s+{re.escape(decl_name)}\b", text, re.M):
            findings.append(
                Finding(
                    "ERROR",
                    audit_file,
                    f"missing standard-definition audit `{decl_name}` ({description})",
                )
            )
    return findings


def configured_review_rows(
    interface_text: str, review_surface: dict[str, object]
) -> list[tuple[int, str]]:
    """Count the configured human surface, including assumptions, without helpers."""

    rows = _legacy_review_surface_structure_module().review_rows_from_interface_text(interface_text)

    def names(field: str) -> set[str]:
        raw = review_surface.get(field)
        return {str(value).strip() for value in raw if str(value).strip()} if isinstance(raw, list) else set()

    included = names("include_names")
    assumptions = names("assumption_names")
    auxiliary = names("auxiliary_names")
    return [
        row for row in rows
        if (not included or row[1] in included or row[1] in assumptions)
        and row[1] not in auxiliary
    ]


def review_surface_slice_counts(interface_text: str, status_file: Path) -> tuple[list[str], dict[str, int]]:
    """Count human-review declaration rows by paper-local status review slices."""

    decls = _legacy_review_surface_structure_module().review_rows_from_interface_text(
        interface_text
    )
    if not status_file.exists():
        return [], {"all": len(decls)}

    try:
        payload = json.loads(status_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return ["status.json is not valid JSON"], {"all": len(decls)}
    if not isinstance(payload, dict):
        return ["status.json should contain a JSON object"], {"all": len(decls)}
    review_surface = payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return ["status.json should define a `review_surface` object"], {"all": len(decls)}
    decls = configured_review_rows(interface_text, review_surface)
    raw_slices = review_surface.get("slices")
    if not isinstance(raw_slices, list) or not raw_slices:
        return ["status.json review_surface should define a nonempty `slices` list"], {"all": len(decls)}

    problems: list[str] = []
    slices: list[dict[str, object]] = []
    for index, raw_slice in enumerate(raw_slices, start=1):
        if not isinstance(raw_slice, dict):
            problems.append(f"slice {index} is not a JSON object")
            continue
        title = str(raw_slice.get("title") or raw_slice.get("id") or f"Slice {index}")
        slices.append({**raw_slice, "id": _safe_slice_id(str(raw_slice.get("id") or title))})

    counts: dict[str, int] = {str(rule["id"]): 0 for rule in slices}
    counts["other"] = 0
    for line_number, name in decls:
        assigned = False
        for rule in slices:
            names = rule.get("names")
            prefixes = rule.get("prefixes")
            pattern = rule.get("name_regex")
            line_start = rule.get("line_start")
            line_end = rule.get("line_end")
            try:
                matches_name = isinstance(names, list) and name in {str(item) for item in names}
                matches_prefix = isinstance(prefixes, list) and any(
                    name.startswith(str(prefix)) for prefix in prefixes
                )
                matches_regex = isinstance(pattern, str) and bool(re.search(pattern, name))
            except re.error:
                problems.append(f"slice `{rule['id']}` has invalid `name_regex`")
                matches_regex = False
            matches_line = False
            if isinstance(line_start, int) or isinstance(line_end, int):
                start_ok = not isinstance(line_start, int) or line_number >= line_start
                end_ok = not isinstance(line_end, int) or line_number <= line_end
                matches_line = start_ok and end_ok
            if matches_name or matches_prefix or matches_regex or matches_line:
                counts[str(rule["id"])] = counts.get(str(rule["id"]), 0) + 1
                assigned = True
                break
        if not assigned:
            counts["other"] += 1
    if counts.get("other") == 0:
        counts.pop("other", None)
    return problems, counts


def check_review_launcher_readiness(include_active: bool) -> list[Finding]:
    """Check the paper-local human-review launcher contract from the skill."""

    findings: list[Finding] = []
    launcher_text = f"{REVIEW_LAUNCHER_TARGET}"
    for folder in paper_dirs():
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue

        interface = folder / "PaperInterface.lean"
        launcher = folder / REVIEW_LAUNCHER_NAME
        cache = folder / REVIEW_TRACE_CACHE

        if not interface.exists():
            findings.append(
                Finding(
                    "ERROR",
                    folder,
                    "review launcher cannot be enabled until `PaperInterface.lean` exists",
                )
            )
            if launcher.exists():
                findings.append(
                    Finding(
                        "WARN",
                        launcher,
                        "review launcher exists but there is no `PaperInterface.lean` to review",
                    )
                )
            continue

        if not launcher.exists():
            findings.append(
                Finding(
                    "ERROR",
                    folder,
                    f"missing `{REVIEW_LAUNCHER_NAME}`; run `python3 scripts/bootstrap_review_launchers.py --write`",
                )
            )
        else:
            text = launcher.read_text(encoding="utf-8")
            if launcher_text not in text:
                findings.append(
                    Finding(
                        "ERROR",
                        launcher,
                        f"launcher should delegate to `{REVIEW_LAUNCHER_TARGET}`",
                    )
                )
            if not (launcher.stat().st_mode & 0o111):
                findings.append(Finding("ERROR", launcher, "launcher is not executable"))

        if not cache.exists():
            findings.append(
                Finding(
                    "WARN",
                    folder,
                    "review dashboard cache is absent; run `python3 scripts/review_dashboard.py --paper "
                    f"{folder.name} --refresh-cache` before a review session",
                )
            )

        status_file = folder / "status.json"
        review_surface: dict[str, object] = {}
        status_payload: dict[str, object] = {}
        if status_file.exists():
            try:
                payload = json.loads(status_file.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                payload = {}
            if isinstance(payload, dict):
                status_payload = payload
                if isinstance(payload.get("review_surface"), dict):
                    review_surface = payload["review_surface"]  # type: ignore[assignment]
        review_source = review_surface_source_file_path(folder, review_surface)
        if not review_source.exists():
            findings.append(Finding("ERROR", review_source, "configured review surface does not exist"))
            continue
        review_source_text = review_source.read_text(encoding="utf-8")
        item_count = len(configured_review_rows(review_source_text, review_surface))
        if item_count == 0:
            if not status_allows_empty_review_surface(status_payload):
                findings.append(Finding("ERROR", review_source, "review dashboard finds no review rows"))
        elif item_count > REVIEW_ROW_WARN_THRESHOLD:
            problems, counts = review_surface_slice_counts(review_source_text, status_file)
            for problem in sorted(set(problems)):
                findings.append(Finding("ERROR", status_file, problem))
            max_slice = max(counts.values()) if counts else item_count
            if not status_file.exists():
                findings.append(
                    Finding(
                        "WARN",
                        review_source,
                        f"review dashboard exposes {item_count} rows; add `status.json` "
                        f"`review_surface.slices` of at most {REVIEW_ROW_WARN_THRESHOLD} rows",
                    )
                )
            elif max_slice > REVIEW_ROW_WARN_THRESHOLD:
                findings.append(
                    Finding(
                        "WARN",
                        status_file,
                        f"largest review slice has {max_slice} rows; keep slices at or below "
                        f"{REVIEW_ROW_WARN_THRESHOLD} rows",
                    )
                )
            else:
                findings.append(
                    Finding(
                        "INFO",
                        status_file,
                        f"review dashboard exposes {item_count} rows across {len(counts)} review slices",
                    )
                )

    return findings


def check_dag_status_styles() -> list[Finding]:
    findings: list[Finding] = []
    preamble = ROOT / "docs" / "tikz" / "dag_preamble.tex"
    template = PAPERS / "TEMPLATE" / DEPENDENCY_DAG_TEX_FILE
    if preamble.exists():
        text = preamble.read_text(encoding="utf-8")
        for style in sorted(DAG_STATUS_STYLES):
            if f"{style}/.style" not in text:
                findings.append(Finding("ERROR", preamble, f"missing DAG status style `{style}`"))
    if template.exists():
        text = template.read_text(encoding="utf-8")
        normalized_text = re.sub(r"\\+", " ", text)
        normalized_text = re.sub(r"\s+", " ", normalized_text)
        for status in sorted(PAPER_STATUS_VALUES):
            if status not in normalized_text:
                findings.append(Finding("ERROR", template, f"template legend should mention status `{status}`"))
    return findings


def check_paper_facing_ledgers(include_active: bool) -> list[Finding]:
    findings: list[Finding] = []
    for folder in paper_dirs():
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue

        review_surface: dict[str, object] = {}
        status_file = folder / "status.json"
        if status_file.exists():
            try:
                status_payload = json.loads(status_file.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                status_payload = {}
            if isinstance(status_payload, dict) and isinstance(status_payload.get("review_surface"), dict):
                review_surface = status_payload["review_surface"]  # type: ignore[assignment]
        review_source = review_surface_source_file_path(folder, review_surface)
        ledger_candidates = [folder / "MainTheorems.lean", folder / "PaperInterface.lean"]
        if review_source.exists() and review_source not in ledger_candidates:
            ledger_candidates.append(review_source)
        existing = [path for path in ledger_candidates if path.exists()]
        if not existing:
            continue

        for ledger in existing:
            text = ledger.read_text(encoding="utf-8")
            if LEDGER_PLACEHOLDER_RE.search(text):
                findings.append(
                    Finding("ERROR", ledger, "paper-facing ledger still contains template placeholders")
                )
            compact_import_shim = (
                ledger.name == "PaperInterface.lean"
                and review_source.exists()
                and review_source.resolve() != ledger.resolve()
            )
            if not compact_import_shim and not LEAN_DECL_RE.search(text):
                findings.append(
                    Finding("WARN", ledger, "paper-facing ledger has no theorem/lemma/def/abbrev declarations")
                )
            if "#check" in text and "#guard_msgs(drop info) in" not in text:
                findings.append(
                    Finding("ERROR", ledger, "paper-facing ledger contains unguarded `#check`")
                )
    return findings


def check_post_paper_audit_interfaces(include_active: bool) -> list[Finding]:
    findings: list[Finding] = []
    interface_required = {
        folder.name
        for folder in paper_dirs()
        if is_closeout_status(paper_local_status(folder))
    }

    for folder in paper_dirs():
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue

        interface = folder / "PaperInterface.lean"
        audit = folder / "PostPaperAudit.lean"
        report = paper_relative_file(
            folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md"
        )
        aggregator = PAPERS / f"{folder.name}.lean"
        review_surface: dict[str, object] = {}
        status_file = folder / "status.json"
        if status_file.exists():
            try:
                status_payload = json.loads(status_file.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                status_payload = {}
            if isinstance(status_payload, dict) and isinstance(status_payload.get("review_surface"), dict):
                review_surface = status_payload["review_surface"]  # type: ignore[assignment]
        review_source = review_surface_source_file_path(folder, review_surface)
        human_interface = review_source if review_source.exists() else interface

        if folder.name in interface_required and not interface.exists():
            findings.append(
                Finding(
                    "ERROR",
                    folder,
                    "completed/formalized paper is missing `PaperInterface.lean`",
                )
            )

        if interface.exists():
            text = interface.read_text(encoding="utf-8")
            if folder.name in interface_required and aggregator.exists():
                import_line = f"import {folder.name}.PaperInterface"
                if import_line not in aggregator.read_text(encoding="utf-8"):
                    findings.append(
                        Finding(
                            "ERROR",
                            aggregator,
                            "completed/formalized paper root should import `PaperInterface.lean`",
                        )
                    )
            if "PProd" in text:
                findings.append(
                    Finding("ERROR", interface, "human-facing interface should not use tuple witnesses")
                )
        if human_interface.exists():
            text = human_interface.read_text(encoding="utf-8")
            if "PProd" in text:
                findings.append(
                    Finding("ERROR", human_interface, "human-facing interface should not use tuple witnesses")
                )
            tuple_witness_decls = interface_tuple_witness_declarations(text)
            if tuple_witness_decls:
                sample_line, sample_name = tuple_witness_decls[0]
                findings.append(
                    Finding(
                        "ERROR",
                        human_interface,
                        "human-facing interface should not expose tuple/prod witness "
                        f"result declarations, e.g. `{sample_name}` at line {sample_line}",
                    )
                )
            if not re.search(r"^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+", text, re.M):
                findings.append(
                    Finding(
                        "WARN",
                        human_interface,
                        "human-facing interface has no visible definition/abbrev declarations",
                    )
                )
            has_theorem_or_theorem_alias = re.search(r"^\s*theorem\s+", text, re.M) or re.search(
                r"^\s*(?:(?:noncomputable|private|protected)\s+)*(?:def|abbrev)\s+"
                r"(?:theorem|lemma|proposition|corollary)[A-Za-z0-9_']*\b",
                text,
                re.M,
            )
            if not has_theorem_or_theorem_alias:
                findings.append(
                    Finding("WARN", human_interface, "human-facing interface has no visible theorem statements")
                )

        if audit.exists():
            text = audit.read_text(encoding="utf-8")
            if interface.exists() and "PaperInterface.lean" not in text:
                findings.append(
                    Finding("WARN", audit, "legacy proof ledger should point to `PaperInterface.lean`")
                )
            for match in PROOF_FACING_AUDIT_FORMULA_RE.finditer(text):
                line_no = text.count("\n", 0, match.start()) + 1
                findings.append(
                    Finding(
                        "ERROR",
                        audit,
                        f"proof-facing formula alias at line {line_no}; put paper formulas in `PaperInterface.lean`",
                    )
                )

        if report.exists():
            text = report.read_text(encoding="utf-8")
            if "Lean witness" in text:
                findings.append(
                    Finding(
                        "WARN",
                        report,
                        "final report should prefer `Lean interface statement(s)` over `Lean witness`",
                    )
                )

        post_audit = paper_relative_file(
            folder, POST_FORMALIZATION_AUDIT_FILE, "POST_FORMALIZATION_AUDIT.md"
        )
        for markdown_report in (report, post_audit):
            if markdown_report.exists():
                findings.extend(check_report_declaration_inventory(markdown_report))

    return findings


def report_decl_code_spans(text: str) -> list[str]:
    spans: list[str] = []
    for span in REPORT_CODE_SPAN_RE.findall(text):
        if span.endswith(REPORT_NON_DECL_CODE_SUFFIXES):
            continue
        if "/" in span or " " in span or "-" in span:
            continue
        if REPORT_DECL_NAME_RE.fullmatch(span):
            spans.append(span)
    return spans


def check_report_declaration_inventory(path: Path) -> list[Finding]:
    findings: list[Finding] = []
    text = path.read_text(encoding="utf-8")
    if re.search(r"\bmain Lean declarations\b", text, re.I):
        findings.append(
            Finding(
                "WARN",
                path,
                "final/post report should name one main interface declaration per paper-facing result, not a declaration inventory",
            )
        )

    for line_no, line in enumerate(text.splitlines(), start=1):
        if REPORT_LEAN_LABEL_RE.search(line):
            spans = report_decl_code_spans(line)
            if len(spans) > 1:
                findings.append(
                    Finding(
                        "WARN",
                        path,
                        f"line {line_no} lists {len(spans)} Lean declarations; keep only the single main interface declaration",
                    )
                )

    for header, rows in iter_markdown_tables(path):
        for idx, cell in enumerate(header):
            if not REPORT_DECL_TABLE_HEADER_RE.search(cell):
                continue
            for row in rows:
                if idx >= len(row):
                    continue
                spans = report_decl_code_spans(row[idx])
                if len(spans) > 1:
                    findings.append(
                        Finding(
                            "WARN",
                            path,
                            f"table column `{cell}` lists {len(spans)} Lean declarations in one row; keep one main interface declaration per paper-facing result",
                        )
                    )
    return findings


def markdown_cells(line: str) -> list[str]:
    return [cell.strip() for cell in line.strip().strip("|").split("|")]


def iter_markdown_tables(path: Path) -> list[tuple[list[str], list[list[str]]]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    tables: list[tuple[list[str], list[list[str]]]] = []
    i = 0
    while i + 1 < len(lines):
        if "|" not in lines[i] or "|" not in lines[i + 1]:
            i += 1
            continue
        header = markdown_cells(lines[i])
        separator = markdown_cells(lines[i + 1])
        if not separator or not all(re.fullmatch(r":?-{3,}:?", cell) for cell in separator):
            i += 1
            continue
        rows: list[list[str]] = []
        i += 2
        while i < len(lines) and "|" in lines[i]:
            rows.append(markdown_cells(lines[i]))
            i += 1
        tables.append((header, rows))
    return tables



def _certified_source_definition_item(
    folder: Path,
    name: str,
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> bool:
    """Require pinned and independently attested source-definition evidence."""

    statement_map = folder / "audit" / "paper_statement_map.json"
    payload = (
        run_context.exact_json_payload(statement_map)
        if run_context is not None
        else load_json_object(statement_map)
    )
    if not payload or payload.get("source_curated") is not True or payload.get("seed_scaffold") is True:
        return False
    try:
        from scripts.audit_evidence_integrity import (
            identities_for_keys,
            source_artifact_pin_findings,
        )
        if source_artifact_pin_findings(
            folder, "formalized", statement_map, payload
        ):
            return False
    except Exception:  # noqa: BLE001 - certification fails closed.
        return False
    curator = str(payload.get("source_curator") or "").strip()
    curated_at = str(payload.get("source_curated_at") or "").strip()
    if not curator or not curated_at:
        return False
    status_payload = (
        run_context.exact_json_payload(folder / "status.json")
        if run_context is not None
        else load_json_object(folder / "status.json")
    ) or {}
    formalizer_ids = identities_for_keys(
        status_payload,
        {"formalizer", "formalization_agent", "formalization_producer"},
    )
    if curator in formalizer_ids:
        return False
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return False
    for key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict):
            continue
        routed_names = {str(key).strip()}
        for field in ("aliases", "lean_declarations", "support_lean_declarations"):
            values = raw_item.get(field)
            if isinstance(values, list):
                routed_names.update(str(value).strip() for value in values)
        if name not in routed_names:
            continue
        if str(raw_item.get("source_kind") or "").strip().lower() != "definition":
            continue
        source_kind_validator = str(
            raw_item.get("source_kind_validator") or ""
        ).strip()
        source_kind_validated_at = str(
            raw_item.get("source_kind_validated_at") or ""
        ).strip()
        human_reviewer = str(
            raw_item.get("source_kind_human_reviewer") or ""
        ).strip()
        human_reviewed_at = str(
            raw_item.get("source_kind_human_reviewed_at") or ""
        ).strip()
        if (
            not source_kind_validator
            or not source_kind_validated_at
            or source_kind_validator == curator
            or raw_item.get("source_kind_human_approved") is not True
            or not human_reviewer
            or not human_reviewed_at
            or human_reviewer in {curator, source_kind_validator}
            or bool(
                {source_kind_validator, human_reviewer} & formalizer_ids
            )
        ):
            continue
        location = str(raw_item.get("source_location") or "").strip()
        if SOURCE_RECORD_EXACT_LOCATOR_RE.search(location):
            return True
    return False


def check_source_proof_fidelity(
    folder: Path,
    status: str,
    status_payload: dict[str, object],
    *,
    require_source_bytes: bool = True,
    run_context: PaperCloseoutRunContext | None = None,
) -> list[Finding]:
    """Run the optional semantic source-proof ledger gate in repository closeout.

    Keep the schema/semantic validation in ``audit_evidence_integrity`` so its
    fast standalone gate and the full repository closeout use the same rules.
    """

    try:
        from scripts.audit_evidence_integrity import source_proof_fidelity_findings
        external_findings = source_proof_fidelity_findings(
            folder,
            status,
            status_payload,
            require_source_bytes=require_source_bytes,
            context=(
                run_context.evidence_context
                if run_context is not None
                else None
            ),
        )
    except Exception as error:  # noqa: BLE001 - provenance gate fails closed.
        return [
            Finding(
                "ERROR",
                folder / "status.json",
                f"source-proof fidelity audit could not run: {error}",
            )
        ]

    converted: list[Finding] = []
    for finding in external_findings:
        raw_path = Path(str(finding.path))
        path = raw_path if raw_path.is_absolute() else ROOT / raw_path
        converted.append(Finding(str(finding.severity), path, str(finding.message)))
    return converted


def check_explicit_source_route_semantic_model_evidence(
    folder: Path,
    status: str,
    status_payload: dict[str, object],
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> list[Finding]:
    """Reuse the fast gate's current semantic-model closeout requirement.

    Repository closeout validates and reuses the transaction's broader
    source-record evidence below, but must also reject an explicit-route v10
    status surface that lacks the saved current semantic-model lane. Keep the
    trigger and freshness rules shared with the push-time integrity audit.
    """

    if run_context is not None and run_context.selected_v11_closeout:
        return []

    try:
        from scripts.audit_evidence_integrity import (
            explicit_source_route_semantic_model_findings,
        )
        external_findings = explicit_source_route_semantic_model_findings(
            folder,
            status,
            status_payload,
            context=(
                run_context.evidence_context
                if run_context is not None
                else None
            ),
        )
    except Exception as error:  # noqa: BLE001 - provenance gate fails closed.
        return [
            Finding(
                "ERROR",
                folder / "status.json",
                f"explicit-route semantic-model evidence audit could not run: {error}",
            )
        ]

    converted: list[Finding] = []
    for finding in external_findings:
        raw_path = Path(str(finding.path))
        path = raw_path if raw_path.is_absolute() else ROOT / raw_path
        converted.append(Finding(str(finding.severity), path, str(finding.message)))
    return converted


def _current_v11_review_route_partition(
    paper_id: str,
    folder: Path,
    review_names: set[str] | frozenset[str],
    *,
    run_context: PaperCloseoutRunContext,
) -> tuple[ReviewRoutePartition | None, list[Finding]]:
    """Load the exact typed route set and delegate its closed partition."""

    source_map = run_context.exact_json_payload(
        folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
    )
    if not isinstance(source_map, Mapping):
        return None, [
            Finding(
                "ERROR",
                folder / "status.json",
                f"`{paper_id}` retained v11 transaction has no statement map",
            )
        ]
    try:
        route_set = EvidenceRouteSet.from_source_map(source_map)
    except ObligationRouteError as exc:
        return None, [
            Finding(
                "ERROR",
                folder / "status.json",
                f"`{paper_id}` retained v11 transaction has invalid typed routes: {exc}",
            )
        ]

    partition = partition_review_routes(
        paper_id=paper_id,
        review_names=tuple(review_names),
        route_set=route_set,
        declarations=run_context.paper_declaration_index(),
    )
    return partition, [
        Finding("ERROR", folder / "status.json", message)
        for message in partition.errors
    ]


def current_v11_typed_review_routes(
    paper_id: str,
    folder: Path,
    review_names: set[str] | frozenset[str],
    *,
    run_context: PaperCloseoutRunContext,
) -> tuple[
    dict[str, tuple[str, EvidenceRoute]],
    dict[str, str],
    list[Finding],
]:
    """Partition one v11 surface into typed results and direct declarations."""

    partition, findings = _current_v11_review_route_partition(
        paper_id,
        folder,
        review_names,
        run_context=run_context,
    )
    if partition is None:
        return {}, {}, findings
    return partition.result_map(), partition.direct_map(), findings


def current_v11_direct_proof_pair_findings(
    paper_id: str,
    folder: Path,
    review_surface: Mapping[str, object],
    proof_routes: Mapping[str, str],
    v11_names: set[str] | frozenset[str],
    *,
    run_context: PaperCloseoutRunContext,
) -> list[Finding]:
    """Project proof findings from the one current-v11 core gate."""

    del review_surface, proof_routes, v11_names
    errors = run_context.current_v11_primary_gate_result().proof_errors
    return [
        Finding("ERROR", folder / "status.json", message) for message in errors
    ]


def current_v11_direct_axiom_closure_findings(
    paper_id: str,
    folder: Path,
    review_surface: Mapping[str, object],
    include_names: list[str],
    approved_boundary_axioms: set[str],
    *,
    run_context: PaperCloseoutRunContext,
) -> list[Finding]:
    """Project axiom findings from the one current-v11 core gate."""

    del review_surface, include_names, approved_boundary_axioms
    errors = run_context.current_v11_primary_gate_result().axiom_errors
    return [
        Finding("ERROR", folder / "status.json", message) for message in errors
    ]


def check_proposition_spec_routes(
    paper_id: str,
    folder: Path,
    review_surface: dict[str, object],
    include_names: list[str],
    assumption_names: set[str],
    status: object,
    *,
    paper_closeout: bool,
    review_items_provider: Callable[[], tuple[Any, ...]] | None = None,
    run_context: PaperCloseoutRunContext | None = None,
) -> list[Finding]:
    """Prevent Prop-defining declarations from being counted as Lean proofs."""

    findings: list[Finding] = []
    raw_source_definitions = review_surface.get("source_definition_names", [])
    if not isinstance(raw_source_definitions, list) or not all(
        isinstance(name, str) and name.strip() for name in raw_source_definitions
    ):
        findings.append(
            Finding(
                "ERROR",
                folder / "status.json",
                f"`{paper_id}.review_surface.source_definition_names` should be a string list",
            )
        )
        source_definition_names: set[str] = set()
    else:
        source_definition_names = {name.strip() for name in raw_source_definitions}
    raw_proofs = review_surface.get("proposition_spec_proofs", {})
    if not isinstance(raw_proofs, dict) or not all(
        isinstance(spec, str)
        and spec.strip()
        and isinstance(proof, str)
        and proof.strip()
        for spec, proof in (raw_proofs.items() if isinstance(raw_proofs, dict) else [])
    ):
        findings.append(
            Finding(
                "ERROR",
                folder / "status.json",
                f"`{paper_id}.review_surface.proposition_spec_proofs` should map spec rows to proof rows",
            )
        )
        proof_routes: dict[str, str] = {}
    else:
        proof_routes = {str(spec).strip(): str(proof).strip() for spec, proof in raw_proofs.items()}

    if (
        paper_closeout
        and run_context is not None
        and run_context.selected_v11_closeout
    ):
        status_payload = run_context.exact_json_payload(folder / "status.json")
        v11_names = (
            v11_source_claim_review_names(status_payload)
            if isinstance(status_payload, Mapping)
            else None
        )
        if v11_names is not None:
            return findings + current_v11_direct_proof_pair_findings(
                paper_id,
                folder,
                review_surface,
                proof_routes,
                v11_names,
                run_context=run_context,
            )

    if paper_closeout and run_context is not None:
        status_payload = run_context.exact_json_payload(folder / "status.json")
        v11_names = (
            v11_source_claim_review_names(status_payload)
            if isinstance(status_payload, Mapping)
            else None
        )
        map_payload = run_context.exact_json_payload(
            folder / PAPER_AUDIT_DIR / "paper_statement_map.json"
        )
        map_items = (
            map_payload.get("items")
            if isinstance(map_payload, Mapping)
            else None
        )
        if v11_names is not None and isinstance(map_items, Mapping):
            declarations = run_context.paper_declaration_index()
            selected_items: list[tuple[str, Mapping[str, object]]] = []
            expected_receipt_routes: set[tuple[str, str, str, str]] = set()
            route_error = False
            for spec_name in sorted(v11_names):
                proof_name = proof_routes.get(spec_name, "")
                specs = resolve_declaration_name(declarations, spec_name)
                proofs = resolve_declaration_name(declarations, proof_name)
                if len(specs) != 1 or len(proofs) != 1:
                    route_error = True
                    break
                qualified_spec = qualified_declaration_identity(specs[0])
                qualified_proof = qualified_declaration_identity(proofs[0])
                candidates: list[tuple[str, Mapping[str, object]]] = []
                for key, raw_item in map_items.items():
                    contract = (
                        raw_item.get("semantic_contract")
                        if isinstance(raw_item, Mapping)
                        else None
                    )
                    if (
                        isinstance(contract, Mapping)
                        and str(contract.get("spec_declaration") or "").strip()
                        == qualified_spec
                        and str(contract.get("evidence_declaration") or "").strip()
                        == qualified_proof
                    ):
                        candidates.append((str(key), raw_item))
                if len(candidates) != 1:
                    route_error = True
                    break
                selected_items.extend(candidates)
                contract = candidates[0][1].get("semantic_contract")
                assert isinstance(contract, Mapping)
                expected_receipt_routes.add(
                    (
                        candidates[0][0],
                        qualified_spec,
                        qualified_proof,
                        str(contract.get("evidence_mode") or "").strip(),
                    )
                )
            if not route_error and len(selected_items) == len(v11_names):
                current_receipt_routes = {
                    (
                        receipt.source_item_key,
                        receipt.spec_declaration,
                        receipt.evidence_declaration,
                        receipt.evidence_mode,
                    )
                    for receipt in (
                        run_context.current_strict_source_spec_correspondence_receipts()
                    )
                }
                current_scope = set(
                    run_context.current_strict_source_spec_correspondence_scope_keys()
                )
                if (
                    expected_receipt_routes
                    and expected_receipt_routes.issubset(current_receipt_routes)
                    and {key for key, _item in selected_items}.issubset(current_scope)
                ):
                    # The statement-map declaration gate already ran the one
                    # exact batched Lean Meta comparison and minted these
                    # source/Spec/proof receipts inside this immutable closeout
                    # transaction.  Reconstructing dashboard manifests here
                    # would repeat that proof-pair check without adding an
                    # independent obligation.
                    return findings
                authority_errors = (
                    semantic_authority_source_spec_correspondence_errors(
                        ROOT,
                        folder,
                        map_payload,
                        selected_items,
                        evidence_context=run_context.evidence_context,
                    )
                )
                if authority_errors == []:
                    # The current semantic authority was issued from Lean's
                    # exact expanded Spec/proof-pair graph for every selected
                    # v11 claim. Re-running one Meta program per pair is a
                    # derived reconstruction, not an independent proof check.
                    return findings

    if paper_closeout:
        return findings + [
            Finding(
                "ERROR",
                folder / "status.json",
                f"`{paper_id}` canonical closeout has no complete typed Lean "
                "semantic-contract graph; parser-discovered declarations and "
                "per-pair checks are diagnostic only",
            )
        ]

    try:
        from scripts.review_dashboard import (
            is_proposition_specification_manifest,
            parse_review_source_declarations,
            review_proof_module,
            review_source_file,
        )
        from scripts.lean_signature_manifest import run_lean_proposition_spec_proof_matches
        items = (
            review_items_provider()
            if review_items_provider is not None
            else strict_review_items_for_paper(
                folder,
                build_input_provider=(
                    run_context.build_input_provider
                    if run_context is not None
                    else None
                ),
                audit_inputs=(
                    run_context.dashboard_audit_inputs()
                    if run_context is not None
                    and run_context.evidence_context is not None
                    else None
                ),
            )
        )
    except Exception as exc:  # noqa: BLE001 - closeout evidence fails closed.
        return [
            Finding(
                "ERROR" if paper_closeout else completed_status_finding_severity(status),
                folder / "status.json",
                f"`{paper_id}` could not compute proposition-spec proof routes: {exc}",
            )
        ]

    by_name = {item.name: item for item in items}
    include_set = set(include_names)
    prop_specs = {
        name: item
        for name, item in by_name.items()
        if name in include_set
        and is_proposition_specification_manifest(item.lean_signature_manifest)
    }

    source_path = (
        review_surface_source_file_path(folder, review_surface)
        if run_context is not None and run_context.evidence_context is not None
        else review_source_file(folder)
    )
    proof_path = proof_endpoint_source_file_path(folder, review_surface)
    if proof_routes and not proof_path.is_file():
        return [
            Finding(
                "ERROR" if paper_closeout else completed_status_finding_severity(status),
                proof_path,
                f"`{paper_id}` configures Spec proof routes but its proof endpoint source is missing",
            )
        ]
    qualified_names: dict[str, str] = {}
    ambiguous_names: set[str] = set()
    if run_context is not None and run_context.evidence_context is not None:
        source_text = run_context.exact_lean_source_text(source_path)
        proof_text = run_context.exact_lean_source_text(proof_path)
        if source_text is None or (proof_routes and proof_text is None):
            return [
                Finding(
                    "ERROR",
                    source_path if source_text is None else proof_path,
                    f"`{paper_id}` proposition-spec routing source is absent from "
                    "the exact Lean import closure",
                )
            ]
        parsed_source_names: list[tuple[str, str]] = []
        parsed_sources = [(source_path, source_text)]
        if proof_path != source_path:
            parsed_sources.append((proof_path, proof_text))
        for path, text in parsed_sources:
            if text is None:
                continue
            declaration_blocks = (
                _legacy_review_surface_structure_module().review_declaration_blocks(
                    text
                )
            )
            namespace_stacks = namespace_stacks_at_lines(
                text,
                {line for line, _kind, _source in declaration_blocks.values()},
            )
            parsed_source_names.extend(
                (
                    name,
                    ".".join([*namespace_stacks.get(line, []), name])
                    if namespace_stacks.get(line)
                    else name,
                )
                for name, (line, _kind, _source) in declaration_blocks.items()
            )
    else:
        parsed_source_names = [
            (short_name, full_name)
            for _kind, short_name, full_name, *_rest in (
                parse_review_source_declarations(source_path)
            )
        ]
        if proof_routes and proof_path != source_path:
            parsed_source_names.extend(
                (short_name, full_name)
                for _kind, short_name, full_name, *_rest in (
                    parse_review_source_declarations(proof_path)
                )
            )
    for short_name, full_name in parsed_source_names:
        qualified_names[full_name] = full_name
        previous = qualified_names.get(short_name)
        if previous is not None and previous != full_name:
            ambiguous_names.add(short_name)
        else:
            qualified_names[short_name] = full_name
    for name in ambiguous_names:
        qualified_names.pop(name, None)

    requested_routes: dict[tuple[str, str], tuple[str, str]] = {}
    for spec_name, proof_name in proof_routes.items():
        if spec_name not in prop_specs:
            continue
        qualified_spec = qualified_names.get(spec_name)
        qualified_proof = qualified_names.get(proof_name)
        if qualified_spec and qualified_proof:
            requested_routes[(spec_name, proof_name)] = (
                qualified_spec,
                qualified_proof,
            )
    meta_matches: dict[tuple[str, str], bool] = {}
    if requested_routes:
        meta_matches = run_lean_proposition_spec_proof_matches(
            ROOT,
            review_proof_module(folder, source_path),
            list(requested_routes.values()),
            build_input_provider=(
                run_context.build_input_provider
                if run_context is not None
                else None
            ),
        )
    for configured in sorted(source_definition_names | set(proof_routes)):
        if configured not in prop_specs:
            findings.append(
                Finding(
                    "ERROR",
                    folder / "status.json",
                    f"`{paper_id}` proposition-spec routing names non-Prop or unconfigured row `{configured}`",
                )
            )

    severity = (
        "ERROR"
        if paper_closeout or status in {"formalized", "formalized with caveat"}
        else "WARN"
    )
    for name, spec_item in sorted(prop_specs.items()):
        if name in assumption_names:
            continue
        if name in source_definition_names:
            if not _certified_source_definition_item(
                folder,
                name,
                run_context=run_context,
            ):
                findings.append(
                    Finding(
                        severity,
                        folder / "status.json",
                        f"`{paper_id}` Prop specification `{name}` is labeled as a source definition "
                        "without pinned bytes, a distinct source curator/kind validator, and an "
                        "independent human-approved `source_kind: definition` item",
                    )
                )
            continue
        proof_name = proof_routes.get(name, "")
        if not proof_name:
            findings.append(
                Finding(
                    severity,
                    folder / "status.json",
                    f"`{paper_id}` configured `{spec_item.kind}` `{name}` is an unproved proposition "
                    "specification, not proof evidence; route a matching theorem in "
                    "`review_surface.proposition_spec_proofs` or classify a certified source definition",
                )
            )
            continue
        if proof_name not in qualified_names:
            findings.append(
                Finding(
                    severity,
                    folder / "status.json",
                    f"`{paper_id}` Prop specification `{name}` routes to missing proof endpoint `{proof_name}`",
                )
            )
            continue
        qualified_route = requested_routes.get((name, proof_name))
        if qualified_route is None or meta_matches.get(qualified_route) is not True:
            findings.append(
                Finding(
                    severity,
                    folder / "status.json",
                    f"`{paper_id}` Lean Meta did not establish that proof row `{proof_name}` "
                    f"has exactly the elaborated type of Prop specification `{name}`; "
                    "extra hypotheses, wrong conclusions, ambiguous routes, and unavailable "
                    "Meta results all fail closed",
                )
            )
    return findings


def check_machine_paper_status(
    library_premise_audit: bool = False,
    paper_filter: str | None = None,
    paper_closeout: bool = False,
    *,
    require_source_bytes: bool = True,
    deep_paper_prose: bool = False,
    prevalidated_strict_v11_occurrence_papers: set[str] | None = None,
    run_context: PaperCloseoutRunContext | None = None,
    phase_timings: MutableMapping[str, float] | None = None,
    phase_progress_callback: Callable[[Mapping[str, object]], None] | None = None,
) -> list[Finding]:
    findings: list[Finding] = []
    using_paper_local_fallback = False
    if paper_closeout and paper_filter is not None:
        # A named-theory paper closeout has one paper-local source of truth.
        # Aggregate status/rendering drift belongs to repository-hygiene or
        # release-preparation checks; it must not make a theorem/provenance
        # closeout depend on an unrelated global file.
        local_status = PAPERS / paper_filter / "status.json"
        if run_context is None and not local_status.exists():
            return [
                Finding(
                    "ERROR",
                    local_status,
                    "missing paper-local status source for paper closeout",
                )
            ]
        local_payload = (
            run_context.exact_json_payload(local_status)
            if run_context is not None
            else load_json_object(local_status)
        )
        if local_payload is None:
            return [
                Finding(
                    "ERROR",
                    local_status,
                    "paper-local status is unavailable from the exact closeout snapshot",
                )
            ]
        if not isinstance(local_payload, dict):
            return [Finding("ERROR", local_status, "paper-local status should be an object")]
        if local_payload.get("id") != paper_filter:
            return [
                Finding(
                    "ERROR",
                    local_status,
                    f"paper-local status id should be `{paper_filter}` for paper closeout",
                )
            ]
        papers = [local_payload]
        using_paper_local_fallback = True
    else:
        if not PAPER_STATUS_FILE.exists():
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, "missing machine-readable paper status file"))
            return findings

        try:
            data = json.loads(PAPER_STATUS_FILE.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"invalid JSON: {exc.msg}"))
            return findings

        if not schema_version_is_exact(data.get("schema"), 1):
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, "expected `schema: 1`"))

        papers = data.get("papers")
        if not isinstance(papers, list):
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, "`papers` should be a list"))
            return findings
        if paper_filter is not None:
            local_status = PAPERS / paper_filter / "status.json"
            if local_status.exists():
                try:
                    local_payload = json.loads(local_status.read_text(encoding="utf-8"))
                except json.JSONDecodeError as exc:
                    findings.append(Finding("ERROR", local_status, f"invalid JSON: {exc.msg}"))
                    local_payload = None
                if isinstance(local_payload, dict):
                    aggregate_entry = next(
                        (
                            entry
                            for entry in papers
                            if isinstance(entry, dict) and entry.get("id") == paper_filter
                        ),
                        None,
                    )
                    if aggregate_entry is not None and aggregate_entry != local_payload:
                        findings.append(
                            Finding(
                                "ERROR",
                                PAPER_STATUS_FILE,
                                f"`{paper_filter}` aggregate entry is out of sync with "
                                f"`{local_status.relative_to(ROOT)}`; paper-scoped audit uses the "
                                "paper-local source of truth",
                            )
                        )
                    papers = [local_payload]
                    using_paper_local_fallback = True

    known = (
        set()
        if using_paper_local_fallback
        else {folder.name for folder in paper_dirs()}
    )
    entries: dict[str, dict] = {}
    for idx, entry in enumerate(papers, start=1):
        if not isinstance(entry, dict):
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"paper entry {idx} should be an object"))
            continue
        paper_id = entry.get("id")
        if not isinstance(paper_id, str) or not paper_id:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"paper entry {idx} has missing `id`"))
            continue
        if paper_id in entries:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"duplicate paper status entry `{paper_id}`"))
        entries[paper_id] = entry
        if paper_filter is not None and paper_id != paper_filter:
            continue
        paper_run_context = (
            run_context
            if run_context is not None
            and run_context.paper_id == paper_id
            and run_context.folder == (PAPERS / paper_id).resolve()
            else (
                PaperCloseoutRunContext(paper_id, PAPERS / paper_id)
                if paper_closeout
                else None
            )
        )
        try:
            dashboard_audit_inputs = (
                paper_run_context.dashboard_audit_inputs()
                if paper_run_context is not None
                and paper_run_context.evidence_context is not None
                and not paper_run_context.selected_v11_closeout
                else None
            )
            validated_configured_review_rows = (
                paper_run_context.current_configured_review_rows_for_manifest_reuse()
                if paper_run_context is not None
                else None
            )
        except Exception as exc:  # noqa: BLE001 - exact-input acquisition fails closed.
            findings.append(
                Finding(
                    "ERROR",
                    PAPERS / paper_id / "status.json",
                    f"`{paper_id}` could not construct exact dashboard inputs: {exc}",
                )
            )
            continue
        review_items_provider = LazyStrictReviewItems(
            PAPERS / paper_id,
            build_input_provider=(
                paper_run_context.build_input_provider
                if paper_run_context is not None
                else None
            ),
            audit_inputs=dashboard_audit_inputs,
            validated_configured_review_rows=validated_configured_review_rows,
            semantic_reuse_authority=(
                getattr(
                    paper_run_context.evidence_context,
                    "semantic_reuse_authority",
                    None,
                )
                if paper_run_context is not None
                and paper_run_context.evidence_context is not None
                else None
            ),
        )

        paper_status_file = PAPERS / paper_id / "status.json"
        paper_status_payload = (
            paper_run_context.exact_json_payload(paper_status_file)
            if paper_run_context is not None
            else load_json_object(paper_status_file)
        )
        if paper_status_payload is None:
            findings.append(
                Finding(
                    "ERROR",
                    paper_status_file,
                    "paper-local status is unavailable from the exact closeout snapshot",
                )
            )
        if isinstance(paper_status_payload, dict) and paper_status_payload != entry:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` aggregate entry is out of sync with `{paper_status_file.relative_to(ROOT)}`",
                )
            )

        for field in ("title", "source_version", "build_target", "status", "review_entrypoint"):
            if not isinstance(entry.get(field), str) or not entry[field].strip():
                findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` has missing `{field}`"))

        status = entry.get("status")
        if isinstance(status, str) and status not in PAPER_STATUS_VALUES:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` has unexpected status `{status}`"))

        summary_review = entry.get("human_summary_review")
        if summary_review is not None:
            if not isinstance(summary_review, dict):
                findings.append(
                    Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}.human_summary_review` should be an object")
                )
            else:
                review_status = summary_review.get("status")
                if review_status not in HUMAN_SUMMARY_REVIEW_VALUES:
                    findings.append(
                        Finding(
                            "ERROR",
                            PAPER_STATUS_FILE,
                            f"`{paper_id}.human_summary_review.status` should be one of "
                            + ", ".join(sorted(HUMAN_SUMMARY_REVIEW_VALUES)),
                        )
                    )
                if review_status == "human_approved" and not isinstance(entry.get("human_summary"), str):
                    findings.append(
                        Finding(
                            "ERROR",
                            PAPER_STATUS_FILE,
                            f"`{paper_id}` has human-approved summary metadata but no `human_summary` string",
                        )
                    )

        review = entry.get("human_review")
        if not isinstance(review, dict):
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` has missing `human_review` object"))
        else:
            reviewed = review.get("reviewed_rows")
            total = review.get("total_rows")
            for field in ("reviewed_rows", "total_rows", "stale_rows", "mismatch_rows"):
                if not isinstance(review.get(field), int) or review[field] < 0:
                    findings.append(
                        Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}.human_review.{field}` should be a nonnegative integer")
                    )
            if isinstance(reviewed, int) and isinstance(total, int) and reviewed > total:
                findings.append(
                    Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` has reviewed_rows greater than total_rows")
                )

        interface = entry.get("paper_interface")
        if not isinstance(interface, dict):
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` has missing `paper_interface` object"))
            continue

        review_surface = entry.get("review_surface")
        if not isinstance(review_surface, dict):
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` has missing `review_surface` object"))
            review_surface = {}
        corrected_scope_evaluation = (
            paper_run_context.corrected_scope_evaluation(entry)
            if paper_run_context is not None
            else None
        )
        corrected_model_scope_current = (
            corrected_scope_evaluation[0]
            if corrected_scope_evaluation is not None
            else current_author_approved_corrected_scope(
                PAPERS / paper_id, entry
            )
        )
        include_names = review_surface.get("include_names")
        if not isinstance(include_names, list) or not all(isinstance(name, str) and name for name in include_names):
            findings.append(
                Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}.review_surface.include_names` should be a nonempty string list")
            )
            include_names = []
        assumption_names, assumption_name_problems = review_surface_assumption_names(review_surface)
        for problem in assumption_name_problems:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` {problem}"))
        proof_boundary_names, proof_boundary_name_problems = review_surface_proof_boundary_names(review_surface)
        for problem in proof_boundary_name_problems:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` {problem}"))
        missing_boundary_assumptions = proof_boundary_names - assumption_names
        if missing_boundary_assumptions:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` proof_boundary_names must also be listed in "
                    "`review_surface.assumption_names`: "
                    + ", ".join(sorted(missing_boundary_assumptions)),
                )
            )
        auxiliary_names, auxiliary_name_problems = review_surface_auxiliary_names(review_surface)
        for problem in auxiliary_name_problems:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` {problem}"))
        quarantined_auxiliary_names, quarantined_auxiliary_name_problems = (
            review_surface_quarantined_auxiliary_names(review_surface)
        )
        for problem in quarantined_auxiliary_name_problems:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` {problem}"))
        quarantine_not_auxiliary = quarantined_auxiliary_names - auxiliary_names
        if quarantine_not_auxiliary:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` quarantined_auxiliary_names must also be listed in "
                    "`review_surface.auxiliary_names`: "
                    + ", ".join(sorted(quarantine_not_auxiliary)),
                )
            )
        quarantine_review_overlap = quarantined_auxiliary_names.intersection(
            set(include_names)
        ).union(quarantined_auxiliary_names.intersection(assumption_names))
        if quarantine_review_overlap:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` quarantined_auxiliary_names overlap reviewed or "
                    "assumption declarations: "
                    + ", ".join(sorted(quarantine_review_overlap)),
                )
            )
        auxiliary_overlap = auxiliary_names.intersection(set(include_names)).union(
            auxiliary_names.intersection(assumption_names)
        )
        if auxiliary_overlap:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` auxiliary_names overlap reviewed or assumption declarations: "
                    + ", ".join(sorted(auxiliary_overlap)),
                )
            )
        assumption_policy = str(review_surface.get("assumption_policy") or "").strip().lower()
        strict_assumption_policy = assumption_policy in ASSUMPTION_POLICY_STRICT_VALUES
        if assumption_policy and assumption_policy not in ASSUMPTION_POLICY_ALLOWED_VALUES:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}.review_surface.assumption_policy` should be one of "
                    + ", ".join(sorted(ASSUMPTION_POLICY_ALLOWED_VALUES)),
                )
            )

        path_value = interface.get("path")
        if not isinstance(path_value, str) or not path_value:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}.paper_interface.path` is missing"))
            continue
        configured_interface_path = Path(path_value)
        if not configured_interface_path.is_absolute():
            configured_interface_path = ROOT / configured_interface_path
        canonical_interface_path = PAPERS / paper_id / "PaperInterface.lean"
        if configured_interface_path.resolve() != canonical_interface_path.resolve():
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}.paper_interface.path` must point to "
                    f"`{canonical_interface_path.relative_to(ROOT)}`, got `{path_value}`",
                )
            )
        audit_surface_value = interface.get("audit_surface_path")
        if isinstance(audit_surface_value, str) and audit_surface_value.strip():
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}.paper_interface.audit_surface_path` is obsolete; "
                    "the review surface must be `PaperInterface.lean` for every paper",
                )
            )

        interface_path = configured_interface_path
        interface_text = (
            paper_run_context.exact_lean_source_text(interface_path)
            if paper_run_context is not None
            else None
        )
        if paper_run_context is None:
            try:
                interface_text = interface_path.read_text(encoding="utf-8")
            except OSError:
                interface_text = None
        if interface_text is None:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` interface path is absent from the exact Lean "
                    f"source snapshot: `{path_value}`",
                )
            )
            continue

        actual_line_count = len(interface_text.splitlines())
        review_source_path = review_surface_source_file_path(PAPERS / paper_id, review_surface)
        review_source_is_interface = (
            review_source_path.resolve() == interface_path.resolve()
        )
        review_source_text = (
            interface_text
            if review_source_is_interface
            else (
                paper_run_context.exact_lean_source_text(review_source_path)
                if paper_run_context is not None
                else None
            )
        )
        if paper_run_context is None and not review_source_is_interface:
            try:
                review_source_text = review_source_path.read_text(encoding="utf-8")
            except OSError:
                review_source_text = None
        if review_source_text is None:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` review surface source file is absent from the "
                    "exact Lean source snapshot: "
                    f"`{review_source_path.relative_to(ROOT)}`",
                )
            )
            continue
        if not review_source_is_interface:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` routes review rows through "
                    f"`{review_source_path.relative_to(ROOT)}`; "
                    "`review_surface.source_file` must be `PaperInterface.lean`. "
                    "Use imported implementation modules such as `AuditInterface.lean` only behind "
                    "paper-facing statement blocks declared in `PaperInterface.lean`.",
                )
            )
        findings.extend(
            run_machine_paper_status_phase(
                MachinePaperStatusPhase.STATEMENT_SIDECAR,
                paper_id,
                lambda: paper_statement_sidecar_findings(
                    paper_id,
                    PAPERS / paper_id,
                    status,
                    presentation_hygiene=deep_paper_prose,
                    review_items_provider=review_items_provider,
                    corrected_scope_evaluation=corrected_scope_evaluation,
                    status_payload_override=entry,
                    run_context=paper_run_context,
                ),
                timings=phase_timings,
                progress_callback=phase_progress_callback,
            )
        )
        declaration_index = (
            paper_run_context.paper_declaration_index()
            if paper_run_context is not None
            else paper_lean_declaration_index(PAPERS / paper_id)
        )
        uses_v11_lean_declaration_surface = bool(
            paper_run_context is not None
            and paper_run_context.selected_v11_closeout
        )
        native_review_declarations = (
            tuple(
                declaration
                for declaration in unique_declarations(declaration_index)
                if declaration.path.resolve() == review_source_path.resolve()
            )
            if uses_v11_lean_declaration_surface
            else ()
        )
        actual_review_names = (
            [declaration.name for declaration in native_review_declarations]
            if uses_v11_lean_declaration_surface
            else [
                name
                for _line, name in (
                    _legacy_review_surface_structure_module()
                    .review_rows_from_interface_text(review_source_text)
                )
            ]
        )
        assumption_source_file = assumption_source_file_path(PAPERS / paper_id, review_surface)
        assumption_source_text = (
            paper_run_context.exact_lean_source_text(assumption_source_file)
            if paper_run_context is not None
            else None
        )
        if paper_run_context is None:
            try:
                assumption_source_text = assumption_source_file.read_text(
                    encoding="utf-8"
                )
            except OSError:
                assumption_source_text = None
        if uses_v11_lean_declaration_surface:
            configured_assumption_declarations: dict[
                str, tuple[int, str, str]
            ] = {}
            for configured_name in sorted(assumption_names.union(auxiliary_names)):
                resolved = [
                    declaration
                    for declaration in resolve_declaration_name(
                        declaration_index, configured_name
                    )
                    if declaration.path.resolve() == assumption_source_file.resolve()
                ]
                if len(resolved) == 1:
                    declaration = resolved[0]
                    configured_assumption_declarations[configured_name] = (
                        declaration.line,
                        declaration.kind,
                        declaration.source,
                    )
        else:
            configured_assumption_declarations = (
                _legacy_review_surface_structure_module()
                .assumption_declarations_from_text(
                    assumption_source_text or "",
                    assumption_names.union(auxiliary_names),
                )
            )
        configured_assumption_auxiliary_names = auxiliary_names.intersection(
            configured_assumption_declarations
        )
        # In the current graph-native lane, auxiliary_names is retained only
        # as historical/presentation metadata. Lean's selected claim and
        # prerequisite graph is the complete semantic authority, so a stale
        # implementation-helper label must not reopen the paper or become an
        # extra review obligation merely because it once appeared in this
        # legacy list. Historical lanes still require every configured
        # auxiliary to resolve through their declared structural surfaces.
        missing_auxiliary_exports = (
            []
            if uses_v11_lean_declaration_surface
            else auxiliary_names_not_exported_from_review_source(
                auxiliary_names,
                actual_review_names,
                configured_assumption_auxiliary_names,
            )
        )
        if missing_auxiliary_exports:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` review_surface.auxiliary_names contains names not "
                    f"declared or exported by PaperInterface.lean and not declared in "
                    f"the configured Assumptions.lean support surface: "
                    + ", ".join(missing_auxiliary_exports[:8])
                    + ("; ..." if len(missing_auxiliary_exports) > 8 else "")
                    + ". Keep implementation-only helpers outside these two "
                    "configured structural surfaces out of `review_surface`.",
                )
            )
        if (
            not uses_v11_lean_declaration_surface
            and review_source_is_interface
            and zero_row_review_surface_imports_paper_module(
                paper_id,
                review_source_text,
                actual_review_names,
            )
        ):
            findings.append(
                Finding(
                    "ERROR",
                    review_source_path,
                    f"`{paper_id}` has a zero-row `PaperInterface.lean` that imports a "
                    "paper-local module. Empty review surfaces must be genuinely empty; "
                    "put proof/build imports in the top-level paper module or an "
                    "implementation module outside the human review surface.",
                )
            )
        declaration_blocks = (
            {
                declaration.name: (
                    declaration.line,
                    declaration.kind,
                    declaration.source,
                )
                for declaration in native_review_declarations
            }
            if uses_v11_lean_declaration_surface
            else _legacy_review_surface_structure_module().review_declaration_blocks(
                review_source_text
            )
        )
        exported_only_review_names = reviewed_names_not_declared_in_review_source(
            include_names,
            declaration_blocks,
        )
        if review_source_is_interface and exported_only_review_names:
            findings.append(
                Finding(
                    "ERROR",
                    review_source_path,
                    f"`{paper_id}` review_surface.include_names contains row(s) "
                    "that are exported or imported but not declared in "
                    "`PaperInterface.lean`: "
                    + ", ".join(exported_only_review_names[:8])
                    + ("; ..." if len(exported_only_review_names) > 8 else "")
                    + ". Move each audited paper-facing statement block into "
                    "`PaperInterface.lean`; proofs may still delegate to "
                    "`MainTheorems.lean`, `AuditInterface.lean`, or other "
                    "implementation modules.",
                )
            )
        declaration_comments = (
            review_declaration_comments(review_source_text)
            if deep_paper_prose and not uses_v11_lean_declaration_surface
            else {}
        )
        assumption_declarations = {
            name: declaration
            for name, declaration in configured_assumption_declarations.items()
            if name in assumption_names
        }
        assumption_file_premises = (
            {}
            if uses_v11_lean_declaration_surface
            else assumption_premises_from_text(
                assumption_source_text or "", assumption_names
            )
        )
        assumption_judgments: dict[str, dict[str, object]] = {}
        validated_assumption_premises: set[str] = set()
        validated_assumption_premise_types: set[str] = set()
        accepted_conditional_boundary_rows = (
            set()
            if status in {"formalized", "formalized with caveat"}
            else current_statement_conditional_boundary_rows(
                PAPERS / paper_id,
                review_items_provider=review_items_provider,
                run_context=paper_run_context,
            )
        )
        hidden_premise_finding_keys: set[tuple[Path, int, str, str, tuple[str, ...]]] = set()
        hidden_premise_severity = assumption_finding_severity(strict_assumption_policy, status)
        corrected_model_premise_bridge = current_corrected_model_premise_bridge(
            PAPERS / paper_id,
            entry,
            run_context=paper_run_context,
        )
        source_record_model_record_bindings: dict[
            str, tuple[tuple[frozenset[str], str], ...]
        ] = {}
        corrected_target_rows = (
            corrected_scope_target_row_names(
                PAPERS / paper_id,
                entry,
                run_context=paper_run_context,
            )
            if corrected_model_scope_current
            else set()
        )

        def add_hidden_premise_finding(
            declaration: LeanDeclaration,
            hidden: list[str],
            context: str,
            row_name: str | None = None,
        ) -> None:
            if row_name and row_name in accepted_conditional_boundary_rows:
                return
            hidden = list(dict.fromkeys(
                premise
                for premise in hidden
                if normalize_premise_text(premise) not in validated_assumption_premises
                and premise_type_text(premise) not in validated_assumption_premise_types
                and not premise_is_current_corrected_model_contract_input(
                    premise,
                    declaration,
                    corrected_model_premise_bridge,
                    declaration_index,
                )
                and not premise_matches_current_model_record_binding(
                    premise, declaration, source_record_model_record_bindings
                )
            ))
            if not hidden:
                return
            key = (declaration.path, declaration.line, declaration.name, context, tuple(hidden))
            if key in hidden_premise_finding_keys:
                return
            hidden_premise_finding_keys.add(key)
            findings.append(
                Finding(
                    hidden_premise_severity,
                    declaration.path,
                    f"`{paper_id}` {context} `{declaration.name}` at line {declaration.line} "
                    "has premises not routed through explicit Assumptions.lean paper assumptions: "
                    + "; ".join(hidden[:4])
                    + ("; ..." if len(hidden) > 4 else ""),
                )
            )

        recorded_line_count = interface.get("line_count")
        if recorded_line_count != actual_line_count:
            findings.append(
                Finding(
                    "WARN",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` display line_count is {recorded_line_count}, "
                    f"currently {actual_line_count}; refresh generated status before release",
                )
            )
        declared_assumption_names = set(actual_review_names) | set(assumption_declarations)
        missing_assumption_rows = assumption_names - declared_assumption_names
        if missing_assumption_rows:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` assumption_names are not exported by the review surface or "
                    f"{assumption_source_file.relative_to(ROOT)}: "
                    + ", ".join(sorted(missing_assumption_rows)),
                )
            )
        if assumption_names and assumption_source_text is None and not any(
            name in actual_review_names for name in assumption_names
        ):
            findings.append(
                Finding(
                    "ERROR" if strict_assumption_policy else "WARN",
                    assumption_source_file,
                    f"`{paper_id}` lists assumptions but has no `{DEFAULT_ASSUMPTION_SOURCE_FILE}` "
                    "or legacy PaperInterface assumption declarations",
                )
            )
        findings.extend(
            run_machine_paper_status_phase(
                MachinePaperStatusPhase.INTERFACE_AXIOM_CLOSURE,
                paper_id,
                lambda: (
                    current_v11_direct_axiom_closure_findings(
                        paper_id,
                        PAPERS / paper_id,
                        review_surface,
                        include_names,
                        proof_boundary_names,
                        run_context=paper_run_context,
                    )
                    if paper_run_context is not None
                    and paper_run_context.selected_v11_closeout
                    else check_paper_interface_axiom_closure(
                        paper_id,
                        review_source_path,
                        review_source_text,
                        include_names,
                        declaration_blocks,
                        status,
                        proof_boundary_names,
                    )
                ),
                timings=phase_timings,
                progress_callback=phase_progress_callback,
            )
        )
        findings.extend(
            run_machine_paper_status_phase(
                MachinePaperStatusPhase.PROPOSITION_SPEC_ROUTES,
                paper_id,
                lambda: check_proposition_spec_routes(
                    paper_id,
                    PAPERS / paper_id,
                    review_surface,
                    include_names,
                    assumption_names,
                    status,
                    paper_closeout=paper_closeout,
                    review_items_provider=review_items_provider,
                    run_context=paper_run_context,
                ),
                timings=phase_timings,
                progress_callback=phase_progress_callback,
            )
        )
        if isinstance(status, str):
            findings.extend(
                run_machine_paper_status_phase(
                    MachinePaperStatusPhase.SOURCE_PROOF_FIDELITY,
                    paper_id,
                    lambda: check_source_proof_fidelity(
                        PAPERS / paper_id,
                        status,
                        entry,
                        require_source_bytes=require_source_bytes,
                        run_context=paper_run_context,
                    ),
                    timings=phase_timings,
                    progress_callback=phase_progress_callback,
                )
            )
            if not (
                paper_run_context is not None
                and paper_run_context.selected_v11_closeout
            ):
                findings.extend(
                    run_machine_paper_status_phase(
                        MachinePaperStatusPhase.EXPLICIT_SEMANTIC_MODEL,
                        paper_id,
                        lambda: check_explicit_source_route_semantic_model_evidence(
                            PAPERS / paper_id,
                            status,
                            entry,
                            run_context=paper_run_context,
                        ),
                        timings=phase_timings,
                        progress_callback=phase_progress_callback,
                    )
                )
        source_record_findings = run_machine_paper_status_phase(
            MachinePaperStatusPhase.SOURCE_RECORD,
            paper_id,
            lambda: check_source_record_audit(
                paper_id,
                PAPERS / paper_id,
                review_surface,
                status,
                strict_assumption_policy,
                paper_closeout=paper_closeout,
                prevalidated_strict_v11_occurrence_papers=(
                    prevalidated_strict_v11_occurrence_papers
                ),
                run_context=paper_run_context,
            ),
            timings=phase_timings,
            progress_callback=phase_progress_callback,
        )
        findings.extend(source_record_findings)
        semantic_hidden_premise_surface: (
            CurrentNamedTheorySemanticReviewSurface | None
        ) = None
        if not any(finding.severity == "ERROR" for finding in source_record_findings):
            # `check_source_record_audit` has reused the transaction's current,
            # byte-pinned source record. Its zero-error result is the exact
            # elaborated-signature freshness precondition for the narrower
            # FQN/source-byte projection below.
            for premise in source_record_validated_boundary_premises(
                paper_id,
                PAPERS / paper_id,
                review_surface,
                status,
                run_context=paper_run_context,
            ):
                validated_assumption_premises.add(normalize_premise_text(premise))
                validated_assumption_premise_types.add(premise_type_text(premise))
            source_record_model_record_bindings = (
                source_record_complete_model_record_bindings(
                    paper_id,
                    PAPERS / paper_id,
                    review_surface,
                    status,
                    run_context=paper_run_context,
                )
            )
            (
                semantic_hidden_premise_surface,
                semantic_surface_error,
            ) = current_named_theory_semantic_review_surface(
                PAPERS / paper_id,
                entry,
                declaration_index,
                run_context=paper_run_context,
            )
            if semantic_surface_error:
                # Do not let a missing, stale, or ambiguous receipt make the
                # normal hidden-premise scan smaller.  The broad scan remains
                # active because the surface stays `None`.
                semantic_hidden_premise_surface = None
                findings.append(
                    Finding(
                        "ERROR",
                        source_record_audit_file_path(
                            PAPERS / paper_id, review_surface
                        ),
                        f"`{paper_id}` cannot safely project normal named-theory "
                        "hidden-premise auditing onto semantic-model rows: "
                        + semantic_surface_error
                        + ". Retained the complete PaperInterface audit surface.",
                    )
                )
        if assumption_names and not corrected_model_scope_current:
            assumption_judge_file = assumption_judgment_file_path(interface_path.parent, review_surface)
            assumption_judgment_payload = (
                paper_run_context.exact_json_payload(assumption_judge_file)
                if paper_run_context is not None
                else load_json_object(assumption_judge_file)
            )
            if assumption_judgment_payload is None:
                findings.append(
                    Finding(
                        "ERROR" if strict_assumption_policy else "WARN",
                        assumption_judge_file,
                        f"`{paper_id}` has explicit paper assumptions but no assumption-provenance LLM judge file",
                    )
                )
                assumption_judgments = {}
            else:
                assumption_judgments = assumption_judgments_from_payload(
                    assumption_judgment_payload, paper_id
                )
                if not assumption_judgments:
                    findings.append(
                        Finding(
                            "ERROR" if strict_assumption_policy else "WARN",
                            assumption_judge_file,
                            f"`{paper_id}` assumption judge file is missing schema-1 judgments",
                        )
                    )
            for assumption_name in sorted(assumption_names):
                judgment = assumption_judgments.get(assumption_name, {}).get("judgment", "")
                if judgment not in APPROVED_ASSUMPTION_JUDGMENTS:
                    findings.append(
                        Finding(
                            "ERROR" if strict_assumption_policy else "WARN",
                            assumption_judge_file,
                            f"`{paper_id}` assumption `{assumption_name}` lacks a current "
                            "`paper_assumption`, `paper_condition`, "
                            "`documented_additional_assumption`, `documented_caveat`, "
                            "or `partial_boundary` "
                            "LLM provenance judgment",
                        )
                    )
                else:
                    if judgment in {
                        "documented_additional_assumption",
                        "partial_boundary",
                    } and status in {"formalized", "formalized with caveat"}:
                        findings.append(
                            Finding(
                                "ERROR",
                                assumption_judge_file,
                                f"`{paper_id}` assumption `{assumption_name}` is marked "
                                f"`{judgment}`, which requires partial status rather than "
                                f"full-closeout status `{status}`",
                            )
                        )
                    premise_judgments = assumption_judgments.get(assumption_name, {}).get(
                        "premise_judgments", {}
                    )
                    if not isinstance(premise_judgments, dict):
                        premise_judgments = {}
                    expected_premises = {
                        normalize_premise_text(premise)
                        for premise in assumption_file_premises.get(assumption_name, set())
                    }
                    judged_premises = {
                        normalize_premise_text(premise)
                        for premise in premise_judgments
                        if normalize_premise_text(premise)
                    }
                    missing_premise_judgments = sorted(expected_premises - judged_premises)
                    if missing_premise_judgments:
                        findings.append(
                            Finding(
                                "ERROR" if strict_assumption_policy else "WARN",
                                assumption_judge_file,
                                f"`{paper_id}` assumption `{assumption_name}` lacks per-premise "
                                "source-text judgments for: "
                                + "; ".join(missing_premise_judgments[:4])
                                + ("; ..." if len(missing_premise_judgments) > 4 else ""),
                            )
                        )
                    extra_premise_judgments = sorted(judged_premises - expected_premises)
                    if extra_premise_judgments:
                        findings.append(
                            Finding(
                                "WARN",
                                assumption_judge_file,
                                f"`{paper_id}` assumption `{assumption_name}` has per-premise "
                                "judgments that do not match current Assumptions.lean premises: "
                                + "; ".join(extra_premise_judgments[:4])
                                + ("; ..." if len(extra_premise_judgments) > 4 else ""),
                            )
                        )
                    for premise in sorted(expected_premises & judged_premises):
                        raw_premise_judgment = premise_judgments.get(premise)
                        if raw_premise_judgment is None:
                            for key, value in premise_judgments.items():
                                if normalize_premise_text(key) == premise:
                                    raw_premise_judgment = value
                                    break
                        if not isinstance(raw_premise_judgment, dict):
                            premise_judgment = normalize_assumption_judgment(raw_premise_judgment)
                            source_location = ""
                        else:
                            premise_judgment = normalize_assumption_judgment(
                                raw_premise_judgment.get("judgment")
                                or raw_premise_judgment.get("verdict")
                                or raw_premise_judgment.get("status")
                            )
                            source_location = str(raw_premise_judgment.get("source_location") or "").strip()
                        if premise_judgment not in APPROVED_ASSUMPTION_PREMISE_JUDGMENTS:
                            findings.append(
                                Finding(
                                    "ERROR" if strict_assumption_policy else "WARN",
                                    assumption_judge_file,
                                    f"`{paper_id}` assumption `{assumption_name}` premise `{premise}` "
                                    f"has non-source or unresolved judgment `{premise_judgment or 'missing'}`",
                                )
                            )
                            continue
                        if premise_judgment in {
                            "documented_additional_assumption",
                            "partial_boundary",
                        }:
                            findings.append(
                                Finding(
                                    "ERROR" if status in {"formalized", "formalized with caveat"} else "WARN",
                                    assumption_judge_file,
                                    f"`{paper_id}` assumption `{assumption_name}` premise `{premise}` "
                                    f"is `{premise_judgment}` and therefore a "
                                    "partial-formalization boundary, not a source-text assumption",
                                )
                            )
                            if status not in {"formalized", "formalized with caveat"}:
                                validated_assumption_premises.add(premise)
                                validated_assumption_premise_types.add(premise_type_text(premise))
                            continue
                        if premise_judgment in {
                            "paper_assumption",
                            "paper_condition",
                            "source_text",
                            "source_text_model_primitive",
                        } and not source_location:
                            findings.append(
                                Finding(
                                    "ERROR" if strict_assumption_policy else "WARN",
                                    assumption_judge_file,
                                    f"`{paper_id}` assumption `{assumption_name}` premise `{premise}` "
                                    "needs a source_location for its source-text judgment",
                                )
                            )
                            continue
                        validated_assumption_premises.add(premise)
                        validated_assumption_premise_types.add(premise_type_text(premise))
        elif strict_assumption_policy and not corrected_model_scope_current:
            llm_assumption_review = review_surface.get("llm_assumption_review")
            if not isinstance(llm_assumption_review, dict):
                findings.append(
                    Finding(
                        "WARN",
                        PAPER_STATUS_FILE,
                        f"`{paper_id}` strict assumption policy should declare "
                        "`review_surface.llm_assumption_review` even when there are no assumptions",
                    )
                )
        # The current v10 source-record lane classifies every direct
        # proof-like input from its instantiated type. The older expanded-cache
        # scan below is a useful diagnostic, but it classifies some binders by
        # spelling/type-word heuristics and therefore cannot be a default
        # semantic closeout gate.
        expanded_review_statements = (
            load_expanded_review_statements(PAPERS / paper_id)
            if deep_paper_prose and not uses_v11_lean_declaration_surface
            else {}
        )
        for name, (expanded_statement, expanded_line) in expanded_review_statements.items():
            if name in assumption_names:
                continue
            expanded_boundary_premises = expanded_statement_boundary_premises(
                expanded_statement,
                assumption_names,
            )
            if not expanded_boundary_premises:
                continue
            declaration = declaration_blocks.get(name)
            if declaration:
                line_no, kind, source = declaration
                expanded_declaration = LeanDeclaration(
                    path=review_source_path,
                    line=line_no,
                    kind=kind,
                    name=name,
                    source=source,
                )
                if not declaration_is_on_current_named_theory_semantic_review_surface(
                    expanded_declaration,
                    semantic_hidden_premise_surface,
                ):
                    continue
            else:
                line_no = expanded_line or 1
                kind = "abbrev"
                source = expanded_statement
                # An expanded cache row that no longer has a concrete local
                # declaration cannot be safely identity-filtered. Retain it.
                expanded_declaration = LeanDeclaration(
                    path=review_source_path,
                    line=line_no,
                    kind=kind,
                    name=name,
                    source=source,
                )
            add_hidden_premise_finding(
                expanded_declaration,
                expanded_boundary_premises,
                "expanded review row",
                row_name=name,
            )
        # The current v11 path has already reviewed Lean's complete emitted
        # parameter/assumption/conclusion atom surface against the verbatim
        # source and checked every material paper/library prerequisite.  Do not
        # reparse those same declaration types with the older textual binder
        # heuristics. Legacy protocols retain that diagnostic below.
        hidden_premise_review_names = (
            () if uses_v11_lean_declaration_surface else include_names
        )
        for name in hidden_premise_review_names:
            declaration = declaration_blocks.get(name)
            if not declaration:
                continue
            line_no, kind, source = declaration
            row_declaration = LeanDeclaration(
                path=review_source_path,
                line=line_no,
                kind=kind,
                name=name,
                source=source,
            )
            # Presentation checks are intentionally opt-in. Named-theory
            # closeout is driven by the source-record's source presentation,
            # exact FQN, source bytes, and elaborated signature pins; it must
            # not change when a Lean row is renamed or a prose comment is
            # reformatted.
            leading_comment = (
                declaration_comments.get(name, "") if deep_paper_prose else ""
            )
            comment_and_name = f"{leading_comment}\n{name}"
            numbered_result_row = bool(
                deep_paper_prose
                and (
                    NUMBERED_SOURCE_RESULT_RE.search(leading_comment)
                    or NUMBERED_SOURCE_NAME_RE.search(name)
                )
            )
            broad_review_row = bool(
                deep_paper_prose and BROAD_REVIEW_ROW_NAME_RE.search(name)
            )
            formula_specific_row = bool(
                deep_paper_prose and FORMULA_SPECIFIC_NAME_RE.search(name)
            )
            definition_review_row = bool(
                deep_paper_prose
                and re.match(r"^definition[A-Z0-9_]", name, re.I)
            )
            formula_facing_row = bool(
                deep_paper_prose
                and not definition_review_row
                and (SOURCE_FORMULA_TEXT_RE.search(leading_comment) or formula_specific_row)
            )
            if (
                numbered_result_row
                and broad_review_row
                and not formula_specific_row
                and name not in corrected_target_rows
                and not declaration_has_current_individual_direct_source_route(
                    row_declaration,
                    semantic_hidden_premise_surface,
                )
            ):
                findings.append(
                    Finding(
                        completed_status_finding_severity(status),
                        review_source_path,
                        f"`{paper_id}` review row `{name}` at line {line_no} appears to summarize a "
                        "numbered source result with a broad aggregate name; split displayed formulas, "
                        "subclaims, and source-defining equations into exact paper-facing rows before "
                        "claiming the result is fully formalized",
                    )
                )
            if formula_facing_row and leading_comment and not SOURCE_STATUS_LINE_RE.search(leading_comment):
                findings.append(
                    Finding(
                        completed_status_finding_severity(status),
                        review_source_path,
                        f"`{paper_id}` formula-bearing review row `{name}` at line {line_no} "
                        "has no `Source status:` provenance line in its paper-facing comment",
                    )
                )
            if (
                formula_facing_row
                and is_signature_only_review_alias(kind, source)
                and not formula_specific_row
            ):
                findings.append(
                    Finding(
                        completed_status_finding_severity(status),
                        review_source_path,
                        f"`{paper_id}` formula-bearing review row `{name}` at line {line_no} is an "
                        "opaque alias/signature; expose the displayed formula or theorem subclaim "
                        "directly, or route any non-derived premise through Assumptions.lean",
                    )
                )
            if formula_facing_row and re.search(r"source[-_ ]rows?", comment_and_name, re.I):
                findings.append(
                    Finding(
                        completed_status_finding_severity(status),
                        review_source_path,
                        f"`{paper_id}` review row `{name}` at line {line_no} mentions a source-row "
                        "formula boundary; source-row wrappers are partial endpoints unless derived "
                        "from primitives or validated as explicit paper assumptions",
                    )
            )
            if (
                deep_paper_prose
                and kind in {"theorem", "lemma", "def", "abbrev"}
                and name not in assumption_names
            ):
                if declaration_is_on_current_named_theory_semantic_review_surface(
                    row_declaration,
                    semantic_hidden_premise_surface,
                ):
                    visible_premises = {
                        normalize_premise_text(premise)
                        for premise in hidden_premise_binders(source, assumption_names)
                    }
                    visible_statement_premises = {
                        premise
                        for premise in visible_premises
                        if not explicit_boundary_premises([premise])
                    }
                    direct_boundary_premises = explicit_boundary_premises(
                        sorted(visible_premises)
                    )
                    if direct_boundary_premises:
                        add_hidden_premise_finding(
                            row_declaration,
                            direct_boundary_premises,
                            "review row",
                            row_name=name,
                        )
                    alias_targets = resolve_paper_local_alias_chain(
                        declaration_index, source
                    )
                    for target_declaration in alias_targets:
                        if target_declaration.name in assumption_names:
                            continue
                        target_hidden = explicit_boundary_premises(
                            [
                                premise
                                for premise in hidden_premise_binders(
                                    target_declaration.source, assumption_names
                                )
                                if normalize_premise_text(premise)
                                not in visible_statement_premises
                            ]
                        )
                        if target_hidden:
                            add_hidden_premise_finding(
                                target_declaration,
                                target_hidden,
                                f"review row `{name}` resolves to",
                                row_name=name,
                            )
            if not deep_paper_prose or not is_signature_only_review_alias(kind, source):
                continue
            candidates = source_equation_wrapper_candidates(name, set(declaration_blocks))
            if candidates:
                findings.append(
                    Finding(
                        "ERROR",
                        review_source_path,
                        f"`{paper_id}` review row `{name}` at line {line_no} is an opaque signature/alias; "
                        f"use source-equation wrapper `{candidates[0]}` in `status.json` `review_surface.include_names`",
                    )
                )
        total_rows = review.get("total_rows") if isinstance(review, dict) else None
        review_rows = interface.get("review_rows")
        source_claim_surface = (
            isinstance(review, dict)
            and review.get("surface") == "source_claims_v1"
        ) or v11_source_claim_review_names(entry) is not None
        graph_native_human_total: int | None = None
        if source_claim_surface:
            source_map_path = PAPERS / paper_id / PAPER_AUDIT_DIR / "paper_statement_map.json"
            source_map_payload = (
                paper_run_context.exact_json_payload(source_map_path)
                if paper_run_context is not None
                else load_json_object(source_map_path)
            )
            if source_map_payload is not None:
                try:
                    graph_native_human_total = (
                        graph_native_human_review_total_from_payload(
                            source_map_payload,
                            entry,
                        )
                    )
                except CloseoutStatusProjectionError as exc:
                    findings.append(
                        Finding(
                            "ERROR",
                            PAPER_STATUS_FILE,
                            f"`{paper_id}` graph-native human-review selection is invalid: {exc}",
                        )
                    )
        source_condition_rows = len(assumption_names)
        if (
            isinstance(total_rows, int)
            and isinstance(review_rows, int)
            and review_rows != total_rows
            and review_rows + source_condition_rows != total_rows
            and not source_claim_surface
        ):
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` review_rows plus source-condition rows should match human_review.total_rows",
                )
            )
        configured_review_surface_names = set(include_names).union(assumption_names)
        valid_review_totals = {len(set(include_names)), len(configured_review_surface_names)}
        if graph_native_human_total is not None:
            valid_review_totals = {graph_native_human_total}
        if source_claim_surface and graph_native_human_total is None:
            paired_specs = review_surface.get("proposition_spec_proofs", {})
            if isinstance(paired_specs, dict):
                valid_review_totals.update(
                    {
                        len(paired_specs),
                        len(paired_specs) + source_condition_rows,
                    }
                )
            slices = review_surface.get("slices", [])
            if isinstance(slices, list):
                sliced_claim_names = {
                    name.strip()
                    for raw_slice in slices
                    if isinstance(raw_slice, dict)
                    for name in raw_slice.get("names", [])
                    if isinstance(name, str)
                    and name.strip()
                    and name.strip() in set(include_names)
                }
                if sliced_claim_names:
                    valid_review_totals.update(
                        {
                            len(sliced_claim_names),
                            len(sliced_claim_names) + source_condition_rows,
                        }
                    )
        if isinstance(total_rows, int) and include_names and total_rows not in valid_review_totals:
            findings.append(
                Finding(
                    "WARN" if graph_native_human_total is not None else "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` human_review.total_rows should be the typed source-graph "
                    f"denominator {graph_native_human_total}"
                    if graph_native_human_total is not None
                    else f"`{paper_id}` human_review.total_rows should count either PaperInterface "
                    "review rows, paired source claims, or those rows plus separately tracked source conditions",
                )
            )
        missing_review_names = set(include_names) - set(actual_review_names)
        if missing_review_names:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` status names are not exported by the review surface: "
                    + ", ".join(sorted(missing_review_names)),
                )
            )
        missing_auxiliary_names = set(missing_auxiliary_exports)
        if missing_auxiliary_names:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` auxiliary_names are neither exported by "
                    "PaperInterface.lean nor declared in the configured "
                    "Assumptions.lean support surface: "
                    + ", ".join(sorted(missing_auxiliary_names)),
                )
            )
        unclassified_review_names = (
            set(actual_review_names) - set(include_names) - assumption_names - auxiliary_names
        )
        # A v11 source-claim surface explicitly selects its one semantic Spec
        # per paper claim. Other declarations in the same module are ordinary
        # transparent vocabulary or proof-facing helpers; their file location
        # does not turn them into additional human-review rows. Completeness is
        # enforced from the source inventory and material-prerequisite ledgers.
        if unclassified_review_names and not source_claim_surface:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` review-surface declarations are neither reviewed, "
                    "assumptions, nor explicit auxiliary proof-facing rows: "
                    + ", ".join(sorted(unclassified_review_names)),
                )
            )

        oversized = interface.get("oversized")
        if not isinstance(oversized, bool):
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}.paper_interface.oversized` should be boolean"))
        elif actual_line_count > PAPER_INTERFACE_OVERSIZED_LINE_THRESHOLD and not oversized:
            findings.append(
                Finding(
                    "ERROR",
                    PAPER_STATUS_FILE,
                    f"`{paper_id}` PaperInterface.lean has {actual_line_count} lines but is not marked oversized",
                )
            )
        elif oversized and not interface.get("maintainability_issue"):
            findings.append(
                Finding("ERROR", PAPER_STATUS_FILE, f"`{paper_id}` oversized interface should include maintainability_issue")
            )

    if not using_paper_local_fallback:
        missing = known - set(entries)
        extra = set(entries) - known
        if missing:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"missing paper status entries: {', '.join(sorted(missing))}"))
        if extra:
            findings.append(Finding("ERROR", PAPER_STATUS_FILE, f"unknown paper status entries: {', '.join(sorted(extra))}"))

    return findings


def check_root_status_table() -> list[Finding]:
    findings: list[Finding] = []
    readme = ROOT / "README.md"
    for header, rows in iter_markdown_tables(readme):
        if "Paper folder" not in header or "Overall status" not in header:
            continue
        status_idx = header.index("Overall status")
        folder_idx = header.index("Paper folder")
        seen = set()
        for row in rows:
            if len(row) <= max(status_idx, folder_idx):
                continue
            folder = row[folder_idx].strip("`")
            seen.add(Path(folder).name)
            status = row[status_idx]
            if status not in ROOT_STATUS_VALUES:
                findings.append(Finding("ERROR", readme, f"unexpected root status `{status}` for `{folder}`"))
        missing = {p.name for p in paper_dirs()} - seen
        if missing:
            findings.append(Finding("ERROR", readme, f"missing root status rows: {', '.join(sorted(missing))}"))
    return findings


def check_status_label_vocabulary() -> list[Finding]:
    findings: list[Finding] = []
    paths = [
        ROOT / "README.md",
        ROOT / "docs" / "PAPER_STATUS.md",
        ROOT / "docs" / "ECONCSLEAN_CURRENT_STATUS.md",
        ROOT / "docs" / "GARG_AUTHOR_FORMALIZATION_REPORT.md",
        ROOT / "site" / "index.html",
    ]
    for folder in paper_dirs(include_template=True):
        paths.append(
            paper_relative_file(folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md")
        )
    for path in paths:
        if not path.exists():
            continue
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if FORBIDDEN_STATUS_LABEL_RE.search(line):
                findings.append(
                    Finding(
                        "ERROR",
                        path,
                        f"legacy `Verified` status label at line {line_no}; use `Formalized` or `Formalized with caveat`",
                    )
                )
    return findings


def check_generated_human_status_labels() -> list[Finding]:
    findings: list[Finding] = []
    if not HUMAN_STATUS_FILE.exists():
        return findings
    try:
        data = json.loads(HUMAN_STATUS_FILE.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return [Finding("ERROR", HUMAN_STATUS_FILE, f"invalid JSON: {exc.msg}")]
    papers = data.get("papers")
    if not isinstance(papers, list):
        return findings
    for idx, entry in enumerate(papers, start=1):
        if not isinstance(entry, dict):
            continue
        paper_id = str(entry.get("id") or f"row {idx}")
        label = str(entry.get("llm_as_judge_translation") or "")
        if re.search(r"\badditional assumptions?\b", label, re.I):
            findings.append(
                Finding(
                    "ERROR",
                    HUMAN_STATUS_FILE,
                    f"`{paper_id}.llm_as_judge_translation` should describe statement translation/boundary rows, not additional assumptions",
                )
            )
        human_match = re.fullmatch(r"\d+/(\d+)", str(entry.get("human_review") or "").strip())
        llm_match = re.search(r"\b\d+/(\d+)(?: statement rows)? match\b", label)
        if human_match and llm_match:
            human_total = int(human_match.group(1))
            statement_total = int(llm_match.group(1))
            source_total = sum(
                int(match.group(1))
                for match in re.finditer(r"\b(\d+) source-condition rows?\b", label)
            )
            if statement_total + source_total != human_total:
                findings.append(
                    Finding(
                        "ERROR",
                        HUMAN_STATUS_FILE,
                        f"`{paper_id}.llm_as_judge_translation` covers {statement_total + source_total} row(s), "
                        f"but human_review covers {human_total}",
                    )
                )
    return findings


def check_readme_status_tables(
    include_active: bool,
    paper_filter: str | None = None,
) -> list[Finding]:
    findings: list[Finding] = []
    suspicious_caveat = re.compile(
        r"\b(open|conditional|caveat|mismatch|bug|not formalized|not covered)\b",
        re.I,
    )
    for folder in paper_dirs():
        if paper_filter and folder.name != paper_filter:
            continue
        if folder.name in ACTIVE_PAPERS and not include_active:
            continue
        readme = folder / "README.md"
        if not readme.exists():
            continue
        readme_text = readme.read_text(encoding="utf-8")
        found_status_table = False
        for header, rows in iter_markdown_tables(readme):
            normalized = [h.lower() for h in header]
            if "status" not in normalized:
                continue
            found_status_table = True
            status_idx = normalized.index("status")
            decl_idx = normalized.index("lean declaration") if "lean declaration" in normalized else None
            file_idx = normalized.index("file") if "file" in normalized else None
            rem_idx = next(
                (idx for idx, h in enumerate(normalized) if "remaining" in h or "mismatch" in h),
                None,
            )
            for row in rows:
                if len(row) <= status_idx:
                    continue
                status_raw = row[status_idx].strip()
                status = status_raw.lower()
                decl = row[decl_idx].lower() if decl_idx is not None and len(row) > decl_idx else ""
                file_cell = row[file_idx].lower() if file_idx is not None and len(row) > file_idx else ""
                remaining = row[rem_idx] if rem_idx is not None and len(row) > rem_idx else ""

                if status not in PAPER_STATUS_VALUES:
                    findings.append(
                        Finding(
                            "ERROR",
                            readme,
                            f"unexpected paper status `{status_raw}` for `{row[0]}`; see docs/STATUS.md",
                        )
                    )

                has_none_decl = decl in {"none", "`none`"} or "none matching" in decl
                has_none_file = file_cell in {"none", "`none`"}
                if has_none_decl and not any(marker in status for marker in ("not", "open", "started")):
                    findings.append(
                        Finding("ERROR", readme, f"row has declaration `none` but status `{row[status_idx]}`")
                    )
                exact_formalized = status.strip() == "formalized"
                if exact_formalized and has_none_file:
                    findings.append(
                        Finding("ERROR", readme, f"formalized row points to file `none`: `{row[0]}`")
                    )
                remaining_normalized = remaining.strip().strip("`").lower()
                if exact_formalized and not remaining_normalized.startswith("none"):
                    findings.append(
                        Finding(
                            "WARN",
                            readme,
                            f"`formalized` row should use remaining assumptions `None`: `{row[0]}`",
                        )
                    )
                if exact_formalized and suspicious_caveat.search(remaining):
                    findings.append(
                        Finding("WARN", readme, f"`formalized` row has caveat-like text: `{row[0]}`")
                    )
        if not found_status_table:
            if "<!-- BEGIN GENERATED PAPER FOLDER README -->" in readme_text:
                fields: dict[str, str] = {}
                for header, rows in iter_markdown_tables(readme):
                    normalized = [h.strip().lower() for h in header]
                    if normalized != ["field", "value"]:
                        continue
                    for row in rows:
                        if len(row) >= 2:
                            fields[row[0].strip()] = row[1].strip()
                required = ["Final status", "Paper reference", "Lines of Code"]
                for field in required:
                    if not fields.get(field):
                        findings.append(Finding("ERROR", readme, f"generated README missing `{field}` field"))
                status = fields.get("Final status", "").lower()
                if status and status not in PAPER_STATUS_VALUES:
                    findings.append(
                        Finding(
                            "ERROR",
                            readme,
                            f"unexpected generated README final status `{fields.get('Final status')}`; see docs/STATUS.md",
                        )
                    )
                loc = fields.get("Lines of Code", "")
                if loc and not re.fullmatch(r"\d{1,3}(?:,\d{3})*|\d+", loc):
                    findings.append(Finding("ERROR", readme, f"generated README has invalid Lines of Code `{loc}`"))
                if status == "paper draft":
                    review_link = (
                        "Agent source audit",
                        r"Agent source audit:\s+\[[^\]]+\]\(docs/AGENT_SOURCE_AUDIT\.md\)",
                    )
                else:
                    review_link = (
                        "Final validation report",
                        r"Final validation report:\s+\[[^\]]+\]\(FINAL_VALIDATION_REPORT\.md\)",
                    )
                required_links = [
                    review_link,
                    (
                        "Dependency DAG",
                        r"Dependency DAG:\s+\[[^\]]+\]\(docs/DependencyDAG\.pdf\)",
                    ),
                    ("status.json", r"\[status\.json\]\(status\.json\)"),
                ]
                for label, pattern in required_links:
                    if not re.search(pattern, readme_text):
                        findings.append(Finding("ERROR", readme, f"generated README missing `{label}` link"))
                continue
            findings.append(Finding("ERROR", readme, "no theorem/status markdown table found"))
    if not paper_filter:
        findings.extend(check_root_status_table())
    return findings


def check_tracked_artifacts(include_active: bool) -> list[Finding]:
    findings: list[Finding] = []
    artifact_re = re.compile(r"DependencyDAG\.(aux|fdb_latexmk|fls|log)$")
    for rel in git_ls_files():
        path = Path(rel)
        full_path = ROOT / path
        if not full_path.exists():
            continue
        if len(path.parts) < 3 or path.parts[0] != "papers":
            continue
        paper = path.parts[1]
        if paper in ACTIVE_PAPERS and not include_active:
            continue
        if artifact_re.search(path.name):
            findings.append(Finding("ERROR", full_path, "tracked LaTeX build artifact"))
        if path.parts[2:] == ("docs", "FINAL_VALIDATION_REPORT.md"):
            findings.append(
                Finding(
                    "ERROR",
                    full_path,
                    "legacy validation-report alias; link to the paper-root `FINAL_VALIDATION_REPORT.md`",
                )
            )
        if path.parts[2:] == ("DependencyDAG.pdf",):
            findings.append(
                Finding(
                    "ERROR",
                    full_path,
                    "legacy root-level DAG alias; link to `docs/DependencyDAG.pdf`",
                )
            )
        if (
            path.suffix == ".pdf"
            and path.name not in ALLOWED_TRACKED_PAPER_PDFS
            and not is_declared_tracked_pdf_artifact(path)
        ):
            findings.append(Finding("ERROR", full_path, "tracked PDF artifact; source PDFs should stay ignored"))
    return findings


def check_stale_architecture_terms() -> list[Finding]:
    findings: list[Finding] = []
    stale_re = re.compile(r"\bDecisionCore\b")
    paths = [
        ROOT / "README.md",
        ROOT / "docs" / "ARCHITECTURE.md",
        ROOT / "docs" / "ECONCSLEAN_CURRENT_STATUS.md",
        ROOT / "skills" / "econcs-formalizer" / "SKILL.md",
    ]
    paths.extend(sorted((ROOT / "skills" / "econcs-formalizer" / "references").glob("*.md")))
    for path in paths:
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        for line_no, line in enumerate(text.splitlines(), start=1):
            if stale_re.search(line):
                findings.append(
                    Finding(
                        "WARN",
                        path,
                        f"stale architecture term `DecisionCore` at line {line_no}; use current `AppliedModelingLib` layering",
                    )
                )
    return findings


def check_human_facing_readme() -> list[Finding]:
    findings: list[Finding] = []
    readme = ROOT / "README.md"
    docs_index = ROOT / "docs" / "README.md"

    if not readme.exists():
        findings.append(Finding("ERROR", readme, "top-level human-facing README is missing"))
        return findings

    text = readme.read_text(encoding="utf-8")
    lines = text.splitlines()

    if len(lines) > README_MAX_LINES:
        findings.append(
            Finding(
                "WARN",
                readme,
                f"top-level README has {len(lines)} lines; keep it short and human-facing",
            )
        )

    if README_OLD_STATUS_TABLE_RE.search(text):
        findings.append(
            Finding(
                "ERROR",
                readme,
                "top-level README should link to the project website and docs status pages instead of embedding a paper-status table",
            )
        )

    if not docs_index.exists():
        findings.append(Finding("ERROR", docs_index, "docs index is missing"))
    else:
        docs_text = docs_index.read_text(encoding="utf-8")
        headings = {
            match.group(1).strip().casefold()
            for match in re.finditer(r"(?m)^##\s+(.+?)\s*$", docs_text)
        }
        reader_sections = {"human-facing", "reading and reviewing a formalization"}
        maintainer_sections = {"agent and maintainer-facing", "maintaining the website and releases"}
        if not headings.intersection(reader_sections) or not headings.intersection(maintainer_sections):
            findings.append(
                Finding(
                    "ERROR",
                    docs_index,
                    "docs index should split human-facing docs from agent/maintainer-facing docs",
                )
            )

    return findings


def has_module_docstring_with_main_declarations(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    match = re.search(r"/-!.*?-/", text, re.S)
    return bool(match and "## Main declarations" in match.group(0))


def check_strict_lean_style() -> list[Finding]:
    findings: list[Finding] = []
    for path in sorted((ROOT / "AppliedModelingLib").rglob("*.lean")):
        if not has_module_docstring_with_main_declarations(path):
            findings.append(
                Finding(
                    "WARN",
                    path,
                    "new reusable modules should have a module docstring with `## Main declarations`",
                )
            )
    return findings


def check_library_certificate_boundaries() -> list[Finding]:
    """List reusable-library APIs that require explicit certificates/boundaries.

    These are not errors by themselves. Library theorems may and often should
    require source-shaped certificates. The important invariant is that a paper
    wrapper cannot be marked fully formalized while leaving such a certificate
    to its caller unless that certificate is a validated paper assumption.
    """

    findings: list[Finding] = []
    seen: set[tuple[Path, int, str]] = set()
    declaration_index = library_lean_declaration_index()
    for declaration in unique_declarations(declaration_index):
        key = declaration_key(declaration)
        if key in seen:
            continue
        seen.add(key)
        if re.match(r"\s*private\s+", declaration.source):
            continue
        boundaries = library_boundary_binders(declaration.source)
        if boundaries:
            samples = [f"{category}: {premise}" for category, premise in boundaries[:4]]
            findings.append(
                Finding(
                    "INFO",
                    declaration.path,
                    f"library `{declaration.name}` at line {declaration.line} exposes "
                    "certificate/source-boundary parameter(s): "
                    + "; ".join(samples)
                    + ("; ..." if len(boundaries) > 4 else "")
                    + ". Paper wrappers must construct these certificates or remain conditional/partial.",
                )
            )
        smells = source_specific_library_smells(declaration)
        if smells:
            findings.append(
                Finding(
                    "INFO",
                    declaration.path,
                    f"library `{declaration.name}` at line {declaration.line} is source-shaped "
                    "inside reusable code: "
                    + "; ".join(smells)
                    + ". Prefer a generic API whose source formulas/certificates are explicit inputs "
                    "or move the paper-specific formula into the paper folder.",
                )
            )
    return sorted(findings, key=lambda finding: (str(finding.path), finding.message))


def check_library_source_hygiene() -> list[Finding]:
    """Fail reusable code that appears to bake a paper/source formula into API names."""

    findings: list[Finding] = []
    seen: set[tuple[Path, int, str]] = set()
    for declaration in unique_declarations(library_lean_declaration_index()):
        key = declaration_key(declaration)
        if key in seen:
            continue
        seen.add(key)
        if re.match(r"\s*private\s+", declaration.source):
            continue
        smells = source_specific_library_smells(declaration)
        if not smells:
            continue
        findings.append(
            Finding(
                "ERROR",
                declaration.path,
                f"library `{declaration.name}` at line {declaration.line} is source-shaped "
                "inside reusable code: "
                + "; ".join(smells)
                + ". Rename it to a paper-neutral API, make the source formula an explicit "
                "certificate parameter, or move the paper-specific formula into the paper folder.",
            )
        )
    return sorted(findings, key=lambda finding: (str(finding.path), finding.message))


def known_paper_source_terms() -> set[str]:
    """Return paper IDs and citation prefixes discovered from paper folders."""

    terms: set[str] = set()
    if not PAPERS.exists():
        return terms
    for folder in PAPERS.iterdir():
        if not folder.is_dir() or folder.name == "TEMPLATE":
            continue
        if not PAPER_FOLDER_NAME_RE.fullmatch(folder.name):
            continue
        terms.add(folder.name)
        match = re.match(r"^([A-Z][A-Za-z]*)(\d{2})", folder.name)
        if not match:
            continue
        author_prefix = match.group(1)
        year_prefix = f"{author_prefix}{match.group(2)}"
        if len(author_prefix) >= 3:
            terms.add(author_prefix)
        terms.add(year_prefix)
    return terms - GENERIC_SOURCE_HYGIENE_ALLOWED_TERMS


def generic_source_hygiene_paths(*, library_only: bool) -> list[Path]:
    """Return reusable files that should not contain concrete paper references."""

    roots: list[Path] = [ROOT / "AppliedModelingLib"]
    if not library_only:
        roots.extend(
            [
                ROOT / "scripts",
                ROOT / "docs" / "AGENT_FORMALIZATION_WORKFLOW.md",
                ROOT / "docs" / "LIBRARY_PROVENANCE.md",
                ROOT / "docs" / "THEOREM_ERGONOMICS.md",
                ROOT / "docs" / "REVIEW_DASHBOARD.md",
                ROOT / "docs" / "NEW_CONTRIBUTOR_WORKFLOW.md",
                ROOT / "skills" / "econcs-formalizer" / "SKILL.md",
            ]
        )

    paths: set[Path] = set()
    for root in roots:
        if root.is_dir():
            for path in root.rglob("*"):
                if path.suffix in {".lean", ".py", ".md"} and path.is_file():
                    paths.add(path)
        elif root.is_file() and root.suffix in {".lean", ".py", ".md"}:
            paths.add(root)
    return sorted(paths)


def check_generic_source_reference_hygiene(*, library_only: bool = False) -> list[Finding]:
    """Reject concrete paper IDs/theorem-number labels in reusable code.

    The check is data-driven: paper IDs and citation prefixes are discovered from
    `papers/` folder names, while allowed domain/algorithm terms live in
    `papers/audit_config.json`.
    """

    findings: list[Finding] = []
    terms = known_paper_source_terms()
    term_re = None
    if terms:
        term_re = re.compile(
            r"\b(?:"
            + "|".join(re.escape(term) for term in sorted(terms, key=len, reverse=True))
            + r")\b"
        )

    for path in generic_source_hygiene_paths(library_only=library_only):
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            continue
        for line_no, line in enumerate(lines, start=1):
            if term_re is not None and (match := term_re.search(line)):
                findings.append(
                    Finding(
                        "ERROR",
                        path,
                        f"generic code/doc line {line_no} mentions paper-specific term "
                        f"`{match.group(0)}`; move citation/display metadata to paper-local "
                        "files or data config, or use a paper-neutral domain name",
                    )
                )
            if path.suffix == ".lean" and "AppliedModelingLib" in path.parts:
                if match := GENERIC_SOURCE_THEOREM_LABEL_RE.search(line):
                    findings.append(
                        Finding(
                            "ERROR",
                            path,
                            f"generic Lean comment/source line {line_no} mentions paper "
                            f"numbered label `{match.group(0)}`; theorem numbering belongs "
                            "in paper-local interfaces and validation reports",
                        )
                    )
    return sorted(findings, key=lambda finding: (str(finding.path), finding.message))


def run_library(
    strict_style: bool,
    library_premise_audit: bool = False,
) -> list[Finding]:
    return execute_registered_checks(
        reusable_library_checks(
            sys.modules[__name__],
            files=library_lean_files(),
            strict_style=strict_style,
            library_premise_audit=library_premise_audit,
        )
    )


def check_root_readme_policy() -> list[Finding]:
    return [
        Finding("ERROR", ROOT / "README.md", message)
        for message in validate_root_readme()
    ]


def paper_closeout_evidence_integrity_findings(
    paper_id: str,
    *,
    require_source_bytes: bool,
    context: object | None = None,
    diagnostics: MutableMapping[str, int] | None = None,
) -> list[Finding]:
    """Run the focused evidence gate inside the closeout process.

    Keeping this lane in-process lets it reuse the exact, mutation-guarded
    source-record and Lean manifest snapshots already validated by the primary
    paper gate. Standalone evidence commands remain useful diagnostics, but
    are not an additional mandatory closeout pass.
    """

    from scripts.audit_evidence_integrity import (
        run as run_evidence_integrity_finalized,
        run_for_consolidated_closeout_transaction as run_evidence_integrity_deferred,
    )

    run_evidence_integrity = (
        run_evidence_integrity_deferred
        if context is not None
        else run_evidence_integrity_finalized
    )

    converted: list[Finding] = []
    for finding in run_evidence_integrity(
        paper_id,
        False,
        False,
        require_source_bytes=require_source_bytes,
        context=context,
        diagnostics=diagnostics,
    ):
        path = Path(finding.path)
        if not path.is_absolute():
            path = ROOT / path
        converted.append(
            Finding(
                finding.severity,
                path,
                f"`{paper_id}` evidence integrity: {finding.message}",
            )
        )
    return converted


def paper_closeout_fast_route_schema_findings(
    paper_id: str,
    *,
    context: object | None = None,
) -> list[Finding]:
    """Reject route/configuration defects from frozen inputs before Lean work.

    This reader is only for an actual historical transaction. Current callers
    use current_closeout.primary_gate_transaction directly.
    """

    from scripts.evidence_run_context import V11EvidenceRunContext

    from scripts.audit_evidence_integrity import source_spec_correspondence_inventory_findings
    from scripts.source_manifest_validation import repaired_source_defect_route_preflight_findings

    folder = PAPERS / paper_id
    if context is not None:
        context_folder = getattr(context, "folder", None)
        if (
            isinstance(context, V11EvidenceRunContext)
            or not exact_evidence_run_context(context)
            or not isinstance(context_folder, Path)
            or context_folder != folder.resolve()
        ):
            return [
                Finding(
                    "ERROR",
                    folder / "status.json",
                    f"`{paper_id}` route-schema preflight requires its exact "
                    "builder-issued historical evidence transaction",
                )
            ]
        status = str(getattr(context, "status", "") or "").strip()
    else:
        status_payload = load_json_object(folder / "status.json") or {}
        status = str(status_payload.get("status") or "").strip()
    raw_findings = source_spec_correspondence_inventory_findings(
        folder,
        status,
        require_source_bytes=False,
        context=context,
    )
    raw_findings.extend(
        repaired_source_defect_route_preflight_findings(
            folder,
            status,
            context=context,
        )
    )
    converted: list[Finding] = []
    seen: set[tuple[str, str, str]] = set()
    for finding in raw_findings:
        path = Path(finding.path)
        if not path.is_absolute():
            path = ROOT / path
        key = (str(finding.severity), str(path), str(finding.message))
        if key in seen:
            continue
        seen.add(key)
        converted.append(
            Finding(
                str(finding.severity),
                path,
                f"`{paper_id}` route-schema preflight: {finding.message}",
            )
        )
    return converted


def build_paper_closeout_evidence_context(
    paper_id: str,
    *,
    diagnostics: MutableMapping[str, int] | None = None,
    operational_plan_receipt: Mapping[str, object] | None = None,
) -> object:
    """Acquire the one exact evidence transaction shared by all closeout lanes."""

    from scripts.current_closeout.evidence_transaction import (
        CurrentV11EvidenceSnapshotRoot,
    )

    graph_reference = (
        operational_plan_receipt.get("v11_lean_review_graph")
        if isinstance(operational_plan_receipt, Mapping)
        else None
    )
    current_root = CurrentV11EvidenceSnapshotRoot.acquire(
        PAPERS / paper_id,
        repository_root=ROOT,
    )
    if current_root.v11_selected:
        return current_root.build_v11(
            graph_reference if isinstance(graph_reference, Mapping) else None
        )

    from scripts.audit_evidence_integrity import build_evidence_run_context

    return build_evidence_run_context(
        PAPERS / paper_id,
        diagnostics=diagnostics,
        v11_lean_review_graph_reference=None,
    )


def paper_closeout_v11_direct_semantic_review_state(
    paper_id: str,
    folder: Path,
    evidence_context: object,
) -> tuple[bool, str]:
    """Validate the exact replacement lane before adopting legacy build inputs."""

    from scripts.current_closeout.semantic_review import (
        current_v11_direct_semantic_review_state,
    )

    try:
        return current_v11_direct_semantic_review_state(
            ROOT,
            folder,
            context=evidence_context,
        )
    except (OSError, RuntimeError, ValueError) as exc:
        return False, str(exc)


def paper_closeout_v11_lean_review_surface(
    folder: Path,
    evidence_context: object,
) -> object | None:
    """Reuse the exact graph already constructed by the v11 semantic gate.

    The graph is retained independently of the final semantic verdict so a
    stale or incomplete judgment is reported as that v11 finding rather than
    being masked by a fallback to superseded legacy source ownership.
    """

    from scripts.current_closeout.review_surface import (
        builder_issued_v11_lean_review_surface,
    )

    return builder_issued_v11_lean_review_surface(folder, evidence_context)


def paper_closeout_source_record_transaction_skew_findings(
    paper_id: str,
    evidence_context: object,
) -> list[Finding]:
    """Stop before derived checks when raw source-record and map snapshots disagree.

    A source-record raw audit is a transaction over the statement map, source
    artifacts, and Lean surface.  When its recorded map hash disagrees with
    the exact map snapshot *and* the existing freshness validator has rejected
    that raw audit, every downstream source-record, correspondence, and
    theorem-realization error is derivative.  Report the single transaction
    failure before entering those lanes.  This is deliberately a read-only
    preflight: it cannot refresh raw evidence or alter any human judgment.
    """

    legacy_state = getattr(evidence_context, "legacy_source_record_state", None)
    if legacy_state is None:
        return []
    legacy_inputs = getattr(legacy_state, "inputs", None)
    audit_snapshot = getattr(legacy_inputs, "audit_snapshot", None)
    audit_payload = getattr(audit_snapshot, "payload", None)
    raw_map_sha = (
        str(audit_payload.get("paper_statement_map_sha256") or "")
        .strip()
        .lower()
        if isinstance(audit_payload, Mapping)
        else ""
    )
    exact_map_sha = str(
        getattr(evidence_context, "paper_statement_map_sha256", "") or ""
    ).strip().lower()
    identity_error = str(
        getattr(legacy_state, "source_record_identity_error", "") or ""
    ).strip()
    if not (
        re.fullmatch(r"[0-9a-f]{64}", raw_map_sha)
        and re.fullmatch(r"[0-9a-f]{64}", exact_map_sha)
        and raw_map_sha != exact_map_sha
        and identity_error
    ):
        return []

    audit_path = getattr(audit_snapshot, "path", None)
    if not isinstance(audit_path, Path):
        audit_path = PAPERS / paper_id / DEFAULT_SOURCE_RECORD_AUDIT_FILE
    return [
        Finding(
            "ERROR",
            audit_path,
            f"`{paper_id}` closeout stopped before derived validation: the saved "
            "source-record raw audit is bound to source-map SHA "
            f"`{raw_map_sha[:12]}`, while this exact closeout transaction holds "
            f"`{exact_map_sha[:12]}`. Existing source-record freshness validation "
            f"rejects the snapshot: {identity_error}. Regenerate the raw "
            "source-record audit only after the statement map is finalized, then "
            "rerun closeout; this guard does not issue or revise human review "
            "receipts.",
        )
    ]


def paper_closeout_evidence_context_prebuild_findings(
    paper_id: str,
    evidence_context: object,
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> list[Finding]:
    """Reject a known-invalid exact raw context before compiling the paper.

    The evidence transaction has already frozen and validated the raw
    source-record receipt.  Its currentness verdict is therefore a
    deterministic closeout input, rather than a result that could be repaired
    by compiling Lean.  Keep the more specific map-skew explanation when it
    applies, then fail closed on every other identity-invalid raw receipt
    before paying for the focused paper-root build.  An absent raw sidecar has
    no builder-issued identity verdict, so its existing primary-gate handling
    remains unchanged.
    """

    # Lane ownership and lane success are different facts.  Once the exact
    # transaction selects v11, legacy source-record files are deliberately not
    # acquired and can never serve as fallback evidence.  A current v11 lane
    # proceeds; a failed one stops here with its actual semantic error before
    # the focused build or any legacy consumer can manufacture derivative
    # missing-sidecar/fingerprint findings.
    if (
        run_context is not None
        and run_context.evidence_context is evidence_context
        and run_context.selected_v11_closeout
    ):
        if run_context.current_v11_closeout:
            return []
        detail = str(run_context.v11_direct_semantic_review_error or "").strip()
        return [
            Finding(
                "ERROR",
                PAPERS / paper_id / "status.json",
                f"`{paper_id}` selected v11 semantic lane is not current: "
                + (detail or "the exact v11 semantic gate did not pass")
                + ". Repair the selected v11 evidence; the superseded legacy "
                "source-record lane is not fallback acceptance evidence.",
            )
        ]

    skew_findings = paper_closeout_source_record_transaction_skew_findings(
        paper_id, evidence_context
    )
    if skew_findings:
        return skew_findings

    legacy_state = getattr(evidence_context, "legacy_source_record_state", None)
    if legacy_state is None:
        return []
    legacy_inputs = getattr(legacy_state, "inputs", None)
    audit_snapshot = getattr(legacy_inputs, "audit_snapshot", None)
    audit_path = getattr(audit_snapshot, "path", None)
    if not isinstance(audit_path, Path):
        audit_path = PAPERS / paper_id / DEFAULT_SOURCE_RECORD_AUDIT_FILE

    identity_error = str(
        getattr(legacy_state, "source_record_identity_error", "") or ""
    ).strip()
    if not identity_error:
        return []
    detail = "the exact source-record identity is invalid: " + identity_error

    return [
        Finding(
            "ERROR",
            audit_path,
            f"`{paper_id}` closeout stopped before focused Lean build because "
            + detail
            + ". Repair or regenerate the raw source-record receipt from the "
            "finalized paper inputs, then rerun closeout; this guard does not "
            "issue or revise human review receipts.",
        )
    ]


def paper_closeout_context_mutation_findings(
    context: object,
    *,
    diagnostics: MutableMapping[str, int] | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> list[Finding]:
    """Convert both exact transaction owners' final mutation verdicts."""

    from scripts.audit_evidence_integrity import (
        evidence_run_context_mutation_findings,
    )

    converted: list[Finding] = []
    for finding in evidence_run_context_mutation_findings(
        context, diagnostics=diagnostics
    ):
        path = Path(finding.path)
        if not path.is_absolute():
            path = ROOT / path
        converted.append(
            Finding(
                finding.severity,
                path,
                f"`{finding.paper}` evidence transaction: {finding.message}",
            )
        )
    if (
        build_input_provider is not None
        and not build_input_provider.finalize_unchanged()
    ):
        converted.append(
            Finding(
                "ERROR",
                ROOT / "lean-toolchain",
                "repository Lean build/import inputs changed during the paper "
                "closeout transaction; discard every manifest-derived result",
            )
        )
    return converted


def _load_conclusion_provenance_auditors() -> tuple[Callable[..., object], Callable[..., object]]:
    """Load the historical/raw conclusion engine only after current-v11 misses.

    The accepted v11 path already owns a runtime-only capability for the exact
    source, semantic, Lean-graph, realization, and axiom checks performed by
    the primary gate.  Importing the historical aggregate engine merely to
    rediscover that capability eagerly loads its raw-receipt implementation.
    Keep the complete auditors available for every nonaccepting or legacy
    route, but outside current-v11 startup.
    """

    from scripts.audit_conclusion_provenance import (
        audit_paper,
        audit_paper_for_consolidated_closeout_transaction,
    )

    return audit_paper, audit_paper_for_consolidated_closeout_transaction


def paper_closeout_conclusion_provenance_findings(
    paper_id: str,
    *,
    theorem_realization_component_prevalidated: bool = False,
    context: object | None = None,
) -> list[Finding]:
    """Run conclusion provenance against the same closeout snapshot."""

    if context is not None and theorem_realization_component_prevalidated:
        from scripts.audit_evidence_integrity import (
            has_current_v11_evidence_integrity_receipt,
        )

        if has_current_v11_evidence_integrity_receipt(context):
            # The unforgeable in-process capability proves that the current
            # v11 primary and evidence gates checked the complete conclusion
            # graph and its exact source/evidence inventory.
            # There is no second conclusion obligation in the superseded raw
            # carrier, so do not import that carrier's audit implementation.
            return []

    audit_paper, audit_paper_for_consolidated_closeout_transaction = (
        _load_conclusion_provenance_auditors()
    )

    if context is not None:
        audit_findings = audit_paper_for_consolidated_closeout_transaction(
            paper_id,
            evidence_context=context,
            theorem_realization_component_prevalidated=(
                theorem_realization_component_prevalidated
            ),
        )
    else:
        audit_findings = audit_paper(
            paper_id,
            theorem_realization_component_prevalidated=(
                theorem_realization_component_prevalidated
            ),
        )
    converted: list[Finding] = []
    for finding in audit_findings:
        fields = (
            f" fields={','.join(finding.fields)}" if finding.fields else ""
        )
        converted.append(
            Finding(
                "ERROR",
                PAPERS / paper_id / "PaperInterface.lean",
                f"`{paper_id}` conclusion provenance row `{finding.row}`, "
                f"binder `{finding.binder}`{fields}: {finding.message}",
            )
        )
    return converted


def closeout_transaction_input_sha256(
    run_context: PaperCloseoutRunContext | None,
) -> str:
    """Identify exact already-acquired closeout inputs without another live read.

    This digest is operational trace data, not a reusable acceptance receipt.
    It lets an operator distinguish a completed run from an older result after
    losing the command's output stream.
    """

    if run_context is None or run_context.evidence_context is None:
        return ""
    evidence_context = run_context.evidence_context
    raw_snapshots = getattr(evidence_context, "input_snapshots", None)
    if not isinstance(raw_snapshots, (tuple, list)):
        return ""
    snapshots: list[dict[str, object]] = []
    for snapshot in raw_snapshots:
        path = getattr(snapshot, "path", None)
        if not isinstance(path, Path):
            continue
        try:
            relative = str(path.resolve().relative_to(ROOT.resolve()))
        except (OSError, RuntimeError, ValueError):
            relative = str(path)
        snapshots.append(
            {
                "path": relative,
                "sha256": getattr(snapshot, "sha256", None),
            }
        )
    material = {
        "schema": 1,
        "paper": run_context.paper_id,
        "watched_input_digest": str(
            getattr(evidence_context, "watched_input_digest", "") or ""
        ),
        "json_snapshots": sorted(snapshots, key=lambda item: str(item["path"])),
    }
    return hashlib.sha256(
        json.dumps(
            material,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def check_paper_root_build_closeout(paper_id: str) -> list[Finding]:
    """Require one focused paper-root compilation before strict closeout.

    The command is an in-process operational gate, not a serializable proof
    receipt.  The subsequent strict audit remains responsible for the
    semantic, source, and final-mutation checks.  Running this only after the
    source-record transaction preflight prevents a stale raw/map pair from
    paying for an unrelated compilation.
    """

    try:
        proc = subprocess.run(
            ["env", "LEAN_NUM_THREADS=1", "lake", "build", f"+{paper_id}"],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=900,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return [
            Finding(
                "ERROR",
                PAPERS / paper_id / "PaperInterface.lean",
                f"`{paper_id}` focused paper-root build could not run: {exc}",
            )
        ]
    diagnostic_failure = lean_diagnostic_failure_reason(proc.stdout, proc.stderr)
    if proc.returncode == 0 and not diagnostic_failure:
        return []
    excerpt = bounded_lean_diagnostic_excerpt(proc.stdout, proc.stderr)
    if diagnostic_failure:
        reason = diagnostic_failure
    else:
        reason = f"Lake exited {proc.returncode}"
    if excerpt:
        reason += f": {excerpt}"
    return [
        Finding(
            "ERROR",
            PAPERS / paper_id / "PaperInterface.lean",
            f"`{paper_id}` focused paper-root build failed: {reason}",
        )
    ]


def run(
    include_active: bool,
    strict_style: bool,
    library_premise_audit: bool = False,
    paper_filter: str | None = None,
    paper_closeout: bool = False,
    require_source_bytes: bool = True,
    deep_paper_prose: bool = False,
    closeout_trace: MutableMapping[str, object] | None = None,
    closeout_progress_callback: Callable[[Mapping[str, object]], None] | None = None,
    operational_plan_identity: str = "",
    operational_plan_receipt: Mapping[str, object] | None = None,
) -> list[Finding]:
    if paper_closeout:
        from scripts.paper_closeout_executor import execute_paper_closeout

        return execute_paper_closeout(
            sys.modules[__name__],
            paper_filter=paper_filter,
            library_premise_audit=library_premise_audit,
            require_source_bytes=require_source_bytes,
            deep_paper_prose=deep_paper_prose,
            closeout_trace=closeout_trace,
            closeout_progress_callback=closeout_progress_callback,
            operational_plan_identity=operational_plan_identity,
            operational_plan_receipt=operational_plan_receipt,
        )

    return execute_registered_checks(
        ordinary_repository_checks(
            sys.modules[__name__],
            include_active=include_active,
            strict_style=strict_style,
            library_premise_audit=library_premise_audit,
            paper_filter=paper_filter,
            require_source_bytes=require_source_bytes,
            deep_paper_prose=deep_paper_prose,
        )
    )


def finding_paper_id(finding: Finding) -> str:
    """Return the paper folder associated with a finding when one is visible."""

    path = finding.path
    parts = path.parts
    if "papers" in parts:
        index = parts.index("papers")
        if index + 1 < len(parts):
            paper = parts[index + 1]
            return paper.removesuffix(".lean") if paper.endswith(".lean") else paper
    match = re.match(r"`([^`]+)`", finding.message)
    if match:
        return match.group(1)
    return "REPO"


def paper_status_label(paper_id: str) -> str:
    status_path = PAPERS / paper_id / "status.json"
    if not status_path.exists():
        return "not recorded"
    try:
        payload = json.loads(status_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return "unreadable status.json"
    status = payload.get("status")
    if isinstance(status, str) and status.strip():
        return status
    return "missing status"


def deep_audit_category(message: str) -> str:
    if "Lean axiom audit" in message or "depends on unapproved Lean axiom" in message:
        return "Lean axiom closure"
    if (
        "broad aggregate name" in message
        or "opaque alias/signature" in message
        or "formula-bearing review row" in message
    ):
        return "broad-or-opaque paper-facing row"
    if (
        "premises not routed through explicit Assumptions.lean" in message
        or "source-row formula boundary" in message
    ):
        return "hidden premise / certificate boundary"
    if "DAG" in message or "final validation report" in message or "post-formalization audit" in message:
        return "DAG/report closeout audit"
    return "other repository audit finding"


def write_markdown_report(
    report_path: Path,
    findings: list[Finding],
    include_active: bool,
    strict_style: bool,
    library_premise_audit: bool,
    library_only: bool,
    paper_filter: str | None = None,
    deep_paper_prose: bool = False,
    paper_closeout: bool = False,
) -> None:
    """Write a durable paper-by-paper audit report.

    This is intentionally generated from the same finding objects printed by the
    CLI so the human report cannot drift from the blocking audit.
    """

    actionable = [finding for finding in findings if finding.severity in {"ERROR", "WARN"}]
    errors = [finding for finding in findings if finding.severity == "ERROR"]
    warnings = [finding for finding in findings if finding.severity == "WARN"]
    infos = [finding for finding in findings if finding.severity == "INFO"]

    by_paper: dict[str, list[Finding]] = {}
    for finding in actionable:
        by_paper.setdefault(finding_paper_id(finding), []).append(finding)

    command_bits = ["python3 scripts/audit_repository.py"]
    if include_active:
        command_bits.append("--include-active")
    if strict_style:
        command_bits.append("--strict-style")
    if library_premise_audit:
        command_bits.append("--library-premise-audit")
    if library_only:
        command_bits.append("--library-only")
    if paper_filter:
        command_bits.extend(["--paper", paper_filter])
    if paper_closeout:
        command_bits.append("--paper-closeout")
    if deep_paper_prose:
        command_bits.append("--deep-paper-prose")
    command_bits.append("--info-limit 0")
    command_bits.append(f"--write-report {report_path.as_posix()}")

    lines: list[str] = [
        "# Recursive Provenance Audit Findings",
        "",
        f"- Generated: {date.today().isoformat()}",
        f"- Command: `{' '.join(command_bits)}`",
        f"- Scope: {'library only' if library_only else 'papers and reusable library'}",
        f"- Paper filter: `{paper_filter}`" if paper_filter else "- Paper filter: none",
        f"- Active paper folders: {'included' if include_active else 'skipped'}",
        f"- Strict style: {'included' if strict_style else 'not included'}",
        f"- Library premise audit: {'included' if library_premise_audit else 'not included'}",
        f"- Totals: {len(errors)} error(s), {len(warnings)} warning(s), {len(infos)} info finding(s)",
        "",
        "## How To Use This Report",
        "",
        "Resolve findings paper-by-paper. For a paper claimed as `formalized`,",
        "`#print axioms` on the paper-facing rows should report only approved",
        "standard Lean foundations, no paper-facing row should remain broad or",
        "opaque, and every visible certificate/source-row/external premise should",
        "be either derived or routed through a source-validated `Assumptions.lean`",
        "declaration. Paper-specific formulas should not be hidden inside reusable",
        "library definitions. A paper may remain `partially formalized` only if the",
        "same boundary is explicit in `status.json`, the dependency DAG, and the",
        "final validation report.",
        "",
    ]

    if not actionable:
        lines.extend(["## Findings By Paper", "", "No actionable findings."])
    else:
        lines.extend(["## Findings By Paper", ""])
        for paper_id in sorted(by_paper):
            paper_findings = by_paper[paper_id]
            counts = {
                severity: sum(1 for finding in paper_findings if finding.severity == severity)
                for severity in ("ERROR", "WARN")
            }
            lines.extend(
                [
                    f"### {paper_id}",
                    "",
                    f"- Current status: `{paper_status_label(paper_id)}`",
                    f"- Findings: {counts['ERROR']} error(s), {counts['WARN']} warning(s)",
                    "",
                ]
            )
            for finding in paper_findings:
                rel = finding.path.relative_to(ROOT) if finding.path.is_absolute() else finding.path
                category = deep_audit_category(finding.message)
                lines.append(
                    f"- `[{finding.severity}]` `{rel}` ({category}): {finding.message}"
                )
            lines.append("")

    report_path = report_path if report_path.is_absolute() else ROOT / report_path
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--include-active",
        action="store_true",
        help="also audit folders listed as active in papers/audit_config.json",
    )
    parser.add_argument(
        "--strict-style",
        action="store_true",
        help="make naming, provenance-comment, binder-placement, and Mathlib-style guidance blocking",
    )
    parser.add_argument(
        "--library-premise-audit",
        action="store_true",
        help="also list reusable-library APIs that expose certificate/source-boundary parameters",
    )
    parser.add_argument(
        "--library-only",
        action="store_true",
        help="audit only reusable AppliedModelingLib code and library provenance checks",
    )
    parser.add_argument(
        "--paper",
        help=(
            "restrict machine-readable paper status checks to one paper folder; "
            "other generic repository checks still run unless --library-only is used"
        ),
    )
    parser.add_argument(
        "--paper-closeout",
        action="store_true",
        help=(
            "with --paper, run only that paper's named-theoretical-statement "
            "semantic proof/provenance closeout lane"
        ),
    )
    parser.add_argument(
        "--deep-paper-prose",
        action="store_true",
        help=(
            "opt in to presentation/prose hygiene diagnostics such as source-status "
            "comments and lexical formula/alias checks; these are not part of the "
            "default named-theory closeout"
        ),
    )
    parser.add_argument(
        "--info-limit",
        type=int,
        default=80,
        help=(
            "maximum INFO findings to print; use 0 to suppress INFO output or a negative "
            "number to print all INFO findings"
        ),
    )
    parser.add_argument(
        "--write-report",
        type=Path,
        help="write a Markdown report grouping actionable findings by paper",
    )
    parser.add_argument(
        "--allow-missing-source-bytes",
        action="store_true",
        help=(
            "structural public-checkout mode: keep canonical source pins but "
            "do not certify absent licensed source bytes"
        ),
    )
    parser.add_argument(
        "--closeout-trace",
        action="store_true",
        help=(
            "print non-authoritative JSON stage timings and reuse counters for "
            "the single consolidated paper closeout"
        ),
    )
    parser.add_argument(
        "--closeout-state",
        type=Path,
        help=(
            "write durable non-authoritative execution state to this path; "
            "paper closeouts default to the paper's ignored .review_traces directory"
        ),
    )
    parser.add_argument(
        "--operational-plan-identity",
        default="",
        help=(
            "planner-issued SHA-256 identity required when a paper-closeout "
            "writes durable execution state"
        ),
    )
    parser.add_argument(
        "--no-closeout-state",
        action="store_true",
        help=(
            "disable the default duplicate-run guard and durable closeout result "
            "(intended only for isolated test runners)"
        ),
    )
    args = parser.parse_args()
    operational_plan_receipt: Mapping[str, object] | None = None
    if args.paper_closeout and not args.paper:
        parser.error("--paper-closeout requires --paper <paper-folder>")
    if args.paper_closeout and args.library_only:
        parser.error("--paper-closeout cannot be combined with --library-only")
    if args.closeout_trace and not args.paper_closeout:
        parser.error("--closeout-trace requires --paper-closeout")
    if args.closeout_state and not args.paper_closeout:
        parser.error("--closeout-state requires --paper-closeout")
    if args.closeout_state and args.no_closeout_state:
        parser.error("--closeout-state cannot be combined with --no-closeout-state")
    if args.operational_plan_identity and not args.paper_closeout:
        parser.error("--operational-plan-identity requires --paper-closeout")
    if args.paper_closeout and args.paper:
        folder = PAPERS / args.paper
        status_payload = load_json_object(folder / "status.json")
        source_map_payload = load_json_object(
            folder / "audit" / "paper_statement_map.json"
        )
        if isinstance(status_payload, Mapping) and (
            explicit_raw_source_spec_screening_requested(
                status_payload,
                source_map_payload,
            )
        ):
            # Current publication has one owner.  Preserve the historical CLI
            # spelling as an operator convenience, but delegate before this
            # module acquires a lease or enters the mixed legacy executor.
            from scripts.current_closeout.strict_runner import main as run_current

            current_argv = ["--paper", args.paper]
            if args.operational_plan_identity:
                current_argv.extend(
                    ["--operational-plan-identity", args.operational_plan_identity]
                )
            if args.deep_paper_prose:
                current_argv.append("--deep-paper-prose")
            if args.allow_missing_source_bytes:
                current_argv.append("--allow-missing-source-bytes")
            if args.closeout_state is not None:
                current_argv.extend(["--closeout-state", str(args.closeout_state)])
            if args.no_closeout_state:
                current_argv.append("--no-closeout-state")
            return run_current(current_argv)
    if args.paper_closeout and not args.no_closeout_state:
        if not re.fullmatch(r"[0-9a-f]{64}", args.operational_plan_identity):
            parser.error(
                "stateful --paper-closeout requires --operational-plan-identity "
                "from run_paper_closeout.py; use --no-closeout-state for a direct diagnostic"
            )
        assert args.paper is not None
        engine_error = runtime_engine_registration_error(ROOT)
        if engine_error:
            print(
                "paper closeout not started: formalization engine runtime is not "
                "registered: " + engine_error,
                file=sys.stderr,
            )
            return 6
        operational_plan_receipt, plan_error = load_validated_closeout_plan_receipt(
            ROOT,
            paper=args.paper,
            deep_paper_prose=args.deep_paper_prose,
            expected_plan_identity=args.operational_plan_identity,
        )
        if plan_error:
            print(
                "paper closeout not started: planner receipt is absent, malformed, "
                "or stale: " + plan_error,
                file=sys.stderr,
            )
            return 6

    closeout_trace: dict[str, object] | None = (
        {} if args.paper_closeout else None
    )
    closeout_lease: CloseoutExecutionLease | None = None
    closeout_state_path: Path | None = None
    if args.paper_closeout and not args.no_closeout_state:
        assert args.paper is not None
        closeout_state_path = (
            args.closeout_state
            if args.closeout_state is not None
            else default_closeout_execution_path(ROOT, args.paper)
        )
        closeout_lease, lease_error = CloseoutExecutionLease.acquire(
            closeout_state_path,
            paper=args.paper,
            command=[sys.executable, *sys.argv],
            request={
                "operational_plan_identity": args.operational_plan_identity,
            },
        )
        if closeout_lease is None:
            print(f"paper closeout not started: {lease_error}", file=sys.stderr)
            return 2
        try:
            print(f"Closeout execution state: {closeout_state_path}")
        except BrokenPipeError:
            # The state file, not this informational line, owns recovery.
            pass

    try:
        if args.library_only:
            findings = run_library(
                strict_style=args.strict_style,
                library_premise_audit=args.library_premise_audit,
            )
        else:
            def publish_closeout_progress(event: Mapping[str, object]) -> None:
                if closeout_lease is None:
                    return
                completed = event.get("completed_stage_count")
                total = event.get("total_stage_count")
                closeout_lease.heartbeat(
                    stage=str(event.get("stage") or "strict_closeout"),
                    completed_units=(
                        completed
                        if isinstance(completed, int) and not isinstance(completed, bool)
                        else None
                    ),
                    total_units=(
                        total
                        if isinstance(total, int) and not isinstance(total, bool)
                        else None
                    ),
                    details={
                        str(key): value
                        for key, value in event.items()
                        if key
                        not in {
                            "stage",
                            "completed_stage_count",
                            "total_stage_count",
                        }
                    },
                )

            findings = run(
                include_active=args.include_active,
                strict_style=args.strict_style,
                library_premise_audit=args.library_premise_audit,
                paper_filter=args.paper,
                paper_closeout=args.paper_closeout,
                require_source_bytes=not args.allow_missing_source_bytes,
                deep_paper_prose=args.deep_paper_prose,
                closeout_trace=closeout_trace,
                closeout_progress_callback=(
                    publish_closeout_progress if args.paper_closeout else None
                ),
                operational_plan_identity=args.operational_plan_identity,
                operational_plan_receipt=operational_plan_receipt,
            )
    except BaseException as exc:
        if closeout_lease is not None:
            closeout_lease.fail(f"{type(exc).__name__}: {exc}")
        raise

    errors = [finding for finding in findings if finding.severity == "ERROR"]
    warnings = [finding for finding in findings if finding.severity == "WARN"]
    infos = [finding for finding in findings if finding.severity == "INFO"]
    if (
        args.paper_closeout
        and not errors
        and args.paper is not None
        and (
            not isinstance(closeout_trace, Mapping)
            or closeout_trace.get("current_closeout_published") is not True
        )
    ):
        finding = Finding(
            "ERROR",
            PAPERS / args.paper / ".review_traces",
            f"`{args.paper}` strict checks passed but the accepted graph was not "
            "published from the issuer-protected in-process closeout pass; the "
            "serialized trace is diagnostics only and cannot be finalized later",
        )
        findings.append(finding)
        errors.append(finding)
    exit_code = 1 if errors else 0
    if closeout_lease is not None:
        persisted_findings = []
        for finding in findings:
            path = finding.path
            try:
                rendered_path = str(path.resolve().relative_to(ROOT.resolve()))
            except (OSError, RuntimeError, ValueError):
                rendered_path = str(path)
            persisted_findings.append(
                {
                    "severity": finding.severity,
                    "path": rendered_path,
                    "message": finding.message,
                }
            )
        closeout_lease.complete(
            exit_code=exit_code,
            result={
                "semantic_closeout_passed": not errors,
                "errors": len(errors),
                "warnings": len(warnings),
                "infos": len(infos),
                "findings": persisted_findings,
                "trace": dict(closeout_trace or {}),
                "operational_plan_identity": args.operational_plan_identity,
            },
        )
    if args.write_report:
        write_markdown_report(
            args.write_report,
            findings,
            include_active=args.include_active,
            strict_style=args.strict_style,
            library_premise_audit=args.library_premise_audit,
            library_only=args.library_only,
            paper_filter=args.paper,
            deep_paper_prose=args.deep_paper_prose,
            paper_closeout=args.paper_closeout,
        )
        print(f"Wrote Markdown audit report to {args.write_report}")
    printed_infos = 0
    omitted_infos = 0
    for finding in findings:
        if finding.severity == "INFO" and args.info_limit >= 0:
            if printed_infos >= args.info_limit:
                omitted_infos += 1
                continue
            printed_infos += 1
        print(finding.format())
    if omitted_infos:
        print(
            f"[INFO] omitted {omitted_infos} additional info finding(s); "
            "rerun with `--info-limit -1` to print all"
        )
    if closeout_trace is not None:
        print(
            "Closeout trace: "
            + json.dumps(closeout_trace, sort_keys=True, separators=(",", ":"))
        )

    print(
        f"Audit complete: {len(errors)} error(s), {len(warnings)} warning(s)"
        + ("; active paper folders included" if args.include_active else "; active paper folders skipped")
        + ("; strict style included" if args.strict_style else "")
        + ("; library premise audit included" if args.library_premise_audit else "")
        + ("; library-only" if args.library_only else "")
        + (f"; paper filter {args.paper}" if args.paper else "")
        + ("; paper-closeout scope" if args.paper_closeout else "")
        + (f"; {len(infos)} info finding(s)" if infos else "")
    )
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
