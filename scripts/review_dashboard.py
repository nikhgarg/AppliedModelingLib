#!/usr/bin/env python3
"""Generate and persist theorem-review metadata from paper interfaces.

This helper creates a local review page for one paper or all papers.  The page
shows side-by-side the paper-facing claim text (when available) and the Lean
statement from the paper's curated review surface, and lets a reviewer record a
checkbox + note pair per theorem.  Each submission is appended to a local JSONL
trace with the reviewer handle and UTC timestamp.
"""

from __future__ import annotations

import argparse
import mimetypes
import hashlib
import csv
import html
import io
import getpass
import os
import json
import re
import signal
import sys
import subprocess
import urllib.parse
import tempfile
from dataclasses import dataclass, field as dataclass_field
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from xml.etree import ElementTree
from typing import Any, Callable, Iterable, Iterator, Mapping

# Use the same canonical package imports under `python scripts/...` and
# `python -m scripts...`; individual dependencies do not need fallback copies.
if __package__ in {None, ""}:
    repository_root = str(Path(__file__).resolve().parents[1])
    if repository_root not in sys.path:
        sys.path.insert(0, repository_root)

from scripts.lean_signature_manifest import (
    RepositoryBuildInputSnapshotProvider,
    repository_build_input_snapshot,
    paper_owned_module_names_in_import_closure,
    review_claim_target_text,
    run_lean_semantic_contract_matches,
    run_lean_semantic_contract_transparency_checks,
    run_lean_signature_manifests,
    signature_manifest_cache_context,
    signature_manifest_cache_context_sha256,
    signature_manifest_digest,
)
from scripts.authenticated_manifest_store import (
    configured_review_row_proposition_graph_sha256,
    current_source_bound_manifest_bindings,
    elaborated_proposition_graph_sha256,
    merge_authenticated_manifest_store,
    prime_attested_resume_manifests_with_current_revalidation,
    prime_exact_context_attested_resume_manifests,
    prime_authenticated_manifest_store,
    prime_authenticated_manifest_store_with_item_revalidation,
)
from scripts.source_artifact_companion import (
    semantic_review_source_identity,
    source_text_companion_validation_issues,
)
from scripts.source_record_semantic_reuse import (
    CurrentSemanticReuseAuthority,
)
from scripts.review_dashboard_html import render_static_html
from scripts.review_dashboard_cli import (
    _format_name_sample,
    print_assumption_audit_warnings,
    print_paper_coverage_audit_warnings,
    print_statement_audit_warnings,
    print_surface_audit_warnings,
)
from scripts.dashboard_audit_inputs import (
    DashboardAuditInputs,
    DashboardFrozenInputError,
    _dashboard_audit_inputs,
    _dashboard_file_bytes_override,
    _dashboard_is_file,
    _dashboard_json_payload,
    _dashboard_read_bytes,
    _dashboard_read_text,
    dashboard_audit_input_scope,
)
from scripts.configured_paper_inputs import (
    configured_dashboard_audit_input_paths,
)
from scripts.semantic_obligation_review import (
    CONDITIONAL_BOUNDARY_RESOLUTION,
    NAME_ONLY_SEMANTIC_EVIDENCE_RE,
    NAME_ONLY_SOURCE_COVERAGE_REASON_RE,
    SOURCE_DEFINITION_SEMANTIC_KINDS,
    SOURCE_DIRECT_EXPRESSION_SEMANTIC_KINDS,
    _normalize_llm_match_judgment,
    _normalize_llm_match_resolution,
    semantic_obligation_ledger_error,
    signature_manifest_atom_digest,
)
from scripts.source_archive_surface import source_archive_surface_validation_issues
from scripts.closeout_pipeline import (
    CloseoutPipelineError,
    EvidenceRouteSet,
    typed_route_validation_required,
)
from scripts.source_coverage_scope import (
    DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
    KNOWN_SOURCE_PRESENTATION_KINDS,
    deep_source_coverage_attestation_error,
    filter_source_inventory_for_coverage,
    source_index_byte_pinned_anchor_item_ids,
    source_item_has_explicit_nonordinary_obligation,
    source_named_result_environment_kinds_from_map,
    source_coverage_mode_from_map,
    source_coverage_mode_migration_error,
    source_coverage_modes_compatible,
    source_item_scope_classification_errors,
    source_item_coverage_sha256,
    source_item_coverage_receipt_matches,
    source_item_coverage_receipt_shape_is_reusable,
    source_item_effective_route_policy,
    source_map_structural_errors,
    source_presentation_aliases,
    source_prose_definition_inventory_errors,
)
from scripts.source_claim_policy import (
    NON_NAMED_COMPUTATIONAL_ILLUSTRATION,
    SOURCE_ARTIFACT_SHA256_RE,
    SOURCE_CATALOGUED_NONFORMAL_OBSERVATION_KINDS,
    SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION,
    SOURCE_FILE_LINE_ANCHOR_RE,
    USER_APPROVED_SCOPE_EXCLUSION,
    source_inventory_anchor_quote_text as _source_inventory_anchor_quote_text,
    source_anchor_paths_match as _source_anchor_paths_match,
    source_inventory_item_is_named_claim as _shared_source_inventory_item_is_named_claim,
    source_inventory_item_is_named_algorithm_block as _source_inventory_item_is_named_algorithm_block,
    source_inventory_item_requires_proof_evidence as _shared_source_inventory_item_requires_proof_evidence,
    source_inventory_item_scope_classification_error as _shared_source_inventory_item_scope_classification_error,
    source_inventory_item_user_approved_scope_exclusion_error as _shared_source_inventory_item_user_approved_scope_exclusion_error,
    source_inventory_search_text as _shared_source_inventory_search_text,
    source_text_has_general_computational_claim as _source_text_has_general_computational_claim,
    source_text_has_general_result_assertion as _source_text_has_general_result_assertion,
)
from scripts.current_closeout.review_surface import (
    current_dashboard_semantic_reuse_authority,
    bind_current_v11_source_spec_screening,
    _source_item_corrected_target,
    _source_item_is_corrected_target,
    _source_item_coverage_statement,
    _source_item_coverage_location,
    _prepared_library_prerequisites,
)
from scripts.source_display_projection import (
    public_source_display_coverage_surface,
)
from scripts.source_review_input import (
    normalize_statement as _shared_normalize_statement,
    source_anchor_file_error as _shared_source_anchor_file_error,
    source_semantic_input_bundle as _shared_source_semantic_input_bundle,
    statement_digest as _shared_statement_digest,
)
from scripts.corrected_target_identity import (
    corrected_target_record_digest as _shared_corrected_target_record_digest,
    corrected_target_review_digest,
)
from scripts.semantic_prerequisite_projection import (
    LIBRARY_SEMANTIC_REVIEW_SCHEMA,  # noqa: F401 -- public dashboard schema API
    LIBRARY_SEMANTIC_TARGET_PROTOCOL,  # noqa: F401 -- public dashboard schema API
    REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,  # noqa: F401 -- public API
)


ROOT = Path(
    os.environ.get("APPLIEDMODELINGLIB_REPO_ROOT", Path(__file__).resolve().parents[1])
).resolve()
PAPERS_DIR = ROOT / "papers"
AUDIT_CONFIG = PAPERS_DIR / "audit_config.json"
DEFAULT_PAPER_LOG_FILE = "paper_theorem_validations.jsonl"
DEFAULT_LIBRARY_PREREQUISITE_LOG_FILE = "library_prerequisite_validations.jsonl"
DEFAULT_PAPER_INTERFACE_CACHE_FILE = "paper_interface_cache.json"
MANIFEST_RESUME_CACHE_DIRNAME = "lean_signature_manifest_resume"
MANIFEST_RESUME_CACHE_SCHEMA = 2
# These records are deliberately ignored local performance data. They are not
# review evidence and never satisfy a paper audit. They are retained across
# publications because deleting them can race an independently interrupted
# refresh; exact context/source binding plus fresh Lean revalidation makes
# stale records harmless cache misses.
MANIFEST_RESUME_CACHE_NON_AUTHORITATIVE = True
DEFAULT_PAPER_STATUS_FILE = "status.json"
PAPER_DOCS_DIR = "docs"
PAPER_AUDIT_DIR = "audit"
FINAL_VALIDATION_REPORT_FILE = "FINAL_VALIDATION_REPORT.md"
DEFAULT_LLM_LEAN_TO_TEX_FILE = f"{PAPER_AUDIT_DIR}/lean_to_tex_llm.json"
DEFAULT_LLM_STATEMENT_JUDGE_FILE = f"{PAPER_AUDIT_DIR}/statement_match_llm.json"
DEFAULT_LLM_REVIEW_SURFACE_FILE = f"{PAPER_AUDIT_DIR}/review_surface_llm.json"
V11_RAW_SOURCE_SPEC_SCREENING_FILE = (
    f"{PAPER_AUDIT_DIR}/v11_raw_source_spec_screening.json"
)
V11_RAW_SOURCE_SPEC_SCREENING_SCHEMA = 3
V11_RAW_SOURCE_SPEC_SCREENING_PROMPT_VERSION = (
    "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-claim-atoms-supporting-declarations-v4"
)
V11_RAW_SOURCE_SPEC_LEAN_TARGET_PROTOCOL = (
    "lean_transparent_paper_expansion_with_claim_atoms_v2"
)
DEFAULT_LLM_PAPER_COVERAGE_FILE = f"{PAPER_AUDIT_DIR}/paper_coverage_llm.json"
DEFAULT_LLM_DEFECT_SUPPORT_FILE = f"{PAPER_AUDIT_DIR}/defect_support_match_llm.json"
DEFAULT_LLM_ASSUMPTION_JUDGE_FILE = f"{PAPER_AUDIT_DIR}/assumption_match_llm.json"
DEFAULT_LIBRARY_SEMANTIC_REVIEW_FILE = f"{PAPER_AUDIT_DIR}/library_semantic_review.json"
DEFAULT_ASSUMPTION_SOURCE_FILE = "Assumptions.lean"
REQUIRED_LLM_LEAN_TO_TEX_PROMPT_VERSION = "lean-to-tex-v3-strict-context-free-semantic-inputs"
REQUIRED_LLM_STATEMENT_PROMPT_VERSION = (
    "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-claim-atoms-supporting-declarations-v4"
)
# Prompt labels identify the producer instructions, while these contracts
# identify the semantic obligations that make an existing row reusable.  A
# wording-only prompt or validator update may be added to the code-owned maps
# below only after reviewing that it preserves the same contract.  Sidecars
# never get to assert their own compatibility.
REQUIRED_LLM_LEAN_TO_TEX_SEMANTIC_CONTRACT_VERSION = (
    "lean-to-tex-semantic-inputs-v3"
)
REQUIRED_LLM_STATEMENT_SEMANTIC_CONTRACT_VERSION = (
    "statement-match-verbatim-source-anchor-expanded-spec-with-prerequisites-v12"
)
LLM_LEAN_TO_TEX_PROMPT_SEMANTIC_CONTRACTS: dict[str, str] = {
    REQUIRED_LLM_LEAN_TO_TEX_PROMPT_VERSION: (
        REQUIRED_LLM_LEAN_TO_TEX_SEMANTIC_CONTRACT_VERSION
    ),
}
LLM_STATEMENT_PROMPT_SEMANTIC_CONTRACTS: dict[str, str] = {
    REQUIRED_LLM_STATEMENT_PROMPT_VERSION: (
        REQUIRED_LLM_STATEMENT_SEMANTIC_CONTRACT_VERSION
    ),
}
REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION = (
    "paper-coverage-v6-verbatim-source-anchor-proof-row-signature-pins"
)
LEGACY_LLM_PAPER_COVERAGE_PROMPT_VERSION = (
    "paper-coverage-v3-semantic-proof-declaration-and-defect-support"
)
REQUIRED_LLM_DEFECT_SUPPORT_PROMPT_VERSION = (
    "defect-support-v1-exact-source-defect-to-lean-semantic"
)
REQUIRED_LLM_REVIEW_SURFACE_PROMPT_VERSION = "review-surface-v2-semantic-paper-facing"
REQUIRED_LLM_ASSUMPTION_PROMPT_VERSION = "assumption-provenance-v4-verbatim-source-anchor-exact-premise"
PAPER_STATEMENT_MAP_FILE = f"{PAPER_AUDIT_DIR}/paper_statement_map.json"
# A public release deliberately omits the complete byte-pinned source artifact.
# This small, generated manifest freezes only the selected review surface and
# its already-published excerpts.  It is a *display* aid: strict audit gates
# continue to require the local source bytes and never consult this file.
PUBLIC_SOURCE_DISPLAY_PROJECTION_FILE = (
    f"{PAPER_AUDIT_DIR}/public_source_display_projection.json"
)
PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA = 1
PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD = "publication_source_display_projection"
PUBLIC_SOURCE_DISPLAY_PROJECTION_GENERATOR = (
    "python3 scripts/public_source_display_projection.py"
)
PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST = (
    "audit/public_source_display_projection.json"
)
PUBLICATION_SOURCE_LOCATOR = "cited publication"
# A mechanically generated sidecar can record its frozen inputs without being
# evidence.  Readers must reject this marker until an independent reviewer
# deletes it after supplying the actual translation or semantic judgment.
NON_EVIDENCE_SCAFFOLD_SCHEMA = 1
NON_EVIDENCE_SCAFFOLD_STATUS = "needs_review"
SOURCE_ROUTE_KINDS = {
    "direct",
    "approved_corrected_target",
    "source_component",
    "source_model_convention",
    "defect_or_remark_support",
    "proof_support",
}
CORRECTED_SOURCE_STATEMENT_STATUS = "corrected_source_statement"
CORRECTED_TARGET_SCHEMA = 1
CORRECTED_TARGET_COVERAGE = "covered_corrected_target"
PAPER_PREREQUISITE_COVERAGE_IDENTITY_SCHEMA = 1
PAPER_PREREQUISITE_COVERAGE_TARGET_KIND = "paper_semantic_prerequisite"
PAPER_PREREQUISITE_LEDGER_SCHEMA = 1
PAPER_PREREQUISITE_LEDGER_PROMPT_VERSION = (
    "paper-prerequisite-match-v2-verbatim-source-anchor-lean-expanded-target-exact-code"
)
PAPER_PREREQUISITE_LEDGER_TARGET_PROTOCOL = (
    "lean_paper_declaration_display_v1"
)
CORRECTED_TARGET_ROUTE_KIND = "approved_corrected_target"
CORRECTED_TARGET_MATCH_RESOLUTION = "approved_corrected_target"
CORRECTED_TARGET_ROUTE_RELATION = "proves_approved_corrected_target"
APPROVED_CORRECTED_TARGET_MATCH = "matches_approved_corrected_target"
# A corrected target is not a literal archival match, but it is an admissible
# positive semantic verdict once the map-pinned approval binding has been
# checked. Keep the exact verdict on review cards; use this set only where a
# consumer needs to know whether a current reviewed target is positive.
POSITIVE_SEMANTIC_MATCH_JUDGMENTS = frozenset(
    {"matches", APPROVED_CORRECTED_TARGET_MATCH}
)
APPROVED_CORRECTED_TARGET_PROTOCOL = "approved_corrected_target_v1"
SOURCE_MODEL_ROUTE_RELATIONS = {
    "equivalent_model_convention",
    "shared_model_convention",
    "source_implies_lean_model",
    "lean_implies_source_model",
}
SOURCE_COMPONENT_ROUTE_RELATIONS = {
    "lean_implies_source_component",
    "equivalent_source_component",
}
SOURCE_DEFINITION_PARTITION_FIELD = "source_definition_partition"
SOURCE_DEFINITION_PARTITION_SCHEMA = 1
SOURCE_DEFINITION_PARTITION_RELATION = (
    "jointly_equivalent_to_source_definition"
)
SOURCE_DEFINITION_COMPONENT_EXACT_STATUS = "exact"
SOURCE_DEFINITION_COMPONENT_CONVENTION_STATUSES = frozenset(
    {
        "documented_model_convention",
        "documented_source_domain_convention",
        "documented_source_model_convention",
        "source_model_convention",
    }
)
SOURCE_DEFINITION_COMPONENT_RELATION = "equivalent_source_component"
SOURCE_COMPONENT_DISPLAY_BINDING_SCHEMA = 2
SOURCE_DEFECT_ROUTE_RELATIONS = {
    "counterexample_to_source_defect",
    "refutes_source_defect",
    "explains_support_only_remark",
}
REVIEW_SURFACE_LLM_AUDIT_THRESHOLD = 30
REVIEW_SURFACE_WARN_THRESHOLD = 120
PAPER_INTERFACE_CACHE_SCHEMA = 20
SEMANTIC_BRIDGE_DECLARATION_FIELDS = (
    "semantic_bridge_declarations",
    "paper_equivalence_declarations",
    "source_equivalence_declarations",
    "library_bridge_declarations",
)
REVIEW_SURFACE_SCHEMA = 1
REVIEW_SOURCE_FILENAME = "PaperInterface.lean"
REVIEW_DECL_KINDS = {
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "axiom",
    "structure",
    "class",
    "inductive",
}


def llm_prompt_version_is_semantically_current(
    prompt_version: str,
    *,
    prompt_contracts: Mapping[str, str],
    required_contract: str,
) -> bool:
    """Check a code-owned prompt compatibility mapping.

    A sidecar can report only the prompt version that produced a row. The
    dashboard decides whether that prompt preserves today's semantic contract;
    arbitrary sidecar metadata cannot turn an older or weaker prompt into
    compatible evidence.
    """

    return prompt_contracts.get(str(prompt_version or "").strip()) == required_contract


def active_paper_names() -> set[str]:
    """Return paper folders skipped by whole-repository dashboard checks."""

    if not AUDIT_CONFIG.exists():
        return set()
    try:
        payload = json.loads(AUDIT_CONFIG.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return set()
    raw = payload.get("active_papers", []) if isinstance(payload, dict) else []
    if not isinstance(raw, list):
        return set()
    return {str(item).strip() for item in raw if str(item).strip()}


def paper_relative_file(folder: Path, preferred: str, legacy: str | None = None) -> Path:
    """Return the organized paper-local path, falling back to a legacy root file."""

    preferred_path = folder / preferred
    inputs = _dashboard_audit_inputs()
    if inputs is not None:
        if not inputs.has_snapshot(preferred_path):
            raise DashboardFrozenInputError(
                f"missing frozen dashboard input: {inputs._key(preferred_path)}"
            )
        if inputs.is_file(preferred_path) or legacy is None:
            return preferred_path
        if legacy is not None:
            legacy_path = folder / legacy
            if inputs.has_snapshot(legacy_path):
                return legacy_path
            raise DashboardFrozenInputError(
                "missing frozen dashboard fallback input: "
                f"{inputs._key(legacy_path)}"
            )
        return preferred_path
    if preferred_path.exists() or legacy is None:
        return preferred_path
    legacy_path = folder / legacy
    if legacy_path.exists():
        return legacy_path
    return preferred_path


def is_non_evidence_scaffold_payload(payload: Any) -> bool:
    """Return whether a sidecar is intentionally blank pending real review.

    The marker is deliberately narrow and machine-readable.  It is not a
    semantic judgment, so every loader treats it as incomplete even if someone
    later adds otherwise plausible-looking fields without clearing the marker.
    """

    if not isinstance(payload, dict):
        return False
    marker = payload.get("non_evidence_scaffold")
    return (
        isinstance(marker, dict)
        and marker.get("schema") == NON_EVIDENCE_SCAFFOLD_SCHEMA
        and str(marker.get("status") or "").strip().lower()
        == NON_EVIDENCE_SCAFFOLD_STATUS
    )


ASSUMPTION_DECL_NAME_RE = re.compile(
    r"^(?:paper_)?assumption(?:_|$)|^source_assumption(?:_|$)|_assumption(?:_|$)"
)
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
    "human_verified_source_implicit",
}
APPROVED_PAPER_COVERAGE_JUDGMENTS = {
    "covered",
    "covered_by_rows",
    CORRECTED_TARGET_COVERAGE,
    "covered_by_support",
    "support_only",
    "covered_with_boundary",
    "conditional_boundary",
    "visible_premise_boundary",
    "out_of_scope",
    "not_a_paper_target",
    "not_a_theorem_statement",
    USER_APPROVED_SCOPE_EXCLUSION,
}
APPROVED_PAPER_COVERAGE_AUDIT_KINDS = {
    "source_to_dashboard_llm",
    "source_to_dashboard_agent",
}
APPROVED_DEFECT_SUPPORT_AUDIT_KINDS = {
    "source_defect_to_lean_llm",
    "source_defect_to_lean_agent",
}
APPROVED_DEFECT_SUPPORT_JUDGMENTS = {
    "valid_counterexample",
    "valid_refutation",
}
DEFECT_SUPPORT_JUDGMENT_RELATIONS = {
    "valid_counterexample": "counterexample_to",
    "valid_refutation": "refutes",
}
PAPER_COVERAGE_SCAFFOLD_KINDS = {
    "all_uncertain_bootstrap",
    "exact_key_scaffold",
    "dashboard_seeded_preliminary",
    "seeded_exact_key",
}
SOURCE_TEXT_ASSUMPTION_PREMISE_JUDGMENTS = {
    "paper_assumption",
    "paper_condition",
    "source_text",
    "source_text_model_primitive",
    "human_verified_source_implicit",
}


DECL_RE = re.compile(
    r"^(?P<indent>\s*)(?:(?:@\[[^\]]+\]|@[A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?)\s+)*"
    r"(?:(?:noncomputable|private|protected)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|axiom|structure|class|inductive)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b"
)
EXPORT_OPEN_RE = re.compile(
    r"^\s*export\s+(?P<source>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s+\((?P<rest>.*)$"
)
EXPORT_NAME_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*\b")
COMMENT_START_RE = re.compile(r"^\s*/-[!]?")
NAMESPACE_OPEN_RE = re.compile(
    r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$"
)
SECTION_OPEN_RE = re.compile(r"^\s*section(?:\s+[A-Za-z_][A-Za-z0-9_']*)?\s*$")
END_SCOPE_RE = re.compile(r"^\s*end\b(?:\s+([A-Za-z_][A-Za-z0-9_']*)\s*)?$")
REPORT_CLAUSE_RE = re.compile(
    r"^\s*-\s*`(?:[A-Za-z0-9_]+\.)?(?P<name>[A-Za-z_][A-Za-z0-9_']+)`\s*:\s*(?P<text>.*)"
)
THEOREM_ENV_OPEN_RE = re.compile(r"^\s*\\begin\{(theorem|lemma|proposition|corollary|claim|definition|remark)\}")
THEOREM_ENV_CLOSE_RE = re.compile(r"^\s*\\end\{(theorem|lemma|proposition|corollary|claim|definition|remark)\}")
THEOREM_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
PAPER_TEXT_STATEMENT_LABEL_RE = re.compile(
    r"^\s*\f?\s*(?P<kind>Definition|Theorem|Lemma|Proposition|Corollary|Claim|Remark)\s+"
    r"(?P<number>[A-Za-z]?\d+(?:\.\d+)?)(?:\s*\((?P<title>[^)]*)\))?\."
)
PAPER_TEXT_STATEMENT_STOP_RE = re.compile(
    r"^\s*(?:Proof\.|Proof\s|The proof\b|To prove\b|The result follows\b|"
    r"The theorem establishes\b|The result establishes\b|Each de|"
    r"Of course\b|Note that\b|Discussion\b|What does\b|Then, we have the following\b)"
)
PAPER_TEX_PRIORITY: list[str] = [
    "{name}.tex",
    "paper.tex",
    "source.tex",
]
AGENT_PREVIEW_TOKEN_RE = re.compile(
    r"^[ \t]*(?:(?:noncomputable|private|protected)\s+)*"
    r"(?:theorem|lemma|def|abbrev)\s+[A-Za-z_][A-Za-z0-9_']*\s*",
    re.MULTILINE,
)
LEAN_TO_TEX_TOKENS: list[tuple[str, str]] = [
    ("→", r"\to"),
    ("↔", r"\iff"),
    ("⇒", r"\Rightarrow"),
    ("⇐", r"\Leftarrow"),
    ("∧", r"\land"),
    ("∨", r"\lor"),
    ("¬", r"\lnot"),
    ("∑", r"\sum"),
    ("∏", r"\prod"),
    ("∫", r"\int"),
    ("∃", r"\exists"),
    ("∀", r"\forall"),
    ("≤", r"\le"),
    ("≥", r"\ge"),
    ("≠", r"\ne"),
    ("≃", r"\simeq"),
    ("≈", r"\approx"),
    ("α", r"\alpha"),
    ("β", r"\beta"),
    ("γ", r"\gamma"),
    ("δ", r"\delta"),
    ("ε", r"\epsilon"),
    ("ι", r"\iota"),
    ("κ", r"\kappa"),
    ("λ", r"\lambda"),
    ("μ", r"\mu"),
    ("ν", r"\nu"),
    ("π", r"\pi"),
    ("σ", r"\sigma"),
    ("τ", r"\tau"),
    ("φ", r"\phi"),
    ("χ", r"\chi"),
    ("ψ", r"\psi"),
    ("ω", r"\omega"),
    ("Γ", r"\Gamma"),
    ("Δ", r"\Delta"),
    ("Π", r"\Pi"),
    ("Σ", r"\Sigma"),
    ("Λ", r"\Lambda"),
    ("Φ", r"\Phi"),
    ("Ψ", r"\Psi"),
    ("Ω", r"\Omega"),
    ("∈", r"\in"),
    ("⊆", r"\subseteq"),
    ("∅", r"\varnothing"),
    ("↦", r"\mapsto"),
]
AGENT_PREVIEW_MAX_LEN = 1800
AGENT_PREVIEW_CHECK_TIMEOUT = 20
PAPER_ASSET_EXTENSIONS = {".pdf", ".txt"}
PAPER_RENDERED_IMAGE_EXTENSIONS = {".png"}
PAPER_RENDERED_STATEMENT_DIR = "paper_statement_images"
PAPER_PDF_PRIORITY: list[str] = [
    "{name}.pdf",
    "source.pdf",
    "paper.pdf",
    "arxiv.pdf",
]
PAPER_TXT_PRIORITY: list[str] = [
    "source.txt",
    "paper.txt",
    "{name}.txt",
]
DEFAULT_USER_ENV_VARS = [
    "GITHUB_ACTOR",
    "GITHUB_USER",
    "GITHUB_USERNAME",
    "GITHUB_REPOSITORY_OWNER",
]
OS_USER_ENV_VARS = [
    "USER",
    "USERNAME",
]
AGENT_PREVIEW_CACHE: dict[str, dict[str, str]] = {}
SIGNATURE_MANIFEST_CACHE: dict[str, dict[str, dict[str, Any]]] = {}


_DASHBOARD_CANONICAL_LEGACY_SIDECARS: tuple[tuple[str, str], ...] = (
    (DEFAULT_LLM_LEAN_TO_TEX_FILE, "lean_to_tex_llm.json"),
    (DEFAULT_LLM_STATEMENT_JUDGE_FILE, "statement_match_llm.json"),
    (DEFAULT_LLM_REVIEW_SURFACE_FILE, "review_surface_llm.json"),
    (DEFAULT_LLM_PAPER_COVERAGE_FILE, "paper_coverage_llm.json"),
    (DEFAULT_LLM_DEFECT_SUPPORT_FILE, "defect_support_match_llm.json"),
    (DEFAULT_LLM_ASSUMPTION_JUDGE_FILE, "assumption_match_llm.json"),
    (PAPER_STATEMENT_MAP_FILE, "paper_statement_map.json"),
    (f"{PAPER_AUDIT_DIR}/source_proof_fidelity.json", "source_proof_fidelity.json"),
    (f"{PAPER_AUDIT_DIR}/source_record_audit.json", "source_record_audit.json"),
    (f"{PAPER_AUDIT_DIR}/source_record_match_llm.json", "source_record_match_llm.json"),
)


def required_dashboard_audit_input_paths(
    folder: Path,
    *,
    status_bytes: bytes,
    statement_map_bytes: bytes | None,
    repository_root: Path = ROOT,
) -> tuple[Path, ...]:
    """Return the bounded exact-file set needed by legacy dashboard checks.

    The dashboard presentation path still supports conventional source names
    and historical sidecar aliases. Current graph-native closeout uses
    :func:`configured_v11_evidence_input_paths` instead, so merely creating
    an unselected conventional file cannot mutate an in-flight v11 audit.
    Neither collector reads, probes, globs, or walks the filesystem.
    """

    paths = set(
        configured_dashboard_audit_input_paths(
            folder,
            status_bytes=status_bytes,
            statement_map_bytes=statement_map_bytes,
            repository_root=repository_root,
        )
    )
    paper_folder = Path(os.path.abspath(folder))
    paths.update(
        {
            paper_folder / DEFAULT_PAPER_STATUS_FILE,
            paper_folder / REVIEW_SOURCE_FILENAME,
            paper_folder / DEFAULT_ASSUMPTION_SOURCE_FILE,
            paper_folder / FINAL_VALIDATION_REPORT_FILE,
            # `_human_review_intake_order` consults this optional legacy input
            # before falling back to the v11 review-surface order. Snapshot an
            # absent file so a strict dashboard does not probe live state.
            paper_folder / PAPER_AUDIT_DIR / "intake_freeze.json",
        }
    )
    for canonical, legacy in _DASHBOARD_CANONICAL_LEGACY_SIDECARS:
        paths.add(paper_folder / canonical)
        paths.add(paper_folder / legacy)
    for pattern in PAPER_TEX_PRIORITY:
        paths.add(paper_folder / pattern.format(name=paper_folder.name))
    for pattern in PAPER_TXT_PRIORITY:
        paths.add(paper_folder / pattern.format(name=paper_folder.name))
    for pattern in PAPER_PDF_PRIORITY:
        paths.add(paper_folder / pattern.format(name=paper_folder.name))
    return tuple(sorted(paths))


# Compatibility for the shorter name advertised during initial integration.
required_dashboard_input_paths = required_dashboard_audit_input_paths


def _normalize_name_key(name: str) -> str:
    """Normalize a declaration-like name into a tolerant lookup key."""

    return re.sub(r"[^A-Za-z0-9_]+", "_", name.strip()).strip("_")


def _add_statement_variant(mapping: dict[str, str], key: str, value: str) -> None:
    mapping[key] = value
    normalized = _normalize_name_key(key)
    if normalized and normalized != key:
        mapping[normalized] = value
    lowered = key.lower()
    if lowered and lowered != key:
        mapping[lowered] = value
    lowered_normalized = normalized.lower()
    if lowered_normalized and lowered_normalized not in {lowered, normalized, key}:
        mapping[lowered_normalized] = value


def _paper_statement_key(kind: str, number: str) -> str:
    """Return a declaration-name-friendly key for a paper statement number."""

    normalized_number = number.strip().replace(".", "_").lower()
    return f"{kind.strip().lower()}{normalized_number}"


def _read_git_config_value(key: str) -> str:
    """Read a git configuration value for this repo, returning empty on failure."""

    try:
        proc = subprocess.run(
            ["git", "-C", str(ROOT), "config", "--get", key],
            check=False,
            capture_output=True,
            text=True,
            timeout=2,
        )
    except (OSError, subprocess.TimeoutExpired):
        return ""
    value = (proc.stdout or "").strip()
    if not value and proc.returncode != 0:
        return ""
    return value


def _read_gh_cli_user() -> str:
    """Read cached GitHub username from gh CLI config if available."""

    host_file = Path.home() / ".config" / "gh" / "hosts.yml"
    if not host_file.exists() or not host_file.is_file():
        return ""
    try:
        lines = host_file.read_text(encoding="utf-8").splitlines()
    except OSError:
        return ""

    in_github_host = False
    for raw_line in lines:
        line = raw_line.rstrip()
        header = re.match(r"^([A-Za-z0-9._-]+):\s*$", line)
        if header and not raw_line.startswith(" "):
            in_github_host = header.group(1).strip() == "github.com"
            continue
        if not in_github_host:
            continue
        match = re.match(r"^\s*user:\s*\"?\'?([^\"\'\\n]+)\"?\'?\s*$", line)
        if match:
            return match.group(1).strip()
    return ""


def _read_gh_api_user() -> str:
    """Return the authenticated GitHub login from `gh`, if available."""

    try:
        proc = subprocess.run(
            ["gh", "api", "user", "--jq", ".login"],
            check=False,
            capture_output=True,
            text=True,
            timeout=3,
        )
    except (OSError, subprocess.TimeoutExpired):
        return ""
    if proc.returncode != 0:
        return ""
    return (proc.stdout or "").strip()


def detect_reviewer_username(explicit_user: str | None, env_vars: list[str]) -> str:
    """Choose the best available reviewer username with sensible fallbacks."""

    user = (explicit_user or "").strip()
    if user:
        return user

    for env_var in env_vars:
        env_user = os.environ.get(env_var)
        if env_user and env_user.strip():
            return env_user.strip()

    authed = _read_gh_api_user()
    if authed:
        return authed

    cached = _read_gh_cli_user()
    if cached:
        return cached

    for key in ("github.user", "user.name", "user.username"):
        git_user = _read_git_config_value(key)
        if git_user:
            return git_user.strip()

    for env_var in OS_USER_ENV_VARS:
        env_user = os.environ.get(env_var)
        if env_user and env_user.strip():
            return env_user.strip()

    return getpass.getuser()


@dataclass
class ReviewItem:
    name: str
    kind: str
    lean_statement: str
    paper_statement: str
    agent_statement: str
    full_name: str = ""
    interface_source: str = ""
    lean_signature_manifest: dict[str, Any] | None = None
    lean_signature_sha256: str = ""
    # Coverage can point either to an ordinary elaborated result row or to an
    # already-reviewed paper-semantic prerequisite card.  The latter is not a
    # fabricated theorem row: this typed identity binds the prerequisite
    # ledger's exact source bundle, Lean target, route, judgment, and protocol.
    coverage_target_kind: str = ""
    coverage_target_identity_sha256: str = ""
    source_status: str = ""
    source_note: str = ""
    llm_match_judgment: str = ""
    llm_match_reason: str = ""
    llm_match_stale: bool = False
    llm_match_source: str = ""
    llm_match_validator: str = ""
    llm_match_validator_type: str = ""
    llm_match_validated_at: str = ""
    llm_match_lean_statement_sha256: str = ""
    llm_match_lean_signature_sha256: str = ""
    llm_match_paper_statement_sha256: str = ""
    llm_match_tex_statement_sha256: str = ""
    llm_match_resolution: str = ""
    llm_match_boundary_type: str = ""
    llm_match_boundary_names: list[str] | None = None
    llm_match_conditional_premises: list[str] | None = None
    llm_match_resolution_reason: str = ""
    llm_match_source_routes: list[dict[str, Any]] | None = None
    llm_match_component_target_sha256: str = ""
    is_assumption: bool = False
    is_proposition_spec: bool = False
    proposition_spec_role: str = ""
    proposition_spec_proof: str = ""
    semantic_contract_lean_match_verified: bool | None = None
    semantic_contract_lean_transparency_verified: bool | None = None
    llm_assumption_judgment: str = ""
    llm_assumption_reason: str = ""
    llm_assumption_stale: bool = False
    llm_assumption_source: str = ""
    llm_assumption_validator: str = ""
    llm_assumption_validator_type: str = ""
    llm_assumption_validated_at: str = ""
    llm_assumption_lean_statement_sha256: str = ""
    llm_assumption_paper_statement_sha256: str = ""
    llm_assumption_premise_judgments: dict[str, dict[str, str]] | None = None
    paper_statement_image_url: str = ""
    # The v11 statement-review source target.  Unlike ``paper_statement``,
    # which may be a readable navigation summary for legacy rows, these values
    # identify only the exact byte-pinned source excerpts supplied to the
    # semantic reviewer.
    source_item_key: str = ""
    source_input_bundle_sha256: str = ""
    verbatim_source_input: str = ""
    line_number: int = 0
    slice_id: str = "all"
    slice_title: str = "All statements"


# Quarantined counterexamples/refutations are not paper claims and therefore
# never enter the dashboard row list.  Coverage validation still needs their
# exact Lean-elaborated statements and manifests.  Keep that separate support
# surface in the same cache transaction as the ordinary rows.
QUARANTINED_SUPPORT_REVIEW_ITEM_CACHE: dict[str, dict[str, ReviewItem]] = {}


def find_review_source_file(folder: Path) -> Path | None:
    """Return the paper's curated human-review Lean surface, if present."""

    def display_path(path: Path) -> str:
        try:
            return str(path.relative_to(ROOT))
        except ValueError:
            return str(path)

    candidate = folder / REVIEW_SOURCE_FILENAME
    payload = load_review_slice_payload(folder)
    raw_source = payload.get("source_file")
    if isinstance(raw_source, str) and raw_source.strip():
        source = Path(raw_source.strip())
        if not source.is_absolute():
            if len(source.parts) == 1:
                source = folder / source
            else:
                source = ROOT / source
        if source.resolve() != candidate.resolve():
            raise FileNotFoundError(
                f"{folder.name} review_surface.source_file must be "
                f"{REVIEW_SOURCE_FILENAME}; got {display_path(source)}"
            )
        if _dashboard_is_file(source):
            return source

    if _dashboard_is_file(candidate):
        return candidate
    return None


def review_source_file(folder: Path) -> Path:
    """Return the paper's review source or raise a readable error."""

    source = find_review_source_file(folder)
    if source is None:
        raise FileNotFoundError(
            f"no canonical human review Lean surface ({REVIEW_SOURCE_FILENAME}) "
            f"for paper: {folder.name}"
        )
    return source


def review_source_module(folder: Path, source_file: Path) -> str:
    """Return the Lean import module for a paper-local review source."""

    return f"{folder.name}.{source_file.stem}"


def review_proof_module(folder: Path, source_file: Path) -> str:
    """Return the module that exposes proof endpoints for semantic Specs.

    The default keeps legacy papers working, where the exact-type wrapper still
    sits in `PaperInterface.lean`. New and migrated papers set `proof_module`
    to their root module, which imports `ProofInterface.lean` without adding
    thin wrappers to the human review surface.
    """

    payload = load_review_slice_payload(folder)
    configured = str(payload.get("proof_module") or "").strip()
    if not configured:
        return review_source_module(folder, source_file)
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", configured):
        raise ValueError(f"{folder.name} review_surface.proof_module is not a Lean module name")
    if configured != folder.name and not configured.startswith(f"{folder.name}."):
        raise ValueError(
            f"{folder.name} review_surface.proof_module must be paper-owned"
        )
    return configured


def assumption_source_file(folder: Path) -> Path:
    """Return the paper-local Lean source that holds explicit assumptions."""

    payload = load_review_slice_payload(folder)
    raw_path = payload.get("assumption_source_file")
    if isinstance(raw_path, str) and raw_path.strip():
        path = Path(raw_path.strip())
        if not path.is_absolute():
            if len(path.parts) == 1:
                path = folder / path
            else:
                path = ROOT / path
        return path
    return folder / DEFAULT_ASSUMPTION_SOURCE_FILE


def find_paper_pdf(folder: Path) -> Path | None:
    """Find the most likely paper pdf in a folder."""

    inputs = _dashboard_audit_inputs()
    if inputs is not None:
        candidates = inputs.existing_files_under(folder, suffix=".pdf")
        by_name = {path.name: path for path in candidates}
        for rel in PAPER_PDF_PRIORITY:
            candidate = by_name.get(rel.format(name=folder.name))
            if candidate is not None:
                return candidate
        return next(
            (
                path
                for path in candidates
                if path.name.lower() not in {"dependencydag.pdf", "dependency_dag.pdf"}
            ),
            None,
        )
    for rel in PAPER_PDF_PRIORITY:
        candidate = folder / rel.format(name=folder.name)
        if candidate.exists() and candidate.is_file():
            return candidate

    for candidate in sorted(
        p
        for p in folder.glob("*.pdf")
        if p.is_file() and p.name.lower() not in {"dependencydag.pdf", "dependency_dag.pdf"}
    ):
        return candidate
    return None


def find_paper_text(folder: Path) -> Path | None:
    """Find a compact text fallback for paper-source viewing."""

    inputs = _dashboard_audit_inputs()
    if inputs is not None:
        candidates = {
            path.name: path for path in inputs.existing_files_under(folder, suffix=".txt")
        }
        for rel in PAPER_TXT_PRIORITY:
            candidate = candidates.get(rel.format(name=folder.name))
            if candidate is not None:
                return candidate
        return None
    for rel in PAPER_TXT_PRIORITY:
        candidate = folder / rel.format(name=folder.name)
        if candidate.exists() and candidate.is_file():
            return candidate
    return None


def paper_asset_url(paper: str, path: Path) -> str:
    """Build a safe route path for a paper-local asset."""

    return f"/paper-assets/{urllib.parse.quote(paper)}/{urllib.parse.quote(path.name)}"


def paper_rendered_statement_url(paper: str, path: Path) -> str:
    """Build a safe route path for a generated statement image."""

    return f"/rendered-statements/{urllib.parse.quote(paper)}/{urllib.parse.quote(path.name)}"


def _file_sha256(path: Path | None) -> str:
    """Return a stable binary digest for a source file."""

    if path is None:
        return ""
    inputs = _dashboard_audit_inputs()
    if inputs is not None:
        if not inputs.is_file(path):
            return ""
        return hashlib.sha256(inputs.read_bytes(path)).hexdigest()
    if not path.exists() or not path.is_file():
        return ""
    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError:
        return ""
    return digest.hexdigest()


def parse_block_comment(lines: list[str], start: int) -> tuple[str, int]:
    """Collect a block comment from `start`; return text and first line after it."""

    collected = [lines[start]]
    j = start
    if "-/" in lines[start]:
        return "\n".join(collected), start + 1
    while j + 1 < len(lines):
        j += 1
        collected.append(lines[j])
        if "-/" in lines[j]:
            return "\n".join(collected), j + 1
    return "\n".join(collected), len(lines)


def clean_comment(raw: str) -> str:
    """Strip Lean block comment markers and clean a docstring for display."""

    text = raw.strip()
    if text.startswith("/-!"):
        text = text[3:]
    elif text.startswith("/-"):
        text = text[2:]
    if text.endswith("-/"):
        text = text[:-2]
    text = text.strip()
    lines = [line.lstrip(" *") for line in text.splitlines()]
    return "\n".join(line.strip() for line in lines).strip()


def split_source_metadata(text: str) -> tuple[str, str, str]:
    """Extract dashboard-only source provenance lines from a docstring."""

    kept: list[str] = []
    source_status = ""
    source_notes: list[str] = []
    for raw_line in text.splitlines():
        line = raw_line.strip()
        status_match = re.match(r"^Source status:\s*(.+)$", line, flags=re.IGNORECASE)
        if status_match:
            source_status = status_match.group(1).strip()
            continue
        note_match = re.match(r"^Source note:\s*(.+)$", line, flags=re.IGNORECASE)
        if note_match:
            source_notes.append(note_match.group(1).strip())
            continue
        kept.append(raw_line)
    return "\n".join(kept).strip(), source_status, " ".join(source_notes).strip()


def normalize_statement(text: str) -> str:
    """Compatibility wrapper for shared statement normalization."""

    return _shared_normalize_statement(text)


def statement_digest(text: str) -> str:
    """Compatibility wrapper for the shared statement digest."""

    return _shared_statement_digest(text)


def corrected_target_digest(raw: Any) -> str:
    """Hash a corrected-target record independently of JSON key ordering.

    This is source-map evidence, not a Lean declaration identity.  It binds a
    reviewed target to its archival baseline, governing defect, and approval
    pin so a later edit cannot silently keep old coverage credit.
    """

    return _shared_corrected_target_record_digest(raw)


def _corrected_target_primary_declaration(item: dict[str, Any]) -> str | None:
    """Return the sole paper-facing endpoint authorized for a repaired target.

    A corrected target is one complete mathematical proposition. Its map entry
    must therefore name exactly one PaperInterface theorem or lemma in
    ``lean_declarations``. Navigation aliases, proof steps, support rows, and
    semantic bridges may remain in the map, but they cannot each inherit the
    repaired statement or accumulate partial credit for it.
    """

    declarations = item.get("lean_declarations")
    if not isinstance(declarations, list) or len(declarations) != 1:
        return None
    declaration = declarations[0]
    if not isinstance(declaration, str) or not declaration.strip():
        return None
    return declaration.strip()


def _corrected_target_semantic_bundle_declarations(item: dict[str, Any]) -> list[str]:
    """Return an explicit non-credit semantic bundle for a corrected model.

    A corrected theorem has one paper-facing endpoint. A corrected source
    algorithm or model may instead have several bounded declarations that each
    need the same source-to-Lean comparison; this is review input, not extra
    theorem coverage.
    """

    if str(item.get("inventory_role") or "").strip() != "source_semantic_declaration":
        return []
    if isinstance(item.get("semantic_contract"), dict):
        return []
    declarations = _normalize_string_list(item.get("lean_declarations"))
    if not declarations or len(declarations) != len(set(declarations)):
        return []
    return declarations


def _corrected_target_coverage_rows_match_primary(
    primary_declaration: str,
    review_rows: list[str],
    source_inventory: object,
    paper_name: str,
) -> bool:
    """Accept the configured endpoint or its unique dashboard-local row name.

    Source maps retain fully qualified Lean declarations, while a dashboard row
    is named by the final PaperInterface declaration component. This is only a
    navigation translation: a short name is accepted for a corrected target
    when it uniquely identifies a configured route in this paper's
    PaperInterface. The normal coverage checks still require an exact current
    elaborated signature and a semantic source route.
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
    if not isinstance(source_inventory, dict):
        return False

    configured_routes: set[str] = set()
    for item in source_inventory.values():
        if not isinstance(item, dict):
            continue
        declarations = item.get("lean_declarations")
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


def source_item_direct_coverage_declarations(item: dict[str, Any]) -> list[str]:
    """Return the declarations eligible for direct source coverage.

    Only ``lean_declarations`` designates a paper-facing source route.
    ``proof_lean_declarations`` and semantic bridge fields document proof or
    translation support, but are not themselves evidence that the source
    statement was reviewed at that declaration. ``aliases`` are a compatibility
    fallback only for legacy records with no explicit paper-facing declaration
    route at all; they can never supplement an explicit route or select a
    partial wrapper.
    """

    if _source_item_is_corrected_target(item):
        primary = _corrected_target_primary_declaration(item)
        return [primary] if primary else []

    names = _normalize_string_list(item.get("lean_declarations"))
    if names:
        return list(dict.fromkeys(names))
    return list(dict.fromkeys(_normalize_string_list(item.get("aliases"))))


def source_item_statement_routing_declarations(item: dict[str, Any]) -> list[str]:
    """Return rows that need the source text for a semantic comparison.

    A declared semantic bridge can receive the source statement as comparison
    input, because the audit must check whether it actually transports the
    source model to the paper-facing endpoint. That routing does *not* grant
    source-coverage or proof credit: those remain restricted to
    ``source_item_direct_coverage_declarations`` and the independently checked
    bridge contract. A configured proposition specification likewise needs the
    canonical source statement as comparison input, but its declaration label
    supplies no coverage or proof evidence. Aliases and proof/support
    declarations remain excluded. Corrected targets route their corrected text
    to the one explicit endpoint and to configured specifications only; the
    archival statement is never attributed to a helper or bridge.
    """

    direct = source_item_direct_coverage_declarations(item)
    routed = list(direct)
    routed.extend(_source_item_specification_statement_routing_declarations(item))
    if _source_item_is_corrected_target(item):
        if not routed:
            routed.extend(_corrected_target_semantic_bundle_declarations(item))
        return list(dict.fromkeys(routed))
    for field in SEMANTIC_BRIDGE_DECLARATION_FIELDS:
        routed.extend(_normalize_string_list(item.get(field)))
    return list(dict.fromkeys(routed))


def _source_item_specification_statement_routing_declarations(
    item: dict[str, Any],
) -> list[str]:
    """Return configured Spec navigation labels needing comparison text only."""

    routed = _normalize_string_list(item.get("spec_lean_declarations"))
    contract = item.get("semantic_contract")
    if isinstance(contract, dict):
        specification = contract.get("spec_declaration")
        if isinstance(specification, str) and specification.strip():
            routed.append(specification.strip())
    return list(dict.fromkeys(routed))


def _source_item_corrected_target_metadata_error(item: dict[str, Any]) -> str:
    """Return a compact fail-closed error for dashboard corrected-target use."""

    if not _source_item_is_corrected_target(item):
        return "source item is not marked corrected_source_statement"
    primary = _corrected_target_primary_declaration(item)
    semantic_bundle = _corrected_target_semantic_bundle_declarations(item)
    if primary is None and not semantic_bundle:
        return (
            "lean_declarations must name one complete corrected-target endpoint "
            "or a bounded source-semantic declaration bundle"
        )
    if _normalize_string_list(item.get("proof_lean_declarations")):
        return (
            "proof_lean_declarations is prohibited for corrected_source_statement; "
            "move helper proofs to support_lean_declarations"
        )
    target = _source_item_corrected_target(item)
    if target is None:
        return "source item has no valid structured corrected_target"
    if target.get("archival_equivalence_claimed") is not False:
        return "corrected_target must explicitly set archival_equivalence_claimed to false"
    archival = normalize_statement(str(item.get("statement") or ""))
    corrected, _ = _source_item_coverage_statement(item)
    if not archival or not corrected or archival == corrected:
        return "corrected_target must differ from the archival source statement"
    governing = _normalize_string_list(target.get("governing_defect_ids"))
    routed = _normalize_string_list(item.get("source_defect_ids"))
    if not governing or not set(governing).issubset(set(routed)):
        return "corrected_target governing_defect_ids must be a nonempty subset of source_defect_ids"
    if not str(target.get("archival_source_locator") or "").strip():
        return "corrected_target has no archival source locator"
    archival_quote_digest = str(
        target.get("archival_source_quote_sha256") or ""
    ).strip().lower()
    if not re.fullmatch(r"[0-9a-f]{64}", archival_quote_digest):
        return "corrected_target has no valid archival source quote digest"
    approval = target.get("approval")
    if not isinstance(approval, dict):
        return "corrected_target has no structured approval"
    if str(approval.get("target_statement_sha256") or "").strip().lower() != statement_digest(
        corrected
    ):
        return "corrected_target approval has a stale target statement digest"
    if str(target.get("corrected_target_sha256") or "").strip().lower() != corrected_target_digest(
        target
    ):
        return "corrected_target has a stale corrected-target record digest"
    recorded_review_digest = str(
        target.get("corrected_target_review_sha256") or ""
    ).strip().lower()
    if recorded_review_digest and recorded_review_digest != corrected_target_review_digest(
        target
    ):
        return "corrected_target has a stale corrected-target review digest"
    return ""


def lean_statement_digest_candidates(
    lean_statement: str, interface_source: str = ""
) -> set[str]:
    """Return acceptable Lean-statement digests for freshness checks.

    `lean_statement` may include a rendered `#check` preview when the local Lean
    subprocess succeeds. `interface_source` is the source-level declaration text
    from the paper-facing Lean file. Sidecar freshness must remain stable when
    CI cannot render the optional preview and falls back to source text.
    """

    digests: set[str] = set()
    for text in (interface_source, lean_statement):
        if text and text.strip():
            digests.add(statement_digest(text))
            # Source-record semantic-parent receipts identify the exact
            # declaration bytes, whereas ordinary dashboard statement reviews
            # use the normalized display digest.  Both are current only for
            # the same source text, so retain the literal digest as a
            # compatible freshness candidate instead of treating a
            # byte-pinned source-assumption receipt as stale merely because
            # its whitespace is significant to the source-record ledger.
            digests.add(hashlib.sha256(text.encode("utf-8")).hexdigest())
    return digests


def source_metadata_digest(source_status: str, source_note: str) -> str:
    """Digest source-provenance metadata that should invalidate old reviews."""

    status = normalize_statement(source_status)
    note = normalize_statement(source_note)
    if not status and not note:
        return ""
    direct_statuses = {
        "direct paper definition",
        "direct paper statement",
        "direct paper formula",
        "direct source text",
        "direct source formula",
        "byte-pinned verbatim source input",
    }
    if status.lower() in direct_statuses and not note:
        return ""
    return statement_digest(f"{status}\n{note}")


def strip_qualified_identifiers(value: str) -> str:
    """Drop long qualified Lean identifiers (`A.B.C`) while preserving base names."""

    return re.sub(
        r"\b([A-Za-z_][A-Za-z0-9_']*\.)+([A-Za-z_][A-Za-z0-9_']*)",
        r"\2",
        value,
    )


def _apply_latex_token_mapping(raw: str) -> str:
    """Apply a compact symbol-to-LaTeX mapping."""

    value = raw.strip().replace("\n", " ")
    value = re.sub(r"\s+", " ", value).strip()
    if not value:
        return ""
    for old, new in LEAN_TO_TEX_TOKENS:
        value = value.replace(old, new)
    for symbol in ("->", "=>", "<->", "<=>"):
        if symbol in value:
            value = value.replace(symbol, " " + symbol + " ")
    return value[:AGENT_PREVIEW_MAX_LEN]


def lean_to_latex_statement(raw: str) -> str:
    """Generate a compact, heuristic TeX-like draft from a Lean declaration signature."""

    if not raw:
        return ""
    value = raw.strip().replace("\n", " ")
    value = re.sub(r"\s+", " ", value).strip()
    if not value:
        return ""
    if ":= by" in value:
        value = value.split(":= by", 1)[0].rstrip()
    value = AGENT_PREVIEW_TOKEN_RE.sub("", value, count=1)
    value = re.sub(r"\s*:\s*[^:=]+:=", " := ", value, count=1)
    value = value.replace(":=", "=")
    value = value.strip().strip(",")
    return _apply_latex_token_mapping(value)


def lean_check_to_latex_statement(raw: str) -> str:
    """Map Lean #check output type text to compact TeX-like form."""

    if not raw:
        return ""
    value = strip_qualified_identifiers(raw)
    return _apply_latex_token_mapping(value)


def _parse_lean_check_previews(output: str, theorem_names: list[str]) -> dict[str, str]:
    """Parse Lean `#check` output into declaration-name to type-text map."""

    names_sorted = sorted(theorem_names, key=len, reverse=True)
    captured: dict[str, list[str]] = {}
    active: str | None = None
    for raw_line in output.splitlines():
        line = raw_line.rstrip()
        matched = False
        for name in names_sorted:
            pattern = rf"^@?{re.escape(name)}\s*:\s*(.*)$"
            match = re.match(pattern, line)
            if not match:
                continue
            body = match.group(1).strip()
            captured[name] = []
            if body:
                captured[name].append(body)
            active = name
            matched = True
            break
        if matched:
            continue
        # Lean's pretty-printer does not indent every continuation. In
        # particular, `let`/`have` chains can begin in column zero. The script
        # contains only #check commands, so everything up to the next known
        # declaration header belongs to the active type preview.
        if active is not None and line.strip():
            captured[active].append(line.strip())

    result: dict[str, str] = {}
    for name, parts in captured.items():
        text = " ".join(parts).strip()
        if text:
            result[name] = text
    return result


def run_lean_check_previews(
    paper_folder: Path,
    theorem_names: list[str],
    timeout_seconds: int = AGENT_PREVIEW_CHECK_TIMEOUT,
    source_file: Path | None = None,
) -> dict[str, str]:
    """Ask Lean for #check output on Lean declarations, with fallback on failure."""

    if not theorem_names:
        return {}
    canonical_names = sorted(set(theorem_names))
    module_file = source_file or find_review_source_file(paper_folder)
    if module_file is None or not _dashboard_is_file(module_file):
        return {}
    cache_key = f"{paper_folder.resolve()}::{module_file.name}::{'|'.join(canonical_names)}"
    if cache_key in AGENT_PREVIEW_CACHE:
        return AGENT_PREVIEW_CACHE[cache_key]

    import_module = review_source_module(paper_folder, module_file)
    lines = [
        f"import {import_module}",
        "set_option pp.universes false",
        "",
    ]
    for name in canonical_names:
        lines.append(f"#check (@{name})")
    script = "\n".join(lines) + "\n"

    with tempfile.TemporaryDirectory() as tmpdir:
        script_path = Path(tmpdir) / "review_agent_preview.lean"
        script_path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(script_path)],
                cwd=str(ROOT),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            )
            stdout_bytes, _stderr = proc.communicate(timeout=timeout_seconds)
        except (OSError, subprocess.TimeoutExpired):
            if "proc" in locals():
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    proc.communicate(timeout=1)
                except (OSError, subprocess.TimeoutExpired):
                    pass
            AGENT_PREVIEW_CACHE[cache_key] = {}
            return {}

    stdout = stdout_bytes.decode("utf-8", errors="replace")

    if proc.returncode != 0 and not stdout.strip():
        AGENT_PREVIEW_CACHE[cache_key] = {}
        return {}

    checked = _parse_lean_check_previews(stdout, canonical_names)
    AGENT_PREVIEW_CACHE[cache_key] = checked
    return checked


def agent_preview_comment(
    comment: str | None, raw_statement: str, check_statement: str | None = None
) -> str:
    """Prefer Lean #check output, then signature heuristic, then doc-comment fallback."""

    if check_statement:
        translated = lean_check_to_latex_statement(check_statement)
        if translated:
            return translated
    translated = lean_to_latex_statement(raw_statement)
    if translated:
        return translated
    if comment:
        text = re.sub(r"\s+", " ", comment).strip()
        return text[:AGENT_PREVIEW_MAX_LEN]
    return "(no auto-generated preview available)"


def parse_report_texts(report_path: Path) -> dict[str, str]:
    """Extract theorem-level paper statement summaries from final report bullets."""

    statements: dict[str, str] = {}
    lines = _dashboard_read_text(report_path).splitlines()
    ignored_sections = {"statement translation audit"}
    active_section = ""
    i = 0
    while i < len(lines):
        line = lines[i]
        heading = re.match(r"^#{2,6}\s+(.+?)\s*$", line)
        if heading:
            active_section = re.sub(
                r"^\d+\.\s*", "", heading.group(1).strip().lower()
            )
            i += 1
            continue
        if active_section in ignored_sections:
            i += 1
            continue
        match = REPORT_CLAUSE_RE.match(line)
        if not match:
            i += 1
            continue

        name = match.group("name")
        text = match.group("text").strip()
        i += 1
        extras: list[str] = []
        while i < len(lines):
            nxt = lines[i]
            if not nxt.strip():
                i += 1
                continue
            if nxt.lstrip().startswith("- "):
                break
            if re.match(r"^\s{2,}\S", nxt):
                extras.append(nxt.strip())
                i += 1
                continue
            break
        if extras:
            text = " ".join([text] + extras).strip()
        if text:
            _add_statement_variant(statements, name, text)
        else:
            _add_statement_variant(statements, name, "(No extracted paper statement text found.)")
    return statements


def find_paper_tex_source(folder: Path) -> Path | None:
    """Find the likely paper TeX source used for display text extraction."""

    inputs = _dashboard_audit_inputs()
    if inputs is not None:
        candidates = inputs.existing_files_under(folder, suffix=".tex")
        by_name = {path.name: path for path in candidates}
        for rel in PAPER_TEX_PRIORITY:
            candidate = by_name.get(rel.format(name=folder.name))
            if candidate is not None:
                return candidate
        return next(
            (
                path
                for path in candidates
                if path.name.lower()
                not in {"dependencydag.tex", "dependency_dag.tex", "paperinterface.tex"}
            ),
            None,
        )
    for rel in PAPER_TEX_PRIORITY:
        candidate = folder / rel.format(name=folder.name)
        if candidate.exists() and candidate.is_file():
            return candidate

    for candidate in sorted(
        p
        for p in folder.glob("*.tex")
        if p.is_file()
    ):
        if candidate.name.lower() in {"dependencydag.tex", "dependency_dag.tex", "paperinterface.tex"}:
            continue
        return candidate
    return None


def parse_paper_tex_statements(folder: Path) -> dict[str, str]:
    """Extract labeled theorem-like statements from a LaTeX source file."""

    source = find_paper_tex_source(folder)
    if source is None:
        return {}

    try:
        lines = _dashboard_read_text(source).splitlines()
    except OSError:
        return {}

    statements: dict[str, str] = {}
    in_env = False
    active_label: str | None = None
    active_kind: str | None = None
    active_lines: list[str] = []

    for raw_line in lines:
        line = raw_line.strip()

        if not in_env:
            open_match = THEOREM_ENV_OPEN_RE.match(line)
            if open_match:
                in_env = True
                active_kind = open_match.group(1)
                active_label = None
                active_lines = [raw_line]
                continue
            else:
                continue

        if in_env and active_kind is not None:
            active_lines.append(raw_line)
            label_match = THEOREM_LABEL_RE.search(raw_line)
            if label_match and not active_label:
                active_label = label_match.group(1).strip()

            close_match = THEOREM_ENV_CLOSE_RE.match(line)
            if close_match:
                if close_match.group(1) == active_kind:
                    if active_label:
                        text = " ".join(active_lines)
                        text = re.sub(r"%.*$", "", text)
                        text = THEOREM_ENV_OPEN_RE.sub("", text)
                        text = THEOREM_ENV_CLOSE_RE.sub("", text)
                        text = THEOREM_LABEL_RE.sub("", text)
                        text = re.sub(r"\s+", " ", text).strip()
                        if text:
                            _add_statement_variant(statements, active_label, text)
                in_env = False
                active_label = None
                active_kind = None
                active_lines = []

    return statements


def _clean_paper_text_statement(lines: list[str]) -> str:
    """Clean a statement block extracted from a PDF text dump."""

    cleaned: list[str] = []
    blank_pending = False
    for raw_line in lines:
        line = raw_line.replace("\f", "").rstrip()
        if not line.strip():
            blank_pending = bool(cleaned)
            continue
        if line.strip().isdigit():
            continue
        if blank_pending and cleaned:
            cleaned.append("")
        cleaned.append(line)
        blank_pending = False
    return "\n".join(cleaned).strip()


def parse_paper_text_statements(folder: Path) -> dict[str, str]:
    """Extract numbered paper statements from `source.txt` when no TeX is present."""

    source = find_paper_text(folder)
    if source is None:
        return {}

    try:
        lines = _dashboard_read_text(source).splitlines()
    except OSError:
        return {}

    statements: dict[str, str] = {}
    active_key: str | None = None
    active_kind: str | None = None
    active_number: str | None = None
    active_lines: list[str] = []

    def flush() -> None:
        nonlocal active_key, active_kind, active_number, active_lines
        if active_key:
            text = _clean_paper_text_statement(active_lines)
            if text:
                _add_statement_variant(statements, active_key, text)
                if active_kind and active_number:
                    _add_statement_variant(
                        statements,
                        f"{active_kind.lower()}_{active_number.replace('.', '_').lower()}",
                        text,
                    )
        active_key = None
        active_kind = None
        active_number = None
        active_lines = []

    for raw_line in lines:
        stripped = raw_line.strip()
        label_match = PAPER_TEXT_STATEMENT_LABEL_RE.match(stripped)
        if label_match:
            flush()
            active_kind = label_match.group("kind")
            active_number = label_match.group("number")
            active_key = _paper_statement_key(active_kind, active_number)
            active_lines = [raw_line]
            continue

        if active_key is not None and PAPER_TEXT_STATEMENT_STOP_RE.match(stripped):
            flush()
            continue

        if active_key is not None:
            active_lines.append(raw_line)

    flush()
    return statements


def parse_paper_statement_map(folder: Path) -> dict[str, str]:
    """Load explicit paper-source line ranges for dashboard statements."""

    map_path = folder / PAPER_STATEMENT_MAP_FILE
    if not _dashboard_is_file(map_path):
        return {}

    payload = _dashboard_json_payload(map_path)
    if payload is None:
        return {}

    raw_items = payload.get("items", payload) if isinstance(payload, dict) else {}
    if not isinstance(raw_items, dict):
        return {}

    statements: dict[str, str] = {}
    text_cache: dict[str, list[str]] = {}
    for key, raw_item in raw_items.items():
        if not isinstance(key, str) or not key.strip() or not isinstance(raw_item, dict):
            continue
        direct_statement = str(raw_item.get("statement") or "").strip()
        if direct_statement:
            archival_text = normalize_statement(direct_statement)
            corrected_target = raw_item.get("corrected_target")
            corrected_text = ""
            if (
                str(raw_item.get("coverage_status") or "").strip().lower()
                == CORRECTED_SOURCE_STATEMENT_STATUS
                and isinstance(corrected_target, dict)
                and corrected_target.get("schema") == CORRECTED_TARGET_SCHEMA
            ):
                corrected_text = normalize_statement(
                    str(corrected_target.get("statement") or "")
                )
            # The map key identifies archival source text. A corrected target
            # may be routed only to the explicitly designated direct endpoint.
            # Navigation aliases and support declarations never inherit a
            # source statement, even for ordinary rows: an alias is not a
            # semantic comparison and a conjunction of helpers is not itself
            # evidence for a paper-facing theorem.
            _add_statement_variant(statements, key.strip(), archival_text)
            primary_declaration = _corrected_target_primary_declaration(raw_item)
            corrected_declarations = (
                [primary_declaration]
                if primary_declaration
                else _corrected_target_semantic_bundle_declarations(raw_item)
            )
            if corrected_text and corrected_declarations:
                for declaration in list(
                    dict.fromkeys(
                        corrected_declarations
                        + _source_item_specification_statement_routing_declarations(
                            raw_item
                        )
                    )
                ):
                    _add_statement_variant(statements, declaration, corrected_text)
            else:
                for declaration in source_item_statement_routing_declarations(raw_item):
                    _add_statement_variant(statements, declaration, archival_text)
            continue
        source_text_file = str(raw_item.get("source_text_file") or "source.txt").strip()
        if not source_text_file or "/" in source_text_file or "\\" in source_text_file:
            continue
        try:
            start_line = int(raw_item.get("start_line"))
            end_line = int(raw_item.get("end_line"))
        except (TypeError, ValueError):
            continue
        if start_line <= 0 or end_line < start_line:
            continue

        source_path = folder / source_text_file
        try:
            lines = text_cache[source_text_file]
        except KeyError:
            try:
                lines = _dashboard_read_text(source_path).splitlines()
            except OSError:
                continue
            text_cache[source_text_file] = lines

        if start_line > len(lines):
            continue
        selected = lines[start_line - 1 : min(end_line, len(lines))]
        text = _clean_paper_text_statement(selected)
        if not text:
            continue
        _add_statement_variant(statements, key.strip(), text)
        for declaration in source_item_statement_routing_declarations(raw_item):
            _add_statement_variant(statements, declaration, text)
    return statements


def paper_statement_inventory(folder: Path) -> dict[str, dict[str, Any]]:
    """Return canonical source-paper statements for paper-level coverage audit.

    `audit/paper_statement_map.json` is the canonical source inventory because
    it separates source items from aliases.  Fallback extraction is intentionally
    lightweight and is best treated as a prompt scaffold, not a closeout-quality
    source inventory.
    """

    map_path = folder / PAPER_STATEMENT_MAP_FILE
    if _dashboard_is_file(map_path):
        payload = _dashboard_json_payload(map_path) or {}
        raw_items = payload.get("items", payload) if isinstance(payload, dict) else {}
        if isinstance(raw_items, dict):
            # Scoped computational illustrations need a source artifact identity and
            # an exact locator.  Preserve the map-level pin on each inventory item
            # so the source-first coverage check can enforce that requirement before
            # an item is allowed to leave the theorem-review lane.
            (
                map_source_artifact_path,
                map_source_artifact_sha256,
            ) = semantic_review_source_identity(payload)
            map_source_anchor_evidence_required = (
                payload.get("source_anchor_evidence_required") is True
            )
            inventory: dict[str, dict[str, Any]] = {}
            text_cache: dict[str, list[str]] = {}
            for raw_key, raw_item in raw_items.items():
                key = str(raw_key or "").strip()
                if not key or not isinstance(raw_item, dict):
                    continue
                direct_statement = str(raw_item.get("statement") or "").strip()
                source_text_file = str(raw_item.get("source_text_file") or "source.txt").strip()
                source_location = str(raw_item.get("source_location") or "").strip()
                source_url = str(raw_item.get("source_url") or payload.get("source_url") or "").strip()
                source_note = str(raw_item.get("source_note") or "").strip()
                source_status = str(raw_item.get("source_status") or "").strip()
                text = ""
                if direct_statement:
                    text = normalize_statement(direct_statement)
                else:
                    if not source_text_file or "/" in source_text_file or "\\" in source_text_file:
                        continue
                    try:
                        start_line = int(raw_item.get("start_line"))
                        end_line = int(raw_item.get("end_line"))
                    except (TypeError, ValueError):
                        continue
                    if start_line <= 0 or end_line < start_line:
                        continue
                    source_path = folder / source_text_file
                    try:
                        lines = text_cache[source_text_file]
                    except KeyError:
                        try:
                            lines = _dashboard_read_text(source_path).splitlines()
                        except OSError:
                            continue
                        text_cache[source_text_file] = lines
                    if start_line > len(lines):
                        continue
                    selected = lines[start_line - 1 : min(end_line, len(lines))]
                    text = _clean_paper_text_statement(selected)
                    if not source_location:
                        source_location = f"{source_text_file}:{start_line}-{end_line}"
                if not text:
                    continue
                aliases = [
                    str(alias).strip()
                    for alias in raw_item.get("aliases", []) or []
                    if isinstance(alias, str) and alias.strip()
                ]
                inventory[key] = {
                    "source_item_key": key,
                    "title": str(raw_item.get("title") or "").strip(),
                    "statement": text,
                    "aliases": aliases,
                    # This is source-presentation metadata, not a Lean route.
                    # Preserve it through the prompt projection so ordinary
                    # coverage counts the canonical result once even when its
                    # proof restates the same theorem or lemma later.
                    "source_presentation_alias": raw_item.get(
                        "source_presentation_alias"
                    ),
                    "source": PAPER_STATEMENT_MAP_FILE,
                    "coverage_status": str(
                        raw_item.get("coverage_status") or ""
                    ).strip().lower(),
                    "protocol_role": str(
                        raw_item.get("protocol_role") or ""
                    ).strip().lower(),
                    "corrected_target": raw_item.get("corrected_target"),
                    "source_kind": str(raw_item.get("source_kind") or "").strip().lower(),
                    "claim_bearing": raw_item.get("claim_bearing"),
                    "source_scope_classification": str(
                        raw_item.get("source_scope_classification") or ""
                    ).strip().lower(),
                    "user_approved_scope_exclusion": raw_item.get(
                        "user_approved_scope_exclusion"
                    ),
                    "scope_reason": str(raw_item.get("scope_reason") or "").strip(),
                    "source_evidence": str(raw_item.get("source_evidence") or "").strip(),
                    "source_artifact_path": str(
                        raw_item.get("source_artifact_path")
                        or map_source_artifact_path
                        or ""
                    ).strip(),
                    "source_artifact_sha256": str(
                        raw_item.get("source_artifact_sha256")
                        or map_source_artifact_sha256
                        or ""
                    ).strip(),
                    "canonical_source_artifact_path": map_source_artifact_path,
                    "canonical_source_artifact_sha256": map_source_artifact_sha256,
                    "source_anchor_evidence_required": (
                        raw_item.get("source_anchor_evidence_required") is True
                        or map_source_anchor_evidence_required
                    ),
                    "source_anchor_evidence": raw_item.get(
                        "source_anchor_evidence"
                    ),
                    "semantic_context_requirements": raw_item.get(
                        "semantic_context_requirements"
                    ),
                    "source_defect_ids": _normalize_string_list(
                        raw_item.get("source_defect_ids")
                    ),
                    "support_lean_declarations": _normalize_string_list(
                        raw_item.get("support_lean_declarations")
                    ),
                    "spec_lean_declarations": _normalize_string_list(
                        raw_item.get("spec_lean_declarations")
                    ),
                    "semantic_contract": raw_item.get("semantic_contract"),
                    "lean_declarations": _normalize_string_list(
                        raw_item.get("lean_declarations")
                    ),
                    "proof_lean_declarations": _normalize_string_list(
                        raw_item.get("proof_lean_declarations")
                    ),
                    "source_location": source_location,
                    "source_url": source_url,
                    "source_note": source_note,
                    "source_status": source_status,
                    "statement_sha256": statement_digest(text),
                }
                if "model_convention_ids" in raw_item:
                    # Preserve even malformed raw metadata. Downstream semantic
                    # reuse must reject an empty, duplicate, or unresolved
                    # convention receipt instead of treating it as absent.
                    inventory[key]["model_convention_ids"] = raw_item.get(
                        "model_convention_ids"
                    )
                if "inventory_role" in raw_item:
                    # Preserve the absence of this v11 support-lane marker on
                    # historic ordinary items.  An empty synthetic field would
                    # alter their source semantic pins despite no source or
                    # semantic-routing change.
                    inventory[key]["inventory_role"] = str(
                        raw_item.get("inventory_role") or ""
                    ).strip().lower()
                if SOURCE_DEFINITION_PARTITION_FIELD in raw_item:
                    inventory[key][SOURCE_DEFINITION_PARTITION_FIELD] = raw_item.get(
                        SOURCE_DEFINITION_PARTITION_FIELD
                    )
            if inventory:
                return inventory

    tex_statements = parse_paper_tex_statements(folder)
    if tex_statements:
        return {
            key: {
                "statement": value,
                "aliases": [],
                "source": find_paper_tex_source(folder).name if find_paper_tex_source(folder) else "",
                "source_location": key,
                "statement_sha256": statement_digest(value),
            }
            for key, value in sorted(tex_statements.items())
            if key and value
        }

    text_statements = parse_paper_text_statements(folder)
    locations = parse_paper_text_statement_locations(folder)
    if locations:
        inventory = {}
        for location in locations:
            key = str(location.get("key") or "").strip()
            value = text_statements.get(key)
            if key and value:
                inventory[key] = {
                    "statement": value,
                    "aliases": [],
                    "source": find_paper_text(folder).name if find_paper_text(folder) else "",
                    "source_location": f"page {location.get('page')}, line {location.get('line_number')}",
                    "statement_sha256": statement_digest(value),
                }
        return inventory
    return {}


def paper_statement_map_payload(folder: Path) -> dict[str, Any]:
    """Load the canonical source-map object when one is available.

    The full source inventory remains available for an explicit deep audit. The
    ordinary closeout selector below reads only source-presentation metadata
    from this payload; it never uses map keys or Lean declaration names.
    """

    map_path = folder / PAPER_STATEMENT_MAP_FILE
    if not _dashboard_is_file(map_path):
        return {}
    payload = _dashboard_json_payload(map_path)
    return payload if isinstance(payload, dict) else {}


def source_component_route_key(
    source_item_key: str, source_anchor_sha256: str
) -> str:
    """Return the stable identity for a quoted source subclaim.

    A source-map item can contain several mathematical components.  The map
    item key is a navigation handle, not evidence that every paper-interface
    row establishes its whole statement.  This key instead binds a component
    route to the parent source item and to the SHA-256 of the exact quoted
    source bytes.  Lean declaration names are intentionally absent from the
    identity.
    """

    return (
        f"{source_item_key}::source-component::"
        f"{source_anchor_sha256.strip().lower()}"
    )


def paper_source_component_route_inventory(folder: Path) -> dict[str, dict[str, Any]]:
    """Return source-map component anchors as route-only source inventory.

    Components are not added to :func:`paper_statement_inventory`: doing so
    would incorrectly enlarge named-result coverage.  They are available only
    to v10 statement-route validation, where a formula row may honestly review
    one quoted source component rather than a parent theorem's full text.
    Invalid or unpinned component anchors are omitted, so a purported route to
    one fails closed as an unknown source item.
    """

    payload = paper_statement_map_payload(folder)
    raw_items = payload.get("items") if isinstance(payload, dict) else None
    if not isinstance(raw_items, dict):
        return {}

    component_inventory: dict[str, dict[str, Any]] = {}
    for raw_parent_key, raw_parent in raw_items.items():
        parent_key = str(raw_parent_key or "").strip()
        if not parent_key or not isinstance(raw_parent, dict):
            continue
        raw_components = raw_parent.get("source_components")
        if not isinstance(raw_components, list):
            continue
        source_kind = str(raw_parent.get("source_kind") or "").strip().lower()
        source_status = str(raw_parent.get("source_status") or "").strip()
        source_url = str(
            raw_parent.get("source_url") or payload.get("source_url") or ""
        ).strip()
        for raw_component in raw_components:
            if not isinstance(raw_component, dict):
                continue
            source_location = str(raw_component.get("source_location") or "").strip()
            anchors = raw_component.get("source_anchor_evidence")
            if not source_location or not isinstance(anchors, list):
                continue
            for raw_anchor in anchors:
                if not isinstance(raw_anchor, dict):
                    continue
                quoted_text = str(raw_anchor.get("quoted_text") or "")
                anchor_sha256 = str(raw_anchor.get("quoted_text_sha256") or "").strip().lower()
                if (
                    not quoted_text.strip()
                    or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(anchor_sha256)
                    or hashlib.sha256(quoted_text.encode("utf-8")).hexdigest()
                    != anchor_sha256
                ):
                    continue
                statement = normalize_statement(quoted_text)
                if not statement:
                    continue
                key = source_component_route_key(parent_key, anchor_sha256)
                # Duplicate quoted bytes within the same parent describe the
                # same component route.  Do not guess between inconsistent
                # locators; preserving the first one is safe only when it is
                # exactly identical.
                existing = component_inventory.get(key)
                if existing is not None:
                    if (
                        existing.get("source_location") != source_location
                        or existing.get("statement") != statement
                    ):
                        component_inventory.pop(key, None)
                    continue
                component_inventory[key] = {
                    "statement": statement,
                    "statement_sha256": statement_digest(statement),
                    "source_location": source_location,
                    "source_kind": source_kind,
                    "source_status": source_status,
                    "source_url": source_url,
                    "source_component_of": parent_key,
                    "source_component_label": str(
                        raw_component.get("component") or ""
                    ).strip(),
                    "source_component_anchor_sha256": anchor_sha256,
                    "source_anchor_evidence": [raw_anchor],
                }
    return component_inventory


def source_definition_component_route_key(
    source_item_key: str,
    semantic_clause_sha256: str,
    source_anchor_sha256: str,
) -> str:
    """Return a navigation key for one semantically identified definition clause.

    The parent key is only a lookup handle.  Validation and reuse bind the route
    to the clause digest, exact source-anchor identity, parent statement
    digest, and the complete partition digest; no Lean declaration name
    participates.
    """

    return (
        f"{source_item_key}::source-definition-clause::"
        f"{semantic_clause_sha256.strip().lower()}::"
        f"{source_anchor_sha256.strip().lower()}"
    )


def _definition_partition_digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def _definition_component_anchor_identity(
    anchors: list[dict[str, Any]],
) -> str:
    """Return a stable identity for one component's exact source anchors.

    Preserve the historical single-quote identity so existing valid routes do
    not churn.  A clause supported by discontiguous source spans instead gets
    a domain-separated digest of the canonical anchor set.  Literal quote
    bytes enter through their individual SHA-256 values; paths and line ranges
    prevent equal text at different source locations from sharing an identity.
    """

    if len(anchors) == 1:
        return str(anchors[0]["quoted_text_sha256"])
    return _definition_partition_digest(
        {
            "schema": 1,
            "kind": "source_definition_component_anchor_set",
            "anchors": [
                {
                    "path": anchor["path"],
                    "line_start": anchor["line_start"],
                    "line_end": anchor["line_end"],
                    "quoted_text_sha256": anchor["quoted_text_sha256"],
                }
                for anchor in anchors
            ],
        }
    )


def source_definition_partition_record(
    source_item: Mapping[str, Any],
) -> tuple[dict[str, Any] | None, list[str]]:
    """Validate and canonicalize an opt-in semantic definition partition.

    A quoted paragraph can state several independent clauses.  Quote identity
    alone therefore cannot identify a component.  Each component is bound to
    both an auditor-written semantic clause digest and exact quoted bytes, while
    the parent record certifies that the clauses are a complete, nonoverlapping
    partition of the whole source definition.
    """

    raw = source_item.get(SOURCE_DEFINITION_PARTITION_FIELD)
    if raw is None:
        return None, []
    if not isinstance(raw, Mapping):
        return None, [f"{SOURCE_DEFINITION_PARTITION_FIELD} must be an object"]
    if _source_item_is_corrected_target(dict(source_item)):
        return None, [
            f"{SOURCE_DEFINITION_PARTITION_FIELD} cannot replace an approved "
            "corrected-target route"
        ]

    required_fields = {
        "schema",
        "source_statement_sha256",
        "semantic_relation",
        "complete",
        "components_semantically_disjoint",
        "completeness_basis",
        "nonoverlap_basis",
        "components",
    }
    errors: list[str] = []
    if set(raw) != required_fields:
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} must contain exactly "
            + ", ".join(sorted(required_fields))
        )
    if raw.get("schema") != SOURCE_DEFINITION_PARTITION_SCHEMA:
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} schema must be "
            f"{SOURCE_DEFINITION_PARTITION_SCHEMA}"
        )

    parent_digest = str(source_item.get("statement_sha256") or "").strip().lower()
    recorded_parent_digest = str(
        raw.get("source_statement_sha256") or ""
    ).strip().lower()
    if (
        not SOURCE_ARTIFACT_SHA256_RE.fullmatch(parent_digest)
        or recorded_parent_digest != parent_digest
    ):
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} has a stale parent source "
            "statement digest"
        )
    if (
        str(raw.get("semantic_relation") or "").strip().lower()
        != SOURCE_DEFINITION_PARTITION_RELATION
    ):
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} has an invalid semantic_relation"
        )
    if raw.get("complete") is not True:
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} must certify complete=true"
        )
    if raw.get("components_semantically_disjoint") is not True:
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} must certify "
            "components_semantically_disjoint=true"
        )
    for field in ("completeness_basis", "nonoverlap_basis"):
        basis = str(raw.get(field) or "").strip()
        if len(basis) < 60 or NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(basis):
            errors.append(
                f"{SOURCE_DEFINITION_PARTITION_FIELD} lacks substantive {field}"
            )

    raw_components = raw.get("components")
    if not isinstance(raw_components, list) or len(raw_components) < 2:
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} components must contain at "
            "least two semantic clauses"
        )
        raw_components = []

    component_fields = {
        "semantic_clause",
        "semantic_clause_sha256",
        "source_location",
        "source_anchor_evidence",
    }
    raw_parent_convention_ids = source_item.get("model_convention_ids")
    parent_convention_ids: list[str] = []
    if "model_convention_ids" in source_item:
        if not isinstance(raw_parent_convention_ids, list):
            errors.append("partition parent model_convention_ids must be a nonempty list")
        else:
            parent_convention_ids = [
                value.strip()
                for value in raw_parent_convention_ids
                if isinstance(value, str) and value.strip()
            ]
            if (
                not parent_convention_ids
                or len(parent_convention_ids) != len(raw_parent_convention_ids)
                or len(set(parent_convention_ids)) != len(parent_convention_ids)
            ):
                errors.append(
                    "partition parent model_convention_ids must be a nonempty "
                    "list of unique strings"
                )
                parent_convention_ids = []
    scoped_component_fields = component_fields | {
        "source_status",
        "model_convention_ids",
    }
    parent_has_conventions = bool(parent_convention_ids)
    anchor_fields = {
        "path",
        "line_start",
        "line_end",
        "quoted_text",
        "quoted_text_sha256",
    }
    canonical_components: list[dict[str, Any]] = []
    seen_clause_digests: set[str] = set()
    seen_pairs: set[tuple[str, str]] = set()
    for index, component in enumerate(raw_components):
        label = f"{SOURCE_DEFINITION_PARTITION_FIELD} components[{index}]"
        if not isinstance(component, Mapping):
            errors.append(f"{label} must be an object")
            continue
        expected_component_fields = (
            component_fields | {"source_status"}
            if parent_has_conventions
            else component_fields
        )
        allowed_component_fields = (
            scoped_component_fields
            if parent_has_conventions
            else component_fields
        )
        if (
            not expected_component_fields <= set(component)
            or not set(component) <= allowed_component_fields
        ):
            errors.append(
                f"{label} must contain "
                + (
                    "explicit component convention scope fields"
                    if parent_has_conventions
                    else "exactly " + ", ".join(sorted(component_fields))
                )
            )
        component_status = str(component.get("source_status") or "").strip().lower()
        component_convention_ids: list[str] = []
        if parent_has_conventions:
            raw_component_ids = component.get("model_convention_ids")
            if component_status == SOURCE_DEFINITION_COMPONENT_EXACT_STATUS:
                if "model_convention_ids" in component:
                    errors.append(
                        f"{label} exact scope must omit model_convention_ids"
                    )
            elif component_status in SOURCE_DEFINITION_COMPONENT_CONVENTION_STATUSES:
                if not isinstance(raw_component_ids, list):
                    errors.append(
                        f"{label} convention scope requires nonempty model_convention_ids"
                    )
                else:
                    component_convention_ids = [
                        value.strip()
                        for value in raw_component_ids
                        if isinstance(value, str) and value.strip()
                    ]
                    if (
                        not component_convention_ids
                        or len(component_convention_ids) != len(raw_component_ids)
                        or len(set(component_convention_ids))
                        != len(component_convention_ids)
                    ):
                        errors.append(
                            f"{label} convention scope requires a nonempty list "
                            "of unique model_convention_ids"
                        )
                        component_convention_ids = []
                    extras = set(component_convention_ids) - set(
                        parent_convention_ids
                    )
                    if extras:
                        errors.append(
                            f"{label} cites convention IDs absent from its parent: "
                            + ", ".join(sorted(extras))
                        )
            else:
                errors.append(
                    f"{label} has invalid explicit source_status for a "
                    "convention-scoped partition"
                )
        semantic_clause = normalize_statement(
            str(component.get("semantic_clause") or "")
        )
        clause_digest = str(
            component.get("semantic_clause_sha256") or ""
        ).strip().lower()
        if not semantic_clause or clause_digest != statement_digest(semantic_clause):
            errors.append(f"{label} has a stale semantic_clause_sha256")
        source_location = str(component.get("source_location") or "").strip()
        if not source_location:
            errors.append(f"{label} has no source_location")
        location_anchors = [
            {
                "path": match.group("path"),
                "line_start": int(match.group("start")),
                "line_end": int(match.group("end") or match.group("start")),
            }
            for match in SOURCE_FILE_LINE_ANCHOR_RE.finditer(source_location)
        ]
        location_keys = [
            (anchor["path"], anchor["line_start"], anchor["line_end"])
            for anchor in location_anchors
        ]
        if not location_anchors:
            errors.append(f"{label} source_location has no exact file:line anchor")
        elif len(set(location_keys)) != len(location_keys):
            errors.append(f"{label} source_location duplicates a source anchor")
        anchors = component.get("source_anchor_evidence")
        if not isinstance(anchors, list) or not anchors:
            errors.append(f"{label} must contain a nonempty pinned source-quote list")
            continue

        canonical_anchors: list[dict[str, Any]] = []
        matched_locations: set[int] = set()
        for anchor_index, anchor in enumerate(anchors):
            anchor_label = f"{label} source_anchor_evidence[{anchor_index}]"
            if not isinstance(anchor, Mapping):
                errors.append(f"{anchor_label} must be an object")
                continue
            if set(anchor) != anchor_fields:
                errors.append(
                    f"{anchor_label} must contain exactly "
                    + ", ".join(sorted(anchor_fields))
                )
            path = str(anchor.get("path") or "").strip()
            raw_line_start = anchor.get("line_start")
            raw_line_end = anchor.get("line_end")
            valid_lines = (
                isinstance(raw_line_start, int)
                and not isinstance(raw_line_start, bool)
                and isinstance(raw_line_end, int)
                and not isinstance(raw_line_end, bool)
            )
            line_start = raw_line_start if valid_lines else 0
            line_end = raw_line_end if valid_lines else -1
            quote = str(anchor.get("quoted_text") or "")
            quote_digest = str(
                anchor.get("quoted_text_sha256") or ""
            ).strip().lower()
            if not path or line_start <= 0 or line_end < line_start:
                errors.append(
                    f"{anchor_label} has an invalid path or line range"
                )
            if (
                not quote
                or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(quote_digest)
                or hashlib.sha256(quote.encode("utf-8")).hexdigest()
                != quote_digest
            ):
                errors.append(f"{anchor_label} has a stale quoted_text_sha256")

            matching_locations = [
                location_index
                for location_index, location_anchor in enumerate(location_anchors)
                if _source_anchor_paths_match(path, location_anchor["path"])
                and line_start == location_anchor["line_start"]
                and line_end == location_anchor["line_end"]
            ]
            if len(matching_locations) != 1:
                errors.append(
                    f"{anchor_label} does not match exactly one declared source anchor"
                )
                continue
            location_index = matching_locations[0]
            if location_index in matched_locations:
                errors.append(f"{anchor_label} duplicates a declared source anchor")
                continue
            matched_locations.add(location_index)
            declared_anchor = location_anchors[location_index]
            canonical_anchors.append(
                {
                    "path": declared_anchor["path"],
                    "line_start": line_start,
                    "line_end": line_end,
                    "quoted_text": quote,
                    "quoted_text_sha256": quote_digest,
                }
            )

        if len(matched_locations) != len(location_anchors):
            errors.append(
                f"{label} must provide exactly one pinned quote for every "
                "declared source anchor"
            )
        canonical_anchors.sort(
            key=lambda anchor: (
                anchor["path"],
                anchor["line_start"],
                anchor["line_end"],
                anchor["quoted_text_sha256"],
            )
        )
        anchor_identity = (
            _definition_component_anchor_identity(canonical_anchors)
            if canonical_anchors
            else ""
        )
        pair = (clause_digest, anchor_identity)
        if clause_digest in seen_clause_digests:
            errors.append(f"{label} duplicates a semantic clause digest")
        if pair in seen_pairs:
            errors.append(
                f"{label} duplicates a semantic-clause/source-anchor pair"
            )
        seen_clause_digests.add(clause_digest)
        seen_pairs.add(pair)
        canonical_component = {
            "semantic_clause": semantic_clause,
            "semantic_clause_sha256": clause_digest,
            "source_location": source_location,
            "source_anchor_sha256": anchor_identity,
            "source_anchor_evidence": canonical_anchors,
        }
        if parent_has_conventions:
            canonical_component["source_status"] = component_status
            if component_convention_ids:
                canonical_component["model_convention_ids"] = sorted(
                    component_convention_ids
                )
        canonical_components.append(canonical_component)

    if parent_has_conventions:
        component_convention_union = {
            convention_id
            for component in canonical_components
            for convention_id in component.get("model_convention_ids", [])
        }
        if component_convention_union != set(parent_convention_ids):
            errors.append(
                "partition component convention scopes do not exactly cover "
                "the parent model_convention_ids"
            )

    if errors:
        return None, errors

    canonical_components.sort(
        key=lambda component: (
            component["semantic_clause_sha256"],
            component["source_anchor_sha256"],
            component["source_location"],
        )
    )
    partition_semantics = {
        "schema": SOURCE_DEFINITION_PARTITION_SCHEMA,
        "source_statement_sha256": parent_digest,
        "semantic_relation": SOURCE_DEFINITION_PARTITION_RELATION,
        "complete": True,
        "components_semantically_disjoint": True,
        "completeness_basis": normalize_statement(
            str(raw.get("completeness_basis") or "")
        ),
        "nonoverlap_basis": normalize_statement(
            str(raw.get("nonoverlap_basis") or "")
        ),
        "components": [
            {
                "semantic_clause": component["semantic_clause"],
                "semantic_clause_sha256": component["semantic_clause_sha256"],
                "source_location": component["source_location"],
                "source_anchor_sha256": component["source_anchor_sha256"],
            }
            for component in canonical_components
        ],
    }
    partition_digest = _definition_partition_digest(partition_semantics)
    for component in canonical_components:
        component["source_definition_component_sha256"] = (
            _definition_partition_digest(
                {
                    "schema": 1,
                    "source_statement_sha256": parent_digest,
                    "source_definition_partition_sha256": partition_digest,
                    "semantic_clause_sha256": component[
                        "semantic_clause_sha256"
                    ],
                    "source_anchor_sha256": component["source_anchor_sha256"],
                    "source_location": component["source_location"],
                    **(
                        {
                            "source_status": component["source_status"],
                            "model_convention_ids": component.get(
                                "model_convention_ids", []
                            ),
                        }
                        if parent_has_conventions
                        else {}
                    ),
                }
            )
        )
    return {
        **partition_semantics,
        "source_definition_partition_sha256": partition_digest,
        "components": canonical_components,
    }, []


def paper_source_definition_component_route_inventory(
    folder: Path,
) -> dict[str, dict[str, Any]]:
    """Return valid definition-partition clauses as route-only inventory."""

    source_inventory = paper_statement_inventory(folder)
    component_inventory: dict[str, dict[str, Any]] = {}
    for parent_key, source_item in source_inventory.items():
        if (
            str(source_item.get("source_kind") or "").strip().lower()
            not in SOURCE_DEFINITION_SEMANTIC_KINDS
        ):
            continue
        partition, errors = source_definition_partition_record(source_item)
        if partition is None or errors:
            continue
        partition_digest = partition["source_definition_partition_sha256"]
        for component in partition["components"]:
            clause_digest = component["semantic_clause_sha256"]
            anchor_digest = component["source_anchor_sha256"]
            key = source_definition_component_route_key(
                parent_key, clause_digest, anchor_digest
            )
            component_inventory[key] = {
                "statement": component["semantic_clause"],
                "statement_sha256": clause_digest,
                "source_location": component["source_location"],
                "source_kind": str(source_item.get("source_kind") or "")
                .strip()
                .lower(),
                "source_status": str(
                    component.get("source_status")
                    or source_item.get("source_status")
                    or ""
                ).strip(),
                "source_url": str(source_item.get("source_url") or "").strip(),
                "source_component_of": parent_key,
                "source_definition_component": True,
                "source_component_anchor_sha256": anchor_digest,
                "source_definition_partition_sha256": partition_digest,
                "source_definition_component_sha256": component[
                    "source_definition_component_sha256"
                ],
                "source_anchor_evidence": component["source_anchor_evidence"],
            }
            if component.get("model_convention_ids"):
                component_inventory[key]["model_convention_ids"] = list(
                    component["model_convention_ids"]
                )
    return component_inventory


def review_source_component_statement_routes(
    folder: Path,
) -> dict[str, dict[str, Any]]:
    """Return explicit row-to-component display bindings for a review surface.

    The row name merely chooses which dashboard display receives a source
    excerpt.  The selected excerpt itself must resolve through the exact
    parent-item key, quoted-byte digest, and source locator held in the source
    map.  Thus a declaration rename or a misleading function name cannot
    manufacture a source comparison.
    """

    payload = load_review_slice_payload(folder)
    raw_routes = payload.get("source_component_statement_routes")
    if not isinstance(raw_routes, list):
        return {}
    components = paper_source_component_route_inventory(folder)
    definition_components = paper_source_definition_component_route_inventory(folder)
    routes: dict[str, dict[str, Any]] = {}
    for raw_route in raw_routes:
        if not isinstance(raw_route, dict):
            continue
        row = str(raw_route.get("row") or "").strip()
        parent = str(raw_route.get("source_item") or "").strip()
        anchor_sha256 = str(
            raw_route.get("source_component_anchor_sha256") or ""
        ).strip().lower()
        clause_sha256 = str(
            raw_route.get("semantic_clause_sha256") or ""
        ).strip().lower()
        source_location = str(raw_route.get("source_location") or "").strip()
        if (
            not row
            or row in routes
            or not parent
            or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(anchor_sha256)
            or not source_location
        ):
            continue
        if clause_sha256:
            component = definition_components.get(
                source_definition_component_route_key(
                    parent, clause_sha256, anchor_sha256
                )
            )
            if component is not None and any(
                str(raw_route.get(field) or "").strip().lower()
                != str(component.get(field) or "").strip().lower()
                for field in (
                    "source_definition_partition_sha256",
                    "source_definition_component_sha256",
                )
            ):
                component = None
        else:
            component = components.get(
                source_component_route_key(parent, anchor_sha256)
            )
        if component is None or component.get("source_location") != source_location:
            continue
        routes[row] = component
    return routes


def resolved_review_source_component_statement_routes(
    folder: Path,
    parsed_rows: Iterable[
        tuple[str, str, str, str, str | None, int, Path]
    ],
    *,
    component_routes: Mapping[str, dict[str, Any]] | None = None,
) -> dict[str, dict[str, Any]]:
    """Resolve component display navigation to exact full declarations.

    A short row name is accepted only when it identifies one reviewed
    declaration.  Qualified row identities bind directly.  The resulting map
    is keyed solely by full declaration navigation, so namespace collisions
    cannot change which semantic source clause is displayed.
    """

    rows = [row for row in parsed_rows if row[0] in REVIEW_DECL_KINDS]
    raw_routes = (
        review_source_component_statement_routes(folder)
        if component_routes is None
        else component_routes
    )
    resolved: dict[str, dict[str, Any]] = {}
    blocked: set[str] = set()
    for navigation, component in raw_routes.items():
        exact = [row for row in rows if row[2] == navigation]
        candidates = exact if exact else [row for row in rows if row[1] == navigation]
        if len(candidates) != 1:
            continue
        full_name = candidates[0][2]
        if full_name in blocked:
            continue
        previous = resolved.get(full_name)
        if previous is not None and previous != component:
            resolved.pop(full_name, None)
            blocked.add(full_name)
            continue
        resolved[full_name] = component
    return resolved


def resolved_direct_source_statement_routes(
    folder: Path,
    parsed_rows: Iterable[
        tuple[str, str, str, str, str | None, int, Path]
    ],
) -> dict[str, str]:
    """Resolve exact source-map display routes to reviewed declarations.

    This is deliberately separate from the tolerant display-key lookup used
    for legacy navigation.  When a map item explicitly names a direct Lean
    endpoint, its canonical source statement is the semantic-comparison
    target for that exact reviewed declaration.  The resolution starts from
    the map's direct-route field and the parsed declaration's qualified name;
    neither a declaration's spelling nor a map-item key is semantic evidence.

    A legacy unqualified route is accepted only when it resolves to exactly
    one current reviewed declaration.  Conflicting direct map statements for
    one declaration are left unresolved rather than letting map iteration
    order choose a paper statement.
    """

    rows = [row for row in parsed_rows if row[0] in REVIEW_DECL_KINDS]
    direct_routes: dict[str, str] = {}
    conflicts: set[str] = set()
    for source_item in paper_statement_inventory(folder).values():
        if not isinstance(source_item, dict):
            continue
        statement, _statement_sha256 = _source_item_coverage_statement(source_item)
        if not statement:
            continue
        # A source-facing `Spec` is a semantic-review target even though its
        # paired theorem, not the Spec, supplies formal proof credit.  Use the
        # broader statement-routing declaration set here; proof/coverage code
        # deliberately continues to call
        # `source_item_direct_coverage_declarations` and therefore cannot
        # mistake a Spec for a proof endpoint.
        for navigation in source_item_statement_routing_declarations(source_item):
            exact = [row for row in rows if row[2] == navigation]
            candidates = exact if exact else [row for row in rows if row[1] == navigation]
            if len(candidates) != 1:
                continue
            full_name = candidates[0][2]
            if full_name in conflicts:
                continue
            previous = direct_routes.get(full_name)
            if previous is not None and previous != statement:
                direct_routes.pop(full_name, None)
                conflicts.add(full_name)
                continue
            direct_routes[full_name] = statement
    return direct_routes


def resolved_direct_source_item_routes(
    folder: Path,
    parsed_rows: Iterable[
        tuple[str, str, str, str, str | None, int, Path]
    ],
) -> dict[str, tuple[str, dict[str, Any]]]:
    """Resolve one canonical source item for each direct review declaration.

    This is a navigation resolution only.  The returned source item's
    byte-pinned anchor bundle is what later establishes the semantic source
    input; neither this key nor the Lean declaration name is evidence.
    """

    rows = [row for row in parsed_rows if row[0] in REVIEW_DECL_KINDS]
    routes: dict[str, tuple[str, dict[str, Any]]] = {}
    conflicts: set[str] = set()
    for source_key, source_item in paper_statement_inventory(folder).items():
        if not isinstance(source_item, dict):
            continue
        # See the companion display-route resolver above.  This attaches the
        # raw source bundle to both the explicitly configured semantic Spec
        # and any legacy direct endpoint that is actually present in the
        # review surface, while coverage/proof credit remains separately
        # constrained to the theorem endpoint.
        for navigation in source_item_statement_routing_declarations(source_item):
            exact = [row for row in rows if row[2] == navigation]
            candidates = exact if exact else [row for row in rows if row[1] == navigation]
            if len(candidates) != 1:
                continue
            full_name = candidates[0][2]
            if full_name in conflicts:
                continue
            previous = routes.get(full_name)
            if previous is not None and previous[0] != source_key:
                routes.pop(full_name, None)
                conflicts.add(full_name)
                continue
            routes[full_name] = (source_key, source_item)
    return routes


def paper_statement_for_review_row(
    paper_statements: Mapping[str, str],
    component_routes: Mapping[str, Mapping[str, Any]],
    name: str,
    full_name: str,
    *,
    component_navigation_keys: Iterable[str] = (),
    direct_statement_routes: Mapping[str, str] | None = None,
) -> str:
    """Select an explicit direct route before component and legacy lookup."""

    if direct_statement_routes is not None:
        statement = str(direct_statement_routes.get(full_name) or "").strip()
        if statement:
            return statement

    component = component_routes.get(full_name)
    if component is not None:
        statement = str(component.get("statement") or "").strip()
        if statement:
            return statement
    excluded = set(component_navigation_keys)
    for candidate in paper_statement_candidate_keys(name, full_name):
        if candidate in excluded:
            continue
        if candidate and candidate in paper_statements:
            return paper_statements[candidate]
    return ""


def _source_artifact_identity(payload: object) -> tuple[str, str]:
    """Return the canonical source bytes identity declared by a source map."""

    if not isinstance(payload, dict):
        return "", ""
    path = str(payload.get("source_artifact_path") or "").strip()
    digest = str(payload.get("source_artifact_sha256") or "").strip().lower()
    if not path or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(digest):
        return "", ""
    return path, digest


def _source_artifact_identity_is_declared(payload: object) -> bool:
    """Whether a map explicitly attempts to pin a canonical source artifact.

    This is intentionally distinct from :func:`_source_artifact_identity`.
    The latter returns only a complete, valid identity for equality checks;
    this helper preserves the fact that a malformed or partial pin was
    supplied.  A sidecar that also claims artifact-level freshness must fail
    closed in that case rather than treating the malformed map as an older map
    that never opted into artifact pinning.
    """

    return isinstance(payload, dict) and (
        "source_artifact_path" in payload
        or "source_artifact_sha256" in payload
    )


def _coverage_audit_source_artifact_is_current(
    audit: object, statement_map_payload: object
) -> bool:
    """Whether a coverage sidecar was recorded against current source bytes.

    This is intentionally independent of semantic item digests.  Those digests
    omit artifact-wide hashes so unrelated source edits can reuse an unchanged
    item, but such reuse still requires a current byte-verified anchor whenever
    this aggregate source identity differs or is absent.
    """

    current_path, current_digest = _source_artifact_identity(statement_map_payload)
    if not isinstance(audit, dict) or not current_path or not current_digest:
        return False
    recorded_path = str(audit.get("source_artifact_path") or "").strip()
    recorded_digest = str(audit.get("source_artifact_sha256") or "").strip().lower()
    return recorded_path == current_path and recorded_digest == current_digest


def _coverage_audit_records_source_artifact_identity(audit: object) -> bool:
    """Whether a coverage sidecar opted into artifact-level freshness pins.

    Legacy sidecars predate these optional top-level fields.  They remain
    governed by their aggregate inventory digest until migrated to item-level
    source identities.  Once a sidecar supplies either artifact field, a
    partial or stale identity is evidence of a changed source and must fail
    closed rather than silently falling back to the legacy rule.
    """

    if not isinstance(audit, dict):
        return False
    return bool(
        str(audit.get("source_artifact_path") or "").strip()
        or str(audit.get("source_artifact_sha256") or "").strip()
    )


def paper_source_map_structural_errors(folder: Path) -> list[str]:
    """Validate raw inventory shape before any safe prompt projection.

    ``paper_statement_inventory`` necessarily skips unreadable objects while
    constructing text prompts.  Treating that projection as the audit input
    would let a malformed source row vanish from ordinary named-theory scope.
    Keep this raw-map lane independent of selected coverage items.
    """

    payload = paper_statement_map_payload(folder)
    if not payload:
        return []
    if "items" not in payload:
        return ["source map `items` must be an object"]
    errors = source_map_structural_errors(
        payload.get("items"),
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            payload
        ),
    )
    # The raw source-record producer rejects malformed semantic-context
    # requirements before it can issue evidence.  Run that same shared shape
    # validator in the cheap source-map preflight so an old hybrid
    # role/location record cannot consume a full Lean scan merely to discover
    # a deterministic schema error.
    try:
        from scripts.audit_evidence_integrity import (
            semantic_context_requirement_shape_findings,
        )
        status_payload = _dashboard_json_payload(folder / DEFAULT_PAPER_STATUS_FILE) or {}
        status = (
            str(status_payload.get("status") or "paper draft")
            if isinstance(status_payload, Mapping)
            else "paper draft"
        )
        map_path = folder / PAPER_STATEMENT_MAP_FILE
        errors.extend(
            "semantic_context_requirements: " + str(finding.message)
            for finding in semantic_context_requirement_shape_findings(
                folder,
                status,
                map_path,
                payload,
            )
        )
    except Exception as error:  # noqa: BLE001 - preflight must fail closed.
        errors.append(
            "semantic_context_requirements validator failed: " + str(error)
        )
    if typed_route_validation_required(payload):
        try:
            EvidenceRouteSet.from_source_map(payload)
        except CloseoutPipelineError as exc:
            errors.append("typed_evidence_routes: " + str(exc))
    raw_items = payload.get("items")
    source_inventory = paper_statement_inventory(folder)
    if isinstance(raw_items, Mapping):
        for raw_key, raw_item in raw_items.items():
            if (
                not isinstance(raw_item, Mapping)
                or SOURCE_DEFINITION_PARTITION_FIELD not in raw_item
            ):
                continue
            key = str(raw_key or "").strip()
            source_item = source_inventory.get(key)
            if source_item is None:
                errors.append(
                    f"{key or '<unnamed>'}: {SOURCE_DEFINITION_PARTITION_FIELD} "
                    "cannot bind to a canonical source item"
                )
                continue
            if (
                str(source_item.get("source_kind") or "").strip().lower()
                not in SOURCE_DEFINITION_SEMANTIC_KINDS
            ):
                errors.append(
                    f"{key}: {SOURCE_DEFINITION_PARTITION_FIELD} is allowed only "
                    "on a source definition"
                )
                continue
            _partition, partition_errors = source_definition_partition_record(
                source_item
            )
            errors.extend(f"{key}: {error}" for error in partition_errors)
    errors.extend(
        "source_prose_definition_inventory: " + error
        for error in source_prose_definition_inventory_errors(
            folder,
            payload,
            repository_root=ROOT,
            file_bytes_override=_dashboard_file_bytes_override(),
        )
    )
    # The dashboard consumes the transcript only after the optional scanned
    # source companion proves that the top-level canonical text pin and visual
    # PDF provenance agree.  This keeps its inexpensive precheck aligned with
    # the release integrity gate without using map keys or Lean routes.
    errors.extend(
        f"source_text_companion: {issue.message}"
        for issue in source_text_companion_validation_issues(
            folder,
            payload,
            repository_root=ROOT,
            require_source_bytes=True,
            file_bytes_override=_dashboard_file_bytes_override(),
        )
    )
    errors.extend(
        f"source_archive_surface: {issue.message}"
        for issue in source_archive_surface_validation_issues(
            folder,
            payload,
            repository_root=ROOT,
            require_source_bytes=True,
            file_bytes_override=_dashboard_file_bytes_override(),
        )
    )
    return sorted(set(errors))


def paper_coverage_inventory(
    folder: Path,
) -> tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any]], str, str]:
    """Return full and selected inventories for the configured coverage mode.

    Ordinary closeout reviews named source-level theory only.  The full
    inventory is retained for an explicit deep-paper audit, so switching modes
    never loses source material or relies on a declaration/function name.
    """

    full_inventory = paper_statement_inventory(folder)
    statement_map = paper_statement_map_payload(folder)
    mode, mode_error = source_coverage_mode_from_map(statement_map)
    raw_map_items = statement_map.get("items") if isinstance(statement_map, dict) else None
    # A valid presentation alias is independently byte-pinned and reconciled
    # elsewhere, but it deliberately has no direct Lean route.  Keep it out
    # of proof coverage after that reconciliation so a repeated proof
    # presentation cannot double-count a paper-facing result.  Malformed
    # alias metadata is not trusted for this exclusion; structural validation
    # keeps it visible and blocks closeout instead.
    presentation_aliases, _presentation_alias_errors = source_presentation_aliases(
        raw_map_items
    )
    selected_inventory = filter_source_inventory_for_coverage(
        full_inventory,
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            statement_map
        ),
    )
    # Keep the established source-presentation selector for compatible maps,
    # then add the stricter source-index lane.  The latter is deliberately
    # independent of a row's summary text, source_kind, map key, or Lean route:
    # a current byte-pinned anchor to exactly one indexed presentation is enough
    # to include a source item whose prose summary omitted its printed heading.
    for item_id in source_index_byte_pinned_anchor_item_ids(
        folder,
        statement_map,
        mode,
        repository_root=ROOT,
        file_bytes_override=_dashboard_file_bytes_override(),
    ):
        item = full_inventory.get(item_id)
        if item is not None and item_id not in presentation_aliases:
            selected_inventory[item_id] = item
    # Corrections and explicit scope dispositions are source-facing obligations
    # in their own right. Preserve them even when neither ordinary selector
    # applies; their dedicated validators still enforce their anchor/approval
    # contracts.
    for item_id, item in full_inventory.items():
        if (
            item_id not in presentation_aliases
            and source_item_has_explicit_nonordinary_obligation(item)
        ):
            selected_inventory[item_id] = item
    return full_inventory, selected_inventory, mode, mode_error


def llm_statement_source_routes_required(folder: Path) -> bool:
    """Return whether a paper opted into exact source-route pins for v10 rows.

    This remains opt-in so legacy sidecars can be refreshed deliberately.  New
    paper scaffolds enable it, and an enabled paper fails closed when a row
    cannot identify the exact source statement(s) it compares.
    """

    status_path = folder / DEFAULT_PAPER_STATUS_FILE
    payload = _dashboard_json_payload(status_path)
    if not isinstance(payload, dict):
        return False
    review_surface = payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return False
    statement_review = review_surface.get("llm_statement_review")
    if not isinstance(statement_review, dict):
        return False
    return statement_review.get("require_explicit_source_routes") is True


DIRECT_EXPRESSION_SEMANTICS_REVIEW_VERSION = "v1"


def llm_direct_expression_semantics_review_required(folder: Path) -> bool:
    """Return whether a paper opts into the versioned formula-domain review.

    Definition and predicate-vocabulary endpoints have always required the
    source-definition semantic review whenever exact v10 source routes are
    enabled.  Formula-like endpoints are an additional review surface, so
    they require an explicit versioned paper policy instead of silently
    invalidating legacy receipt evidence.  This intentionally accepts only
    the literal current protocol version; truthy values and future versions
    must not opt a paper in by accident.
    """

    status_path = folder / DEFAULT_PAPER_STATUS_FILE
    payload = _dashboard_json_payload(status_path)
    if not isinstance(payload, dict):
        return False
    review_surface = payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return False
    statement_review = review_surface.get("llm_statement_review")
    if not isinstance(statement_review, dict):
        return False
    return (
        statement_review.get("require_direct_expression_semantics_review")
        == DIRECT_EXPRESSION_SEMANTICS_REVIEW_VERSION
    )


def direct_source_definition_route_keys(
    raw: Any,
    *,
    inventory: dict[str, dict[str, Any]],
    include_direct_expressions: bool = False,
) -> set[str]:
    """Return direct source routes needing totalization/domain review.

    Definitions and predicate vocabulary always use the legacy v10 gate.
    When the paper's versioned direct-expression policy is enabled, displayed
    formulas, equations, and algorithmic formulas join that same domain and
    totalization review.  This is a source-map semantic classification plus an
    explicit route kind; it intentionally does not inspect row, declaration,
    or function names.  ``source_route_pin_error`` independently verifies
    that each returned route has the exact source digest and conclusion binding
    before it can receive source credit.
    """

    if not isinstance(raw, dict):
        return set()
    routes = raw.get("source_routes")
    if not isinstance(routes, list):
        return set()
    keys: set[str] = set()
    for route in routes:
        if not isinstance(route, dict):
            continue
        source_item_key = str(route.get("source_item") or "").strip()
        source_item = inventory.get(source_item_key)
        if not isinstance(source_item, dict):
            continue
        source_kind = str(source_item.get("source_kind") or "").strip().lower()
        route_kind = str(route.get("route_kind") or "").strip().lower()
        whole_definition_route = route_kind in {
            "direct",
            CORRECTED_TARGET_ROUTE_KIND,
        }
        partition_component_route = (
            route_kind == "source_component"
            and source_item.get("source_definition_component") is True
        )
        semantic_kinds = (
            SOURCE_DIRECT_EXPRESSION_SEMANTIC_KINDS
            if include_direct_expressions
            else SOURCE_DEFINITION_SEMANTIC_KINDS
        )
        if source_kind in semantic_kinds and (
            whole_definition_route or partition_component_route
        ):
            keys.add(source_item_key)
    return keys


def source_anchor_quote_identity(
    source_item: Mapping[str, Any],
) -> tuple[str, str]:
    """Return the identity of the verbatim source text for one source item.

    A source-map ``statement`` is a navigation aid for a human reader.  It is
    not an admissible semantic-review input: it may summarize a displayed
    theorem and its surrounding context.  The LLM statement/coverage lanes
    instead bind the exact, byte-pinned anchor quotes.  The content-only
    identity deliberately excludes line numbers, since an unchanged passage
    can move after an unrelated source edit; the source-anchor integrity gate
    separately validates the current locations and artifact bytes.
    """

    anchors = source_item.get("source_anchor_evidence")
    if not isinstance(anchors, list) or not anchors:
        return "", "source item has no byte-pinned source_anchor_evidence"
    quote_digests: list[str] = []
    for index, raw_anchor in enumerate(anchors):
        if not isinstance(raw_anchor, Mapping):
            return "", f"source anchor {index} is not an object"
        quote = raw_anchor.get("quoted_text")
        recorded = str(raw_anchor.get("quoted_text_sha256") or "").strip().lower()
        if not isinstance(quote, str) or not quote:
            return "", f"source anchor {index} has no quoted_text"
        normalized = quote.replace("\r\n", "\n").replace("\r", "\n")
        actual = hashlib.sha256(normalized.encode("utf-8")).hexdigest()
        if not re.fullmatch(r"[0-9a-f]{64}", recorded) or recorded != actual:
            return "", f"source anchor {index} quoted_text_sha256 is stale"
        quote_digests.append(actual)
    return (
        hashlib.sha256(
            json.dumps(
                {"schema": 1, "quotes": quote_digests},
                ensure_ascii=True,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        ).hexdigest(),
        "",
    )


def source_anchor_file_error(folder: Path, source_record: Mapping[str, Any]) -> str:
    """Compatibility wrapper for exact transaction-aware source validation."""

    return _shared_source_anchor_file_error(
        folder,
        source_record,
        repository_root=ROOT,
        file_bytes_override=_dashboard_file_bytes_override(),
    )


def source_semantic_input_bundle(
    source_item: Mapping[str, Any],
    *,
    require_context_roles: bool = False,
) -> tuple[str, str, str]:
    """Compatibility wrapper for the shared exact source-review bundle."""

    return _shared_source_semantic_input_bundle(
        source_item,
        require_context_roles=require_context_roles,
    )


def statement_review_requires_verbatim_source_inputs(
    raw: Mapping[str, Any],
    *,
    prompt_version: str = "",
) -> bool:
    """Return whether a statement receipt is governed by the raw-source contract.

    Consumers outside a complete sidecar envelope use the row's explicit
    protocol marker.  A caller that is validating a current sidecar may also
    supply its prompt version, which makes a missing protocol marker fail
    closed.  Historical receipt transport deliberately does not infer a new
    raw-source obligation from a reused prompt label alone.
    """

    return (
        str(prompt_version or "").strip()
        == REQUIRED_LLM_STATEMENT_PROMPT_VERSION
        or str(raw.get("source_input_protocol") or "").strip()
        == "verbatim_source_anchor_bundle_v1"
    )


def source_route_pin_error(
    raw: Any,
    *,
    inventory: dict[str, dict[str, Any]],
    require_statement_target: bool = False,
    require_verbatim_source_inputs: bool = False,
) -> str:
    """Validate source-statement pins recorded by a statement-review row.

    The legacy primary evidence was an exact map-statement digest, exact
    source locator, and a source-conclusion obligation carrying those same
    values.  Current v11 evidence additionally binds every route and endpoint
    obligation to the identity of the *verbatim* byte-pinned source-anchor
    bundle.  A source-map paraphrase may remain useful navigation metadata but
    can never be the source text supplied to an LLM semantic reviewer.
    Curated declaration names may help an auditor find candidates, but they are
    not certification evidence and are deliberately not read here.  Production
    v10 consumers also require ``require_statement_target``: the judgment's
    nonempty paper-statement digest must be one of these exact source targets,
    and a ``matches`` judgment must use an equivalence-bearing route.  The
    optional structural-only mode is retained for low-level route-policy tests
    and support-route construction before a statement receipt exists.
    """

    if not isinstance(raw, dict):
        return "judgment is not an object"
    if require_verbatim_source_inputs and (
        str(raw.get("source_input_protocol") or "").strip()
        != "verbatim_source_anchor_bundle_v1"
    ):
        return (
            "statement review does not declare the required "
            "verbatim_source_anchor_bundle_v1 input protocol"
        )
    if require_verbatim_source_inputs and (
        str(raw.get("lean_target_protocol") or "").strip()
        != "expanded_paperinterface_spec_v1"
    ):
        return (
            "statement review does not declare the required "
            "expanded_paperinterface_spec_v1 Lean target protocol"
        )
    routes = raw.get("source_routes")
    if not isinstance(routes, list) or not routes:
        return "missing nonempty explicit `source_routes` list"
    source_obligations = raw.get("source_obligations")
    if not isinstance(source_obligations, list):
        return "missing source obligations for explicit source-route pins"

    lean_obligations = raw.get("lean_obligations")
    if not isinstance(lean_obligations, list):
        return "missing Lean obligations for explicit source-route pins"
    lean_kinds = {
        str(obligation.get("id") or "").strip(): str(
            obligation.get("kind") or ""
        ).strip().lower()
        for obligation in lean_obligations
        if isinstance(obligation, dict) and str(obligation.get("id") or "").strip()
    }
    conclusion_ids = {
        obligation_id
        for obligation_id, kind in lean_kinds.items()
        if kind == "conclusion"
    }
    if not conclusion_ids:
        return "source-route row has no Lean conclusion obligation"
    alignment = raw.get("obligation_alignment")
    if not isinstance(alignment, list):
        return "missing obligation alignment for explicit source-route pins"

    source_input_bundle_sha256 = str(
        raw.get("source_input_bundle_sha256") or ""
    ).strip().lower()

    def exact_endpoint_binding(
        source_item_key: str,
        expected_digest: str,
        expected_location: str,
        expected_anchor_identity: str,
    ) -> bool:
        matching_ids = {
            str(obligation.get("id") or "").strip()
            for obligation in source_obligations
            if isinstance(obligation, dict)
            and str(obligation.get("kind") or "").strip().lower() == "conclusion"
            and str(obligation.get("source_item") or "").strip() == source_item_key
            and str(obligation.get("source_statement_sha256") or "").strip()
            == expected_digest
            and str(obligation.get("source_location") or "").strip()
            == expected_location
            and (
                (
                    statement_digest(str(obligation.get("statement") or ""))
                    == expected_digest
                )
                if not require_verbatim_source_inputs
                else (
                    str(
                        obligation.get("source_anchor_quote_identity_sha256") or ""
                    ).strip().lower()
                    == expected_anchor_identity
                    and str(
                        obligation.get("source_input_bundle_sha256") or ""
                    ).strip().lower()
                    == source_input_bundle_sha256
                )
            )
        }
        return bool(matching_ids) and any(
            isinstance(entry, dict)
            and str(entry.get("source_id") or "").strip() in matching_ids
            and str(entry.get("lean_id") or "").strip() in conclusion_ids
            and str(entry.get("relation") or "").strip().lower() == "equivalent"
            for entry in alignment
        )

    def scope_evidence_error(
        raw_route: dict[str, Any],
        source_item_key: str,
        *,
        require_conclusion: bool,
    ) -> str:
        scope = str(raw_route.get("source_support_scope") or "").strip()
        if len(scope) < 60 or NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(scope):
            return (
                f"source route `{source_item_key}` has no substantive "
                "source_support_scope"
            )
        evidence_ids = _normalize_string_list(raw_route.get("lean_evidence_ids"))
        if not evidence_ids:
            return f"source route `{source_item_key}` has no lean_evidence_ids"
        if any(evidence_id not in lean_kinds for evidence_id in evidence_ids):
            return f"source route `{source_item_key}` references unknown Lean evidence"
        if require_conclusion and not any(
            evidence_id in conclusion_ids for evidence_id in evidence_ids
        ):
            return (
                f"source route `{source_item_key}` has no Lean conclusion in "
                "lean_evidence_ids"
            )
        return ""

    seen_items: set[str] = set()
    route_kinds: dict[str, str] = {}
    source_target_routes: list[tuple[str, str, str, bool]] = []
    for raw_route in routes:
        if not isinstance(raw_route, dict):
            return "source route is not an object"
        source_item_key = str(raw_route.get("source_item") or "").strip()
        if not source_item_key:
            return "source route has no source_item"
        if source_item_key in seen_items:
            return f"source route duplicates `{source_item_key}`"
        seen_items.add(source_item_key)
        source_item = inventory.get(source_item_key)
        if source_item is None:
            return f"source route names unknown source item `{source_item_key}`"

        route_kind = str(raw_route.get("route_kind") or "").strip().lower()
        if route_kind not in SOURCE_ROUTE_KINDS:
            return f"source route `{source_item_key}` has invalid route_kind"
        is_definition_component = (
            source_item.get("source_definition_component") is True
        )
        if is_definition_component and route_kind != "source_component":
            return (
                f"definition-component route `{source_item_key}` must use "
                "source_component; a clause cannot masquerade as a whole-item route"
            )
        is_corrected_target = _source_item_is_corrected_target(source_item)
        target_error = (
            _source_item_corrected_target_metadata_error(source_item)
            if is_corrected_target
            else ""
        )
        if target_error:
            return f"source route `{source_item_key}` {target_error}"
        expected_statement, expected_digest = _source_item_coverage_statement(source_item)
        expected_location = _source_item_coverage_location(source_item)
        expected_anchor_identity, anchor_identity_error = source_anchor_quote_identity(
            source_item
        )
        expected_semantic_input_text, expected_semantic_input_identity, semantic_input_error = (
            source_semantic_input_bundle(
                source_item,
                require_context_roles=require_verbatim_source_inputs,
            )
        )
        # The paper-statement target is the literal source text supplied to
        # the reviewer.  The bundle identity separately binds that text to its
        # anchors and permitted context; it is not itself a statement digest.
        # Comparing the target to the bundle digest would make a properly
        # pinned verbatim review impossible whenever the bundle carries its
        # structural provenance in addition to the text.
        expected_verbatim_statement_digest = statement_digest(
            expected_semantic_input_text
        )
        recorded_digest = str(raw_route.get("source_statement_sha256") or "").strip()
        recorded_location = str(raw_route.get("source_location") or "").strip()
        if not expected_statement or not expected_digest or not expected_location:
            return f"source route `{source_item_key}` has incomplete canonical source inventory"
        if require_verbatim_source_inputs and anchor_identity_error:
            return f"source route `{source_item_key}` {anchor_identity_error}"
        if require_verbatim_source_inputs and semantic_input_error:
            return f"source route `{source_item_key}` {semantic_input_error}"
        if require_verbatim_source_inputs and str(
            raw_route.get("source_anchor_quote_identity_sha256") or ""
        ).strip().lower() != expected_anchor_identity:
            return (
                f"source route `{source_item_key}` lacks the current exact "
                "verbatim source-anchor identity"
            )
        if (
            require_verbatim_source_inputs
            and route_kind in {"direct", CORRECTED_TARGET_ROUTE_KIND}
            and source_input_bundle_sha256 != expected_semantic_input_identity
        ):
            return (
                f"direct source route `{source_item_key}` lacks the exact "
                "verbatim source-input bundle identity"
            )
        if is_corrected_target and route_kind != CORRECTED_TARGET_ROUTE_KIND:
            return (
                f"corrected-target source route `{source_item_key}` must use "
                "approved_corrected_target; an approved correction cannot be "
                "certified through a component, convention, proof-support, or "
                "archival direct route"
            )
        if recorded_digest != expected_digest:
            return f"source route `{source_item_key}` has a stale source statement digest"
        if recorded_location != expected_location:
            return f"source route `{source_item_key}` has a stale source location"

        route_kinds[source_item_key] = route_kind
        route_policy = source_item_effective_route_policy(source_item)
        relation = str(raw_route.get("semantic_relation") or "").strip().lower()
        endpoint_binding = exact_endpoint_binding(
            source_item_key, expected_digest, expected_location, expected_anchor_identity
        )
        source_target_routes.append(
            (
                expected_verbatim_statement_digest
                if require_verbatim_source_inputs
                else expected_digest,
                route_kind,
                relation,
                endpoint_binding,
            )
        )

        if route_kind == CORRECTED_TARGET_ROUTE_KIND:
            if not is_corrected_target:
                return (
                    f"approved corrected-target route `{source_item_key}` does not name "
                    "a corrected_source_statement inventory item"
                )
            target = _source_item_corrected_target(source_item)
            assert target is not None
            archival_digest = str(source_item.get("statement_sha256") or "").strip()
            archival_location = _source_item_coverage_location(source_item)
            approval = target.get("approval")
            assert isinstance(approval, dict)
            expected_governing = _normalize_string_list(
                target.get("governing_defect_ids")
            )
            if relation != CORRECTED_TARGET_ROUTE_RELATION:
                return (
                    f"approved corrected-target route `{source_item_key}` has invalid "
                    "semantic_relation"
                )
            if str(raw.get("resolution") or "").strip().lower() != CORRECTED_TARGET_MATCH_RESOLUTION:
                return (
                    f"approved corrected-target route `{source_item_key}` requires "
                    "judgment resolution approved_corrected_target"
                )
            if str(raw_route.get("archival_statement_sha256") or "").strip().lower() != archival_digest:
                return (
                    f"approved corrected-target route `{source_item_key}` has a stale "
                    "archival statement digest"
                )
            if str(raw_route.get("archival_source_location") or "").strip() != archival_location:
                return (
                    f"approved corrected-target route `{source_item_key}` has a stale "
                    "archival source location"
                )
            if str(raw_route.get("corrected_target_sha256") or "").strip().lower() != corrected_target_digest(target):
                return (
                    f"approved corrected-target route `{source_item_key}` has a stale "
                    "corrected-target record digest"
                )
            if _normalize_string_list(raw_route.get("governing_defect_ids")) != expected_governing:
                return (
                    f"approved corrected-target route `{source_item_key}` lacks the "
                    "exact governing source-statement defect ids"
                )
            if raw_route.get("archival_equivalence_claimed") is not False:
                return (
                    f"approved corrected-target route `{source_item_key}` must set "
                    "archival_equivalence_claimed to false"
                )
            if str(raw_route.get("approval_artifact_sha256") or "").strip().lower() != str(
                approval.get("artifact_sha256") or ""
            ).strip().lower():
                return (
                    f"approved corrected-target route `{source_item_key}` has a stale "
                    "approval artifact digest"
                )
            if not endpoint_binding:
                return (
                    f"approved corrected-target route `{source_item_key}` has no exact "
                    "equivalent corrected-target conclusion binding"
                )
        elif route_kind == "direct":
            if route_policy["is_model_convention"]:
                return (
                    f"direct source route `{source_item_key}` is a model/assumption "
                    "convention rather than a source result"
                )
            if not route_policy["allows_direct_route"]:
                return (
                    f"direct source route `{source_item_key}` is quarantined or support-only"
                )
            if not endpoint_binding:
                return (
                    f"direct source route `{source_item_key}` has no exact equivalent "
                    "source-conclusion binding"
                )
        elif route_kind == "source_model_convention":
            if not route_policy["allows_source_model_convention_route"]:
                return (
                    f"source-model route `{source_item_key}` does not identify a "
                    "source model convention"
                )
            if relation not in SOURCE_MODEL_ROUTE_RELATIONS:
                return f"source-model route `{source_item_key}` has invalid semantic_relation"
            scope_error = scope_evidence_error(
                raw_route, source_item_key, require_conclusion=False
            )
            if scope_error:
                return scope_error
            if relation == "equivalent_model_convention" and not endpoint_binding:
                return (
                    f"equivalent source-model route `{source_item_key}` has no exact "
                    "equivalent source-conclusion binding"
                )
        elif route_kind == "source_component":
            if not route_policy["allows_source_component_route"]:
                return (
                    f"source-component route `{source_item_key}` is not an ordinary "
                    "source component"
                )
            if relation not in SOURCE_COMPONENT_ROUTE_RELATIONS:
                return f"source-component route `{source_item_key}` has invalid semantic_relation"
            expected_component_anchor = str(
                source_item.get("source_component_anchor_sha256") or ""
            ).strip().lower()
            if expected_component_anchor and str(
                raw_route.get("source_component_anchor_sha256") or ""
            ).strip().lower() != expected_component_anchor:
                return (
                    f"source-component route `{source_item_key}` has a stale "
                    "source_component_anchor_sha256"
                )
            if is_definition_component:
                if relation != SOURCE_DEFINITION_COMPONENT_RELATION:
                    return (
                        f"definition-component route `{source_item_key}` must use "
                        f"{SOURCE_DEFINITION_COMPONENT_RELATION}"
                    )
                for field in (
                    "source_definition_partition_sha256",
                    "source_definition_component_sha256",
                ):
                    if str(raw_route.get(field) or "").strip().lower() != str(
                        source_item.get(field) or ""
                    ).strip().lower():
                        return (
                            f"definition-component route `{source_item_key}` has "
                            f"a stale {field}"
                        )
                if not endpoint_binding:
                    return (
                        f"definition-component route `{source_item_key}` has no "
                        "exact equivalent clause-conclusion binding"
                    )
            elif relation == "equivalent_source_component" and not endpoint_binding:
                return (
                    f"equivalent source-component route `{source_item_key}` has no "
                    "exact equivalent source-conclusion binding"
                )
            scope_error = scope_evidence_error(
                raw_route, source_item_key, require_conclusion=True
            )
            if scope_error:
                return scope_error
        elif route_kind == "defect_or_remark_support":
            if not route_policy["allows_defect_or_remark_support_route"]:
                return (
                    f"defect/remark support route `{source_item_key}` is not a "
                    "quarantined defect or support-only source item"
                )
            if relation not in SOURCE_DEFECT_ROUTE_RELATIONS:
                return f"defect/remark route `{source_item_key}` has invalid semantic_relation"
            scope_error = scope_evidence_error(
                raw_route, source_item_key, require_conclusion=True
            )
            if scope_error:
                return scope_error
            defect_ids = _normalize_string_list(source_item.get("source_defect_ids"))
            defect_id = str(raw_route.get("defect_id") or "").strip()
            if defect_ids and defect_id not in defect_ids:
                return (
                    f"defect/remark route `{source_item_key}` lacks its exact "
                    "source defect id"
                )
        else:  # proof_support
            if relation != "proof_component_support":
                return f"proof-support route `{source_item_key}` has invalid semantic_relation"
            scope_error = scope_evidence_error(
                raw_route, source_item_key, require_conclusion=True
            )
            if scope_error:
                return scope_error

    # A model convention can contextualize a row, but it cannot replace a
    # source result that the row's own semantic obligation ledger identifies
    # as an endpoint.  This deliberately reads source-item pins from the
    # ledger rather than declaration names: renaming Lean code must not change
    # whether a theorem endpoint is required to have a direct source route.
    endpoint_source_items: set[str] = set()
    for obligation in source_obligations:
        if not isinstance(obligation, dict):
            continue
        if str(obligation.get("kind") or "").strip().lower() != "conclusion":
            continue
        source_item_key = str(obligation.get("source_item") or "").strip()
        source_item = inventory.get(source_item_key)
        if source_item is None:
            continue
        if source_item.get("source_definition_component") is True:
            # This obligation is a certified clause in a complete partition,
            # not a claim that the row alone realizes the whole definition.
            continue
        if str(source_item.get("source_kind") or "").strip().lower() not in (
            SOURCE_RESULT_KINDS | SOURCE_DEFINITION_SEMANTIC_KINDS
        ):
            continue
        if not source_item_effective_route_policy(source_item)[
            "direct_source_endpoint_required"
        ]:
            continue
        # A source item can also anchor a smaller proof component.  It is a
        # theorem endpoint only when the ledger says this exact audited target,
        # rather than merely citing the proposition's location.  Corrected
        # rows deliberately compare their approved target, never the archival
        # statement retained in the source inventory.
        _endpoint_statement, endpoint_digest = _source_item_coverage_statement(
            source_item
        )
        endpoint_anchor_identity, endpoint_anchor_error = source_anchor_quote_identity(
            source_item
        )
        if not (
            str(obligation.get("source_statement_sha256") or "").strip()
            == endpoint_digest
            and str(obligation.get("source_location") or "").strip()
            == _source_item_coverage_location(source_item)
            and statement_digest(str(obligation.get("statement") or ""))
            == endpoint_digest
            and (
                not require_verbatim_source_inputs
                or (
                    not endpoint_anchor_error
                    and str(
                        obligation.get("source_anchor_quote_identity_sha256") or ""
                    ).strip().lower()
                    == endpoint_anchor_identity
                )
            )
        ):
            continue
        endpoint_source_items.add(source_item_key)
    missing_direct_endpoints = sorted(
        key
        for key in endpoint_source_items
        if route_kinds.get(key)
        != (
            CORRECTED_TARGET_ROUTE_KIND
            if _source_item_is_corrected_target(inventory[key])
            else "direct"
        )
    )
    if missing_direct_endpoints:
        return (
            "row has source-result/definition endpoint obligations without the required direct or "
            "approved-corrected-target source routes: "
            + ", ".join(missing_direct_endpoints)
        )
    if require_statement_target:
        recorded_target = str(raw.get("paper_statement_sha256") or "").strip().lower()
        empty_target = statement_digest("")
        if not SOURCE_ARTIFACT_SHA256_RE.fullmatch(recorded_target):
            return "statement review has no valid paper_statement_sha256 target receipt"
        if recorded_target == empty_target:
            return "statement review has an empty paper-statement target receipt"
        matching_routes = [
            route
            for route in source_target_routes
            if route[0] == recorded_target
        ]
        if not matching_routes:
            return (
                "statement review paper-statement target is not bound by any "
                "current explicit source route"
            )
        if require_verbatim_source_inputs:
            target_declaration = str(
                raw.get("semantic_target_declaration") or ""
            ).strip()
            if not target_declaration:
                return "statement review has no transparent Spec target declaration"
            direct_source_items = {
                str(route.get("source_item") or "").strip()
                for route in routes
                if isinstance(route, Mapping)
                and str(route.get("route_kind") or "").strip().lower()
                in {"direct", CORRECTED_TARGET_ROUTE_KIND}
            }
            allowed_specs: set[str] = set()
            for source_item_key in direct_source_items:
                source_item = inventory.get(source_item_key)
                if not isinstance(source_item, Mapping):
                    continue
                allowed_specs.update(
                    _normalize_string_list(source_item.get("spec_lean_declarations"))
                )
                contract = source_item.get("semantic_contract")
                if isinstance(contract, Mapping):
                    declaration = str(contract.get("spec_declaration") or "").strip()
                    if declaration:
                        allowed_specs.add(declaration)
            if target_declaration not in allowed_specs:
                return (
                    "statement review semantic target is not the direct source "
                    "item's transparent Spec declaration"
                )
        judgment = _normalize_llm_match_judgment(
            raw.get("judgment")
            or raw.get("verdict")
            or raw.get("status")
            or raw.get("matches")
        )
        if judgment == "matches":
            equivalence_bearing = any(
                route_kind in {"direct", CORRECTED_TARGET_ROUTE_KIND}
                or (
                    route_kind == "source_component"
                    and relation == "equivalent_source_component"
                    and endpoint_binding
                )
                or (
                    route_kind == "source_model_convention"
                    and relation == "equivalent_model_convention"
                    and endpoint_binding
                )
                for _digest, route_kind, relation, endpoint_binding in matching_routes
            )
            if not equivalence_bearing:
                return (
                    "matches judgment paper-statement target has no exact "
                    "equivalence-bearing source route"
                )
    return ""


def paper_statement_inventory_digest(inventory: dict[str, dict[str, Any]]) -> str:
    """Return a stable digest of canonical source-paper statement inventory."""

    payload = [
        {
            "key": key,
            "statement": normalize_statement(str(item.get("statement") or "")),
            "aliases": sorted(str(alias) for alias in item.get("aliases", []) or []),
            "source_presentation_alias": item.get("source_presentation_alias"),
            "source": str(item.get("source") or ""),
            "coverage_status": str(item.get("coverage_status") or "").strip().lower(),
            "protocol_role": str(item.get("protocol_role") or "").strip().lower(),
            **(
                {
                    "inventory_role": str(
                        item.get("inventory_role") or ""
                    ).strip().lower()
                }
                if "inventory_role" in item
                else {}
            ),
            "corrected_target": item.get("corrected_target"),
            "source_kind": str(item.get("source_kind") or "").strip().lower(),
            "claim_bearing": item.get("claim_bearing"),
            "source_scope_classification": str(
                item.get("source_scope_classification") or ""
            ).strip().lower(),
            "user_approved_scope_exclusion": item.get(
                "user_approved_scope_exclusion"
            ),
            "scope_reason": normalize_statement(str(item.get("scope_reason") or "")),
            "source_evidence": normalize_statement(
                str(item.get("source_evidence") or "")
            ),
            "source_artifact_path": str(item.get("source_artifact_path") or "").strip(),
            "source_artifact_sha256": str(
                item.get("source_artifact_sha256") or ""
            ).strip().lower(),
            "source_anchor_evidence_required": item.get(
                "source_anchor_evidence_required"
            )
            is True,
            "source_anchor_evidence": item.get("source_anchor_evidence"),
            "source_status": str(item.get("source_status") or "").strip(),
            "source_note": normalize_statement(str(item.get("source_note") or "")),
            "source_defect_ids": sorted(
                str(defect_id)
                for defect_id in item.get("source_defect_ids", []) or []
            ),
            "lean_declarations": sorted(
                str(name) for name in item.get("lean_declarations", []) or []
            ),
            "proof_lean_declarations": sorted(
                str(name)
                for name in item.get("proof_lean_declarations", []) or []
            ),
            "support_lean_declarations": sorted(
                str(name)
                for name in item.get("support_lean_declarations", []) or []
            ),
            "spec_lean_declarations": sorted(
                str(name)
                for name in item.get("spec_lean_declarations", []) or []
            ),
            "semantic_contract": item.get("semantic_contract"),
            **(
                {
                    SOURCE_DEFINITION_PARTITION_FIELD: item[
                        SOURCE_DEFINITION_PARTITION_FIELD
                    ]
                }
                if SOURCE_DEFINITION_PARTITION_FIELD in item
                else {}
            ),
            "source_location": str(item.get("source_location") or ""),
            "source_url": str(item.get("source_url") or ""),
        }
        for key, item in sorted(inventory.items())
    ]
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def paper_coverage_inventory_digest(
    inventory: dict[str, dict[str, Any]],
    *,
    mode: str,
    statement_map_payload: dict[str, Any] | None = None,
) -> str:
    """Return the mode-aware aggregate digest for coverage-sidecar discovery.

    This aggregate is useful to find additions/removals.  It is deliberately
    not the sole freshness gate: a current per-item source digest plus a
    current elaborated Lean signature lets an unchanged obligation retain its
    completed judgment when another source item changes.
    """

    payload: dict[str, Any] = {
        "mode": mode,
        "items": [
            {
                "key": key,
                "source_item_coverage_sha256": source_item_coverage_sha256(
                    item, mode
                ),
            }
            for key, item in sorted(inventory.items())
        ],
    }
    if mode == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS and isinstance(
        statement_map_payload, dict
    ):
        payload["source_prose_inventory_review"] = statement_map_payload.get(
            "source_prose_inventory_review"
        )
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def _coverage_item_source_digest_is_current(
    coverage_item: dict[str, Any],
    source_item: dict[str, Any],
    mode: str,
    *,
    legacy_navigation_key: str | None = None,
) -> bool:
    """Return per-item freshness without treating aggregate-map drift as stale.

    Legacy sidecars did not record a source-item semantic digest.  They remain
    usable only while their aggregate inventory digest is current; new
    sidecars record this field and can safely reuse unchanged item judgments.
    """

    return source_item_coverage_receipt_matches(
        source_item,
        mode,
        digest_schema=coverage_item.get("source_item_coverage_digest_schema"),
        digest=coverage_item.get("source_item_coverage_sha256"),
        legacy_navigation_key=legacy_navigation_key,
    )


def _coverage_item_has_current_source_digest_schema(item: dict[str, Any]) -> bool:
    """Return whether a sidecar item can use semantic item-level freshness."""

    return source_item_coverage_receipt_shape_is_reusable(
        digest_schema=item.get("source_item_coverage_digest_schema"),
        digest=item.get("source_item_coverage_sha256"),
    )


def _semantic_coverage_item_bindings(
    inventory: dict[str, dict[str, Any]],
    audit_items: dict[str, Any],
    mode: str,
) -> tuple[dict[str, str], list[str]]:
    """Bind current source items to uniquely identical saved judgments.

    Coverage-sidecar object keys are navigation handles, not mathematical
    identity.  Preserve an exact key match (so a changed item reports stale),
    then bind an otherwise renamed current item only when its versioned source
    semantic digest identifies exactly one unused sidecar item.  Ambiguous
    duplicates fail closed rather than guessing which human judgment applies.
    """

    bindings: dict[str, str] = {
        key: key for key in inventory if isinstance(audit_items.get(key), dict)
    }
    used = set(bindings.values())
    ambiguous: list[str] = []
    for source_key, source_item in inventory.items():
        if source_key in bindings:
            continue
        candidates = sorted(
            str(audit_key)
            for audit_key, raw_item in audit_items.items()
            if audit_key not in used
            and isinstance(raw_item, dict)
            and _coverage_item_has_current_source_digest_schema(raw_item)
            and source_item_coverage_receipt_matches(
                source_item,
                mode,
                digest_schema=raw_item.get("source_item_coverage_digest_schema"),
                digest=raw_item.get("source_item_coverage_sha256"),
                legacy_navigation_key=str(audit_key),
            )
        )
        if len(candidates) == 1:
            bindings[source_key] = candidates[0]
            used.add(candidates[0])
        elif len(candidates) > 1:
            ambiguous.append(
                f"{source_key}: multiple sidecar items share its source semantic digest"
            )
    return bindings, ambiguous


@dataclass(frozen=True)
class _CoverageBindingFreshness:
    """One authoritative source-item/coverage-sidecar freshness projection.

    The fast inventory precheck and the full dashboard need different
    presentation detail, but they must not independently decide which saved
    judgment belongs to a source item or whether that judgment is current.
    Keeping this state typed and row-local prevents aggregate/navigation drift
    from acquiring a second acceptance meaning in either consumer.
    """

    audit: dict[str, Any]
    audit_items: dict[str, Any]
    coverage_item_bindings: dict[str, str]
    ambiguous_semantic_item_bindings: tuple[str, ...]
    bound_audit_items: dict[str, dict[str, Any]]
    inventory_hash: str
    recorded_inventory_hash: str
    recorded_mode: str
    mode_mismatch: bool
    aggregate_current: bool
    source_artifact_current: bool
    missing_coverage: tuple[str, ...]
    extra_coverage: tuple[str, ...]
    out_of_mode_coverage: tuple[str, ...]
    missing_statement_digest: tuple[str, ...]
    stale_statement: tuple[str, ...]
    stale_source_items: tuple[str, ...]
    semantic_reuse_anchor_errors: dict[str, list[str]]
    unverified_reused_source_items: tuple[str, ...]
    legacy_unpinned_items: tuple[str, ...]


def _coverage_binding_freshness(
    folder: Path,
    full_inventory: dict[str, dict[str, Any]],
    inventory: dict[str, dict[str, Any]],
    mode: str,
    statement_map_payload: dict[str, Any],
    *,
    presentation_aliases: Iterable[str] = (),
) -> _CoverageBindingFreshness:
    """Bind and validate saved coverage rows exactly once for both consumers."""

    audit = load_llm_paper_coverage_audit(folder)
    audit_items = audit.get("items") if isinstance(audit.get("items"), dict) else {}
    coverage_item_bindings, ambiguous_semantic_item_bindings = (
        _semantic_coverage_item_bindings(inventory, audit_items, mode)
    )
    bound_audit_items = {
        source_key: audit_items[audit_key]
        for source_key, audit_key in coverage_item_bindings.items()
        if isinstance(audit_items.get(audit_key), dict)
    }
    inventory_hash = paper_coverage_inventory_digest(
        inventory,
        mode=mode,
        statement_map_payload=statement_map_payload,
    )
    full_inventory_hash = paper_statement_inventory_digest(full_inventory)
    recorded_inventory_hash = str(
        audit.get("paper_statement_inventory_sha256") or ""
    ).strip()
    recorded_mode = str(audit.get("source_coverage_mode") or "").strip()
    mode_mismatch = bool(
        recorded_mode and not source_coverage_modes_compatible(recorded_mode, mode)
    )
    missing_coverage = tuple(
        sorted(key for key in inventory if key not in bound_audit_items)
    )
    used_audit_keys = set(coverage_item_bindings.values())
    extra_coverage = tuple(
        sorted(
            key
            for key in audit_items
            if key not in full_inventory and key not in used_audit_keys
        )
    )
    alias_keys = set(presentation_aliases)
    out_of_mode_coverage = tuple(
        sorted(
            key
            for key in audit_items
            if key in full_inventory
            and key not in inventory
            and key not in alias_keys
        )
    )
    missing_statement_digest = tuple(
        sorted(
            key
            for key, item in bound_audit_items.items()
            if not str(item.get("statement_sha256") or "").strip()
        )
    )
    stale_statement = tuple(
        sorted(
            key
            for key, item in bound_audit_items.items()
            if str(item.get("statement_sha256") or "").strip()
            and str(item.get("statement_sha256") or "").strip()
            != _source_item_coverage_statement(inventory[key])[1]
        )
    )
    aggregate_current = recorded_inventory_hash in {
        inventory_hash,
        # Pre-mode sidecars used the full inventory hash. They remain valid
        # when the full inventory itself is unchanged.
        full_inventory_hash,
    }
    source_artifact_current = _coverage_audit_source_artifact_is_current(
        audit, statement_map_payload
    )
    source_artifact_identity_declared = _source_artifact_identity_is_declared(
        statement_map_payload
    )
    source_artifact_identity_recorded = _coverage_audit_records_source_artifact_identity(
        audit
    )
    current_item_keys: list[str] = []
    stale_source_items: list[str] = []
    for key, item in bound_audit_items.items():
        if not _coverage_item_has_current_source_digest_schema(item):
            continue
        if _coverage_item_source_digest_is_current(
            item,
            inventory[key],
            mode,
            legacy_navigation_key=coverage_item_bindings.get(key),
        ):
            current_item_keys.append(key)
        else:
            stale_source_items.append(key)
    # Per-item semantic identity deliberately excludes navigation locators.
    # Exact quote validation remains mandatory on every proposed reuse.
    semantic_reuse_anchor_errors = _semantic_reuse_source_anchor_errors(
        folder, current_item_keys
    )
    legacy_unpinned_items = tuple(
        sorted(
            key
            for key, item in bound_audit_items.items()
            if not _coverage_item_has_current_source_digest_schema(item)
            and (
                not aggregate_current
                or (
                    source_artifact_identity_declared
                    and source_artifact_identity_recorded
                    and not source_artifact_current
                )
            )
        )
    )
    return _CoverageBindingFreshness(
        audit=audit,
        audit_items=audit_items,
        coverage_item_bindings=coverage_item_bindings,
        ambiguous_semantic_item_bindings=tuple(ambiguous_semantic_item_bindings),
        bound_audit_items=bound_audit_items,
        inventory_hash=inventory_hash,
        recorded_inventory_hash=recorded_inventory_hash,
        recorded_mode=recorded_mode,
        mode_mismatch=mode_mismatch,
        aggregate_current=aggregate_current,
        source_artifact_current=source_artifact_current,
        missing_coverage=missing_coverage,
        extra_coverage=extra_coverage,
        out_of_mode_coverage=out_of_mode_coverage,
        missing_statement_digest=missing_statement_digest,
        stale_statement=stale_statement,
        stale_source_items=tuple(sorted(stale_source_items)),
        semantic_reuse_anchor_errors=semantic_reuse_anchor_errors,
        unverified_reused_source_items=tuple(sorted(semantic_reuse_anchor_errors)),
        legacy_unpinned_items=legacy_unpinned_items,
    )


def _current_row_signature_digest(row_item: ReviewItem) -> str:
    """Return one row's verified coverage-target identity, if available."""

    if row_item.coverage_target_kind == PAPER_PREREQUISITE_COVERAGE_TARGET_KIND:
        digest = str(row_item.coverage_target_identity_sha256 or "").strip().lower()
        if (
            not row_item.llm_match_stale
            and SOURCE_ARTIFACT_SHA256_RE.fullmatch(digest)
        ):
            return digest
        return ""

    manifest = row_item.lean_signature_manifest
    if not isinstance(manifest, dict):
        return ""
    digest = signature_manifest_digest(manifest)
    if not digest:
        return ""
    if str(manifest.get("sha256") or "").strip().lower() != digest:
        return ""
    if str(row_item.lean_signature_sha256 or "").strip().lower() != digest:
        return ""
    return digest


def paper_prerequisite_coverage_identity_sha256(
    *,
    paper_declaration: str,
    source_item: str,
    source_input_bundle_sha256: str,
    paper_semantic_target_sha256: str,
    judgment: str,
    prompt_version: str,
    target_protocol: str,
) -> str:
    """Bind one direct source-definition coverage target to reviewed semantics."""

    values = {
        "paper_declaration": paper_declaration.strip(),
        "source_item": source_item.strip(),
        "source_input_bundle_sha256": source_input_bundle_sha256.strip().lower(),
        "paper_semantic_target_sha256": paper_semantic_target_sha256.strip().lower(),
        "judgment": judgment.strip().lower(),
        "prompt_version": prompt_version.strip(),
        "target_protocol": target_protocol.strip(),
    }
    if (
        not values["paper_declaration"]
        or not values["source_item"]
        or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(
            values["source_input_bundle_sha256"]
        )
        or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(
            values["paper_semantic_target_sha256"]
        )
        or values["judgment"] != "matches"
        or values["prompt_version"] != PAPER_PREREQUISITE_LEDGER_PROMPT_VERSION
        or values["target_protocol"]
        != PAPER_PREREQUISITE_LEDGER_TARGET_PROTOCOL
    ):
        return ""
    return statement_digest(
        json.dumps(
            {
                "schema": PAPER_PREREQUISITE_COVERAGE_IDENTITY_SCHEMA,
                **values,
            },
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        )
    )


def paper_semantic_prerequisite_coverage_review_items(
    folder: Path,
    inventory: Mapping[str, dict[str, Any]],
    claim_items: Iterable[ReviewItem],
    *,
    semantic_targets_by_name_override: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, ReviewItem]:
    """Project current paper-prerequisite judgments into typed coverage targets.

    This is a reference projection, not another semantic review.  The
    prerequisite lane remains responsible for proving the Lean target current;
    coverage proves only that every source presentation is routed to the exact
    already-reviewed target.  The projection independently requires that target
    in the authenticated current packet graph.  A stale source bundle or Lean
    target, wrong source item, non-direct declaration, malformed protocol, or
    non-match yields no current target identity and therefore fails closed in
    the ordinary coverage pin checks.
    """

    if semantic_targets_by_name_override is None:
        specification_names = sorted(
            {
                str(item.full_name or "").strip()
                for item in claim_items
                if str(item.full_name or "").strip().endswith("Spec")
            }
        )
        try:
            from scripts.current_closeout import review_surface as packet

            packet_cache = packet._current_packet_lean_cache(  # type: ignore[attr-defined]
                folder,
                specification_names,
            )
        except Exception:  # noqa: BLE001 - missing authority fails closed below.
            packet_cache = None
        raw_targets = (
            packet.paper_semantic_review_targets_from_cache(packet_cache)
            if isinstance(packet_cache, Mapping)
            else None
        )
        semantic_targets_by_name = (
            raw_targets if isinstance(raw_targets, Mapping) else {}
        )
    else:
        semantic_targets_by_name = semantic_targets_by_name_override

    ledger = _dashboard_json_payload(
        folder / PAPER_AUDIT_DIR / "paper_semantic_prerequisites.json"
    )
    if not isinstance(ledger, Mapping):
        return {}
    prompt_version = str(ledger.get("prompt_version") or "").strip()
    target_protocol = str(ledger.get("target_protocol") or "").strip()
    ledger_current = bool(
        ledger.get("schema") == PAPER_PREREQUISITE_LEDGER_SCHEMA
        and ledger.get("paper") == folder.name
        and prompt_version == PAPER_PREREQUISITE_LEDGER_PROMPT_VERSION
        and target_protocol == PAPER_PREREQUISITE_LEDGER_TARGET_PROTOCOL
    )
    raw_items = ledger.get("items")
    if not isinstance(raw_items, Mapping):
        return {}

    projected: dict[str, ReviewItem] = {}
    for raw_name, raw_entry in raw_items.items():
        name = str(raw_name or "").strip()
        if not name or not isinstance(raw_entry, Mapping):
            continue
        source_key = str(raw_entry.get("source_item") or "").strip()
        source_item = inventory.get(source_key)
        if not isinstance(source_item, dict):
            continue
        direct_declarations = source_item_direct_coverage_declarations(source_item)
        if name not in direct_declarations:
            continue
        source_input, source_digest, source_error = source_semantic_input_bundle(
            source_item,
            require_context_roles=True,
        )
        target_digest = str(
            raw_entry.get("paper_semantic_target_sha256") or ""
        ).strip().lower()
        current_target = semantic_targets_by_name.get(name)
        current_target_digest = (
            str(current_target.get("display_sha256") or "").strip().lower()
            if isinstance(current_target, Mapping)
            else ""
        )
        judgment = str(raw_entry.get("judgment") or "").strip().lower()
        identity = paper_prerequisite_coverage_identity_sha256(
            paper_declaration=name,
            source_item=source_key,
            source_input_bundle_sha256=source_digest,
            paper_semantic_target_sha256=target_digest,
            judgment=judgment,
            prompt_version=prompt_version,
            target_protocol=target_protocol,
        )
        current = bool(
            ledger_current
            and not source_error
            and str(raw_entry.get("paper_declaration") or "").strip() == name
            and str(
                raw_entry.get("source_input_bundle_sha256") or ""
            ).strip().lower()
            == source_digest
            and str(
                raw_entry.get("paper_semantic_target_protocol") or ""
            ).strip()
            == target_protocol
            and current_target_digest == target_digest
            and identity
            and str(raw_entry.get("validator") or "").strip()
            and str(raw_entry.get("validator_type") or "").strip()
            and str(raw_entry.get("validated_at") or "").strip()
        )
        _coverage_statement, coverage_statement_digest = (
            _source_item_coverage_statement(source_item)
        )
        coverage_location = _source_item_coverage_location(source_item)
        projected[name] = ReviewItem(
            name=name,
            full_name=name,
            kind="def",
            lean_statement=name,
            paper_statement=source_input,
            agent_statement=str(raw_entry.get("reason") or "").strip(),
            lean_signature_sha256=identity,
            coverage_target_kind=PAPER_PREREQUISITE_COVERAGE_TARGET_KIND,
            coverage_target_identity_sha256=identity,
            source_item_key=source_key,
            source_input_bundle_sha256=source_digest,
            verbatim_source_input=source_input,
            llm_match_judgment=judgment,
            llm_match_reason=str(raw_entry.get("reason") or "").strip(),
            llm_match_stale=not current,
            llm_match_source="paper_semantic_prerequisites.json",
            llm_match_validator=str(raw_entry.get("validator") or "").strip(),
            llm_match_validator_type=str(
                raw_entry.get("validator_type") or ""
            ).strip(),
            llm_match_validated_at=str(
                raw_entry.get("validated_at") or ""
            ).strip(),
            llm_match_lean_statement_sha256=target_digest,
            llm_match_lean_signature_sha256=identity,
            llm_match_paper_statement_sha256=(
                statement_digest(source_input) if source_input else ""
            ),
            llm_match_source_routes=[
                {
                    "source_item": source_key,
                    "source_statement_sha256": coverage_statement_digest,
                    "source_location": coverage_location,
                    "route_kind": "direct",
                }
            ],
        )
    return projected


def _current_row_signature_index(
    row_items: dict[str, ReviewItem],
) -> dict[str, list[str]]:
    """Index current row navigation by verified elaborated signature once."""

    current_by_signature: dict[str, list[str]] = {}
    for row_name, row_item in row_items.items():
        digest = _current_row_signature_digest(row_item)
        if digest:
            current_by_signature.setdefault(digest, []).append(row_name)
    return current_by_signature


def _semantic_rebound_coverage_item(
    raw_item: dict[str, Any], current_by_signature: dict[str, list[str]]
) -> tuple[dict[str, Any], list[str], bool]:
    """Rebind saved row navigation only through unique current signatures.

    The sidecar retains the original names for traceability, but all later
    coverage checks see current row names.  A missing, malformed, stale, or
    non-unique signature pin is left untouched so the existing fail-closed row
    link diagnostics remain authoritative.
    """

    copied = dict(raw_item)
    rows = _normalize_string_list(raw_item.get("review_rows"))
    if not rows:
        return copied, [], False
    pins = _normalize_review_row_signature_pins(
        raw_item.get("review_row_signature_sha256")
    )
    if pins is None or set(pins) != set(rows) or len(set(rows)) != len(rows):
        return copied, [], False

    rebound_rows: list[str] = []
    changes: list[str] = []
    for old_name in rows:
        digest = str(pins.get(old_name) or "").strip().lower()
        candidates = sorted(current_by_signature.get(digest, []))
        if old_name in candidates:
            rebound_rows.append(old_name)
            continue
        if len(candidates) != 1:
            return copied, [], False
        new_name = candidates[0]
        rebound_rows.append(new_name)
        changes.append(f"{old_name} -> {new_name}")
    if not changes:
        return copied, [], False
    copied["review_rows"] = rebound_rows
    copied["review_row_signature_sha256"] = {
        row_name: pins[old_name]
        for old_name, row_name in zip(rows, rebound_rows)
    }
    return copied, changes, True


def parse_paper_text_statement_locations(folder: Path) -> list[dict[str, Any]]:
    """Extract first source-text locations for numbered paper statements."""

    source = find_paper_text(folder)
    if source is None:
        return []
    try:
        lines = _dashboard_read_text(source).split("\n")
    except OSError:
        return []

    page = 1
    out: list[dict[str, Any]] = []
    seen: set[str] = set()
    for line_number, raw_line in enumerate(lines, start=1):
        line = raw_line
        if "\f" in line:
            page += line.count("\f")
            line = line.rsplit("\f", 1)[-1]
        stripped = line.strip()
        label_match = PAPER_TEXT_STATEMENT_LABEL_RE.match(stripped)
        if not label_match:
            continue
        kind = label_match.group("kind")
        number = label_match.group("number")
        key = _paper_statement_key(kind, number)
        if key in seen:
            continue
        seen.add(key)
        out.append(
            {
                "key": key,
                "kind": kind,
                "number": number,
                "page": page,
                "line_number": line_number,
            }
        )
    return out


def load_llm_lean_to_tex_draft_entries(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, dict[str, str]]:
    """Load optional context-free LLM TeX draft entries with metadata."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_llm_lean_to_tex_draft_entries(folder)
    path = llm_lean_to_tex_drafts_file(folder)
    if not _dashboard_is_file(path):
        return {}
    payload = _dashboard_json_payload(path)
    if payload is None:
        return {}
    if is_non_evidence_scaffold_payload(payload):
        # Frozen-input scaffolds deliberately contain no context-free
        # translation.  Ignore any later fields until the marker is removed.
        return {}
    if payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, folder.name}:
        return {}
    items = payload.get("items")
    if not isinstance(items, dict):
        return {}
    out: dict[str, dict[str, Any]] = {}
    source = path.name
    payload_translator = str(
        payload.get("translator")
        or payload.get("validator")
        or payload.get("model")
        or payload.get("agent")
        or payload.get("generator")
        or ""
    ).strip()
    payload_translated_at = str(
        payload.get("translated_at")
        or payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
        or ""
    ).strip()
    payload_prompt_version = str(payload.get("prompt_version") or "").strip()
    for raw_name, raw_value in items.items():
        name = str(raw_name).strip()
        if isinstance(raw_value, dict):
            value = str(
                raw_value.get("tex_statement")
                or raw_value.get("statement")
                or raw_value.get("latex")
                or raw_value.get("translation")
                or raw_value.get("draft")
                or ""
            ).strip()
            lean_digest = str(raw_value.get("lean_statement_sha256") or "").strip()
            item_prompt_version = str(
                raw_value.get("prompt_version") or payload_prompt_version
            ).strip()
            translator = str(
                raw_value.get("translator")
                or raw_value.get("validator")
                or raw_value.get("model")
                or raw_value.get("agent")
                or raw_value.get("generator")
                or payload_translator
            ).strip()
            translated_at = str(
                raw_value.get("translated_at")
                or raw_value.get("validated_at")
                or raw_value.get("timestamp")
                or raw_value.get("generated_at")
                or payload_translated_at
            ).strip()
        else:
            value = str(raw_value).strip()
            lean_digest = ""
            item_prompt_version = payload_prompt_version
            translator = payload_translator
            translated_at = payload_translated_at
        if name and value:
            out[name] = {
                "statement": value,
                "lean_statement_sha256": lean_digest,
                "source": source,
                "translator": translator,
                "translated_at": translated_at,
                "metadata_missing": not bool(translator and translated_at),
                "prompt_version": item_prompt_version,
                "prompt_version_stale": not llm_prompt_version_is_semantically_current(
                    item_prompt_version,
                    prompt_contracts=LLM_LEAN_TO_TEX_PROMPT_SEMANTIC_CONTRACTS,
                    required_contract=REQUIRED_LLM_LEAN_TO_TEX_SEMANTIC_CONTRACT_VERSION,
                ),
            }
    return out


def load_llm_lean_to_tex_drafts(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, str]:
    """Load optional context-free LLM TeX drafts for expanded Lean statements."""

    return {
        name: entry["statement"]
        for name, entry in load_llm_lean_to_tex_draft_entries(
            folder, audit_inputs=audit_inputs
        ).items()
        if entry.get("statement")
    }


def llm_statement_judgments_file(folder: Path) -> Path:
    """Return the preferred LLM statement-match judgment sidecar for a paper."""

    tracked_path = paper_relative_file(folder, DEFAULT_LLM_STATEMENT_JUDGE_FILE, "statement_match_llm.json")
    if _dashboard_audit_inputs() is not None or _dashboard_is_file(tracked_path):
        return tracked_path
    return folder / ".review_traces" / "statement_match_llm.json"


def llm_paper_coverage_file(folder: Path) -> Path:
    """Return the preferred LLM source-paper coverage sidecar for a paper."""

    tracked_path = paper_relative_file(folder, DEFAULT_LLM_PAPER_COVERAGE_FILE, "paper_coverage_llm.json")
    if _dashboard_audit_inputs() is not None or _dashboard_is_file(tracked_path):
        return tracked_path
    return folder / ".review_traces" / "paper_coverage_llm.json"


def llm_defect_support_file(folder: Path) -> Path:
    """Return the independent source-defect-to-Lean semantic audit sidecar."""

    tracked_path = paper_relative_file(
        folder,
        DEFAULT_LLM_DEFECT_SUPPORT_FILE,
        "defect_support_match_llm.json",
    )
    if _dashboard_audit_inputs() is not None or _dashboard_is_file(tracked_path):
        return tracked_path
    return folder / ".review_traces" / "defect_support_match_llm.json"


def load_llm_defect_support_audit(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, Any]:
    """Load exact-hash semantic judgments for quarantined defect support.

    This audit is deliberately separate from paper-coverage classification.  A
    coverage reviewer may select a candidate counterexample route, but that
    route receives defect-support credit only after this sidecar binds the exact
    defect record to the exact elaborated Lean statement and explains the
    mathematical counterexample/refutation relation atom by atom.
    """

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_llm_defect_support_audit(folder)
    path = llm_defect_support_file(folder)
    if not _dashboard_is_file(path):
        return {}
    payload = _dashboard_json_payload(path)
    if payload is None:
        return {"source": path.name, "load_error": "invalid JSON", "items": {}}
    if not isinstance(payload, dict):
        return {"source": path.name, "load_error": "top level is not an object", "items": {}}
    if payload.get("schema") != 1:
        return {"source": path.name, "load_error": "schema must be 1", "items": {}}
    if payload.get("paper") != folder.name:
        return {
            "source": path.name,
            "load_error": "paper does not match the paper folder",
            "items": {},
        }
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return {"source": path.name, "load_error": "items is not an object", "items": {}}
    items = raw_items
    validator = str(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or ""
    ).strip()
    validated_at = str(
        payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
        or ""
    ).strip()
    audit_kind = str(payload.get("audit_kind") or "").strip()
    prompt_version = str(payload.get("prompt_version") or "").strip()
    return {
        "source": path.name,
        "load_error": "",
        "validator": validator,
        "validator_type": str(payload.get("validator_type") or "").strip(),
        "validated_at": validated_at,
        "audit_kind": audit_kind,
        "source_grounded": payload.get("source_grounded") is True,
        "prompt_version": prompt_version,
        "prompt_version_stale": (
            prompt_version != REQUIRED_LLM_DEFECT_SUPPORT_PROMPT_VERSION
        ),
        "metadata_missing": not bool(validator and validated_at),
        "items": items,
    }


def _normalize_paper_coverage_judgment(raw: Any) -> str:
    """Normalize paper-level source-coverage verdicts."""

    if isinstance(raw, bool):
        return "covered" if raw else "missing"
    value = str(raw or "").strip().lower().replace("-", "_")
    value = re.sub(r"\s+", "_", value)
    if value in {"match", "matches", "yes", "true", "represented", "present"}:
        return "covered"
    if value in {
        "conditional",
        "conditional_boundary",
        "visible_premise_boundary",
        "covered_with_boundary",
        "covered_conditionally",
        "additional_assumption",
        "covered_with_additional_assumption",
    }:
        return "conditional_boundary"
    if value in {
        "support",
        "support_only",
        "covered_by_support",
        "covered_in_support",
        "covered_by_support_declarations",
    }:
        return "covered_by_support"
    if value in {"partial", "partially_represented", "partial_coverage"}:
        return "partially_covered"
    if value in {"not_covered", "absent", "no", "false"}:
        return "missing"
    if value in {"irrelevant", "background", "not_target", "not_review_target"}:
        return "not_a_paper_target"
    return value


def _normalize_string_list(raw: Any) -> list[str]:
    """Normalize scalar/list sidecar fields into a stable string list."""

    if raw is None:
        return []
    if isinstance(raw, (list, tuple, set)):
        values = raw
    else:
        values = str(raw).split(",")
    out: list[str] = []
    for value in values:
        text = str(value or "").strip()
        if text:
            out.append(text)
    return out


def _normalize_review_row_signature_pins(raw: Any) -> dict[str, str] | None:
    """Normalize one coverage item's exact current-row signature pin map.

    Coverage-sidecar row names are only routing keys.  The value for each key
    must be the canonical digest of the elaborated, normalized Lean signature
    that the source-to-row judgment actually inspected.  Keep a malformed
    non-object distinct from an empty object so the summary can fail closed.
    """

    if not isinstance(raw, dict):
        return None
    return {
        str(name or "").strip(): str(digest or "").strip().lower()
        for name, digest in raw.items()
    }


def is_proposition_definition_manifest(manifest: Any) -> bool:
    """Return whether schema-2 freezes a definition whose instantiated value is Prop."""

    if not isinstance(manifest, dict):
        return False
    if manifest.get("schema") != 2 or manifest.get("declaration_kind") != "definition":
        return False
    atoms = manifest.get("atoms")
    if not isinstance(atoms, list) or not atoms:
        return False
    result = atoms[-1]
    if not isinstance(result, dict) or result.get("ref") != "result":
        return False
    canonical = result.get("canonical")
    if not isinstance(canonical, dict) or canonical.get("tag") != "definition":
        return False
    result_type = canonical.get("type")
    if not isinstance(result_type, dict) or result_type.get("tag") != "sort":
        return False
    level = result_type.get("level")
    return isinstance(level, dict) and level.get("tag") == "zero"


def is_proposition_specification_manifest(manifest: Any) -> bool:
    """Return whether a reviewed declaration defines, rather than proves, a Prop."""

    if is_proposition_definition_manifest(manifest):
        return True
    if not isinstance(manifest, dict):
        return False
    if manifest.get("schema") != 2 or manifest.get("declaration_kind") != "inductive":
        return False
    atoms = manifest.get("atoms")
    if not isinstance(atoms, list) or not atoms:
        return False
    result = atoms[-1]
    if not isinstance(result, dict) or result.get("ref") != "result":
        return False
    canonical = result.get("canonical")
    if not isinstance(canonical, dict) or canonical.get("tag") != "inductive":
        return False
    result_type = canonical.get("type")
    if not isinstance(result_type, dict) or result_type.get("tag") != "sort":
        return False
    level = result_type.get("level")
    return isinstance(level, dict) and level.get("tag") == "zero"


def _is_conditional_boundary_judgment(judgment: dict[str, Any]) -> bool:
    """Return whether a mismatch has an audited visible-premise boundary."""

    alignment = judgment.get("obligation_alignment")
    relations_are_equivalent = (
        isinstance(alignment, list)
        and bool(alignment)
        and all(
            isinstance(item, dict)
            and str(item.get("relation") or "").strip().lower() == "equivalent"
            for item in alignment
        )
    )
    return (
        str(judgment.get("judgment") or "").strip() == "mismatch"
        and _normalize_llm_match_resolution(judgment.get("resolution"))
        == CONDITIONAL_BOUNDARY_RESOLUTION
        and not judgment.get("obligation_ledger_error")
        and not judgment.get("unmatched_source_conclusions")
        and not judgment.get("unmatched_source_inputs")
        and not judgment.get("unmatched_lean_conclusions")
        and relations_are_equivalent
        and bool(judgment.get("unjustified_lean_inputs"))
    )


def load_llm_statement_judgments(
    folder: Path,
    signature_manifests: dict[str, dict[str, Any]] | None = None,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, dict[str, Any]]:
    """Load independent semantic judgments comparing paper text and Lean-to-TeX drafts."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_llm_statement_judgments(folder, signature_manifests)
    path = llm_statement_judgments_file(folder)
    if not _dashboard_is_file(path):
        return {}
    payload = _dashboard_json_payload(path)
    if payload is None:
        return {}
    if is_non_evidence_scaffold_payload(payload):
        # A scaffold is input provenance, not a semantic judgment.  Treat it
        # exactly like absent evidence until an independent reviewer clears it.
        return {}
    if payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, folder.name}:
        return {}
    items = payload.get("items")
    if not isinstance(items, dict):
        return {}
    out: dict[str, dict[str, Any]] = {}
    source = path.name
    payload_validator = str(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
        or source
    ).strip()
    payload_has_validator = bool(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
    )
    payload_validator_type = str(
        payload.get("validator_type")
        or payload.get("generator_type")
        or ("model" if payload.get("model") else "agent" if payload.get("judge") else "")
    ).strip()
    payload_validated_at = str(
        payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
        or ""
    ).strip()
    payload_has_validated_at = bool(payload_validated_at)
    payload_prompt_version = str(payload.get("prompt_version") or "").strip()
    payload_prompt_version_stale = not llm_prompt_version_is_semantically_current(
        payload_prompt_version,
        prompt_contracts=LLM_STATEMENT_PROMPT_SEMANTIC_CONTRACTS,
        required_contract=REQUIRED_LLM_STATEMENT_SEMANTIC_CONTRACT_VERSION,
    )
    payload_comment = str(
        payload.get("comment")
        or payload.get("notes")
        or payload.get("reason")
        or payload.get("explanation")
        or ""
    ).strip()
    require_source_routes = llm_statement_source_routes_required(folder)
    require_direct_expression_semantics_review = (
        llm_direct_expression_semantics_review_required(folder)
    )
    source_inventory = paper_statement_inventory(folder) if require_source_routes else {}
    # Component anchors are route-only inventory.  They must never enter the
    # named-result coverage selector, but a v10 formula-row judgment may use
    # one when the source map explicitly pins the smaller source claim.
    source_route_inventory = dict(source_inventory)
    if require_source_routes:
        source_route_inventory.update(paper_source_component_route_inventory(folder))
        source_route_inventory.update(
            paper_source_definition_component_route_inventory(folder)
        )
    manifests = signature_manifests or {}
    manifests_by_signature: dict[str, list[dict[str, Any]]] = {}
    seen_manifest_objects: dict[str, set[int]] = {}
    for manifest in manifests.values():
        if not isinstance(manifest, dict):
            continue
        signature = str(manifest.get("sha256") or "").strip().lower()
        if not re.fullmatch(r"[0-9a-f]{64}", signature):
            continue
        # The parser exposes the same manifest under both a short and a fully
        # qualified navigation name.  Collapse only those object aliases. Two
        # independently materialized declarations with the same semantic
        # signature remain ambiguous and therefore fail closed.
        object_id = id(manifest)
        if object_id in seen_manifest_objects.setdefault(signature, set()):
            continue
        seen_manifest_objects[signature].add(object_id)
        manifests_by_signature.setdefault(signature, []).append(manifest)
    for raw_name, raw_value in items.items():
        name = str(raw_name).strip()
        if not name:
            continue
        if isinstance(raw_value, dict):
            item_prompt_version = str(
                raw_value.get("prompt_version") or payload_prompt_version
            ).strip()
            item_prompt_version_stale = not llm_prompt_version_is_semantically_current(
                item_prompt_version,
                prompt_contracts=LLM_STATEMENT_PROMPT_SEMANTIC_CONTRACTS,
                required_contract=REQUIRED_LLM_STATEMENT_SEMANTIC_CONTRACT_VERSION,
            )
            raw_judgment = (
                raw_value.get("judgment")
                or raw_value.get("verdict")
                or raw_value.get("status")
                or raw_value.get("matches")
            )
            judgment = _normalize_llm_match_judgment(raw_judgment)
            reason = str(
                raw_value.get("reason")
                or raw_value.get("notes")
                or raw_value.get("explanation")
                or ""
            ).strip()
            validator = str(
                raw_value.get("validator")
                or raw_value.get("model")
                or raw_value.get("judge")
                or raw_value.get("agent")
                or raw_value.get("generator")
                or payload_validator
            ).strip()
            has_validator = bool(
                raw_value.get("validator")
                or raw_value.get("model")
                or raw_value.get("judge")
                or raw_value.get("agent")
                or raw_value.get("generator")
                or payload_has_validator
            )
            validator_type = str(
                raw_value.get("validator_type")
                or raw_value.get("generator_type")
                or ("model" if raw_value.get("model") else "agent" if raw_value.get("judge") else "")
                or payload_validator_type
            ).strip()
            validated_at = str(
                raw_value.get("validated_at")
                or raw_value.get("timestamp")
                or raw_value.get("generated_at")
                or payload_validated_at
            ).strip()
            has_validated_at = bool(
                raw_value.get("validated_at")
                or raw_value.get("timestamp")
                or raw_value.get("generated_at")
                or payload_has_validated_at
            )
            comment = str(
                raw_value.get("comment")
                or raw_value.get("notes")
                or raw_value.get("reason")
                or raw_value.get("explanation")
                or payload_comment
                or ""
            ).strip()
            resolution = _normalize_llm_match_resolution(
                raw_value.get("resolution")
                or raw_value.get("accepted_resolution")
                or raw_value.get("review_resolution")
            )
            boundary_type = str(
                raw_value.get("boundary_type")
                or raw_value.get("resolution_type")
                or raw_value.get("boundary_kind")
                or ""
            ).strip()
            boundary_names = _normalize_string_list(
                raw_value.get("boundary_names")
                or raw_value.get("boundaries")
                or raw_value.get("boundary_name")
            )
            conditional_premises = _normalize_string_list(
                raw_value.get("conditional_premises")
                or raw_value.get("extra_premises")
                or raw_value.get("conditional_on")
            )
            resolution_reason = str(
                raw_value.get("resolution_reason")
                or raw_value.get("boundary_reason")
                or raw_value.get("resolution_notes")
                or ""
            ).strip()
            # A stored row key is only a navigation locator.  When a sidecar
            # was mechanically rekeyed, recover its manifest solely from one
            # exact elaborated-signature digest; ambiguous matches remain
            # deliberately unbound and therefore fail the obligation ledger.
            signature_manifest = manifests.get(name)
            recorded_signature = str(
                raw_value.get("lean_signature_sha256") or ""
            ).strip().lower()
            if (
                signature_manifest is None
                and re.fullmatch(r"[0-9a-f]{64}", recorded_signature)
            ):
                matching_manifests = manifests_by_signature.get(
                    recorded_signature, []
                )
                if len(matching_manifests) == 1:
                    signature_manifest = matching_manifests[0]
            require_source_definition_semantics_review = bool(
                require_source_routes
                and direct_source_definition_route_keys(
                    raw_value,
                    inventory=source_route_inventory,
                    include_direct_expressions=(
                        require_direct_expression_semantics_review
                    ),
                )
            )
            obligation_ledger_error = semantic_obligation_ledger_error(
                raw_value,
                signature_manifest,
                require_source_definition_semantics_review=(
                    require_source_definition_semantics_review
                ),
            )
            source_route_error = (
                source_route_pin_error(
                    raw_value,
                    inventory=source_route_inventory,
                    require_statement_target=True,
                    require_verbatim_source_inputs=(
                        statement_review_requires_verbatim_source_inputs(
                            raw_value,
                            prompt_version=item_prompt_version,
                        )
                    ),
                )
                if require_source_routes
                else ""
            )
            if source_route_error:
                obligation_ledger_error = (
                    f"{obligation_ledger_error}; {source_route_error}"
                    if obligation_ledger_error
                    else source_route_error
                )
            unmatched_source_conclusions = (
                list(raw_value.get("unmatched_source_conclusions"))
                if isinstance(raw_value.get("unmatched_source_conclusions"), list)
                else []
            )
            unjustified_lean_inputs = (
                list(raw_value.get("unjustified_lean_inputs"))
                if isinstance(raw_value.get("unjustified_lean_inputs"), list)
                else []
            )
            unmatched_source_inputs = (
                list(raw_value.get("unmatched_source_inputs"))
                if isinstance(raw_value.get("unmatched_source_inputs"), list)
                else []
            )
            unmatched_lean_conclusions = (
                list(raw_value.get("unmatched_lean_conclusions"))
                if isinstance(raw_value.get("unmatched_lean_conclusions"), list)
                else []
            )
            obligation_alignment = (
                list(raw_value.get("obligation_alignment"))
                if isinstance(raw_value.get("obligation_alignment"), list)
                else []
            )
            out[name] = {
                "judgment": judgment,
                "reason": reason,
                "source": source,
                "validator": validator,
                "validator_type": validator_type,
                "validated_at": validated_at,
                "metadata_missing": not bool(has_validator and has_validated_at),
                "comment": comment,
                "resolution": resolution,
                "boundary_type": boundary_type,
                "boundary_names": boundary_names,
                "conditional_premises": conditional_premises,
                "resolution_reason": resolution_reason,
                "obligation_ledger_error": obligation_ledger_error,
                "source_route_error": source_route_error,
                "source_route_validation_performed": bool(require_source_routes),
                "source_routes": (
                    raw_value.get("source_routes")
                    if isinstance(raw_value.get("source_routes"), list)
                    else []
                ),
                "unmatched_source_conclusions": unmatched_source_conclusions,
                "unmatched_source_inputs": unmatched_source_inputs,
                "unjustified_lean_inputs": unjustified_lean_inputs,
                "unmatched_lean_conclusions": unmatched_lean_conclusions,
                "obligation_alignment": obligation_alignment,
                "semantic_scope_review": (
                    raw_value.get("semantic_scope_review")
                    if isinstance(raw_value.get("semantic_scope_review"), dict)
                    else {}
                ),
                "prompt_version": item_prompt_version,
                "prompt_version_stale": item_prompt_version_stale,
                "source_input_protocol": str(
                    raw_value.get("source_input_protocol") or ""
                ).strip(),
                "source_input_bundle_sha256": str(
                    raw_value.get("source_input_bundle_sha256") or ""
                ).strip().lower(),
                "lean_target_protocol": str(
                    raw_value.get("lean_target_protocol") or ""
                ).strip(),
                "semantic_target_declaration": str(
                    raw_value.get("semantic_target_declaration") or ""
                ).strip(),
                "lean_statement_sha256": str(raw_value.get("lean_statement_sha256") or "").strip(),
                "lean_signature_sha256": str(raw_value.get("lean_signature_sha256") or "").strip(),
                "paper_statement_sha256": str(raw_value.get("paper_statement_sha256") or "").strip(),
                "tex_statement_sha256": str(raw_value.get("tex_statement_sha256") or "").strip(),
            }
        else:
            judgment = _normalize_llm_match_judgment(raw_value)
            if judgment:
                out[name] = {
                    "judgment": judgment,
                    "reason": "",
                    "source": source,
                    "validator": payload_validator,
                    "validator_type": payload_validator_type,
                    "validated_at": payload_validated_at,
                    "metadata_missing": not bool(payload_has_validator and payload_has_validated_at),
                    "comment": payload_comment,
                    "resolution": "",
                    "boundary_type": "",
                    "boundary_names": [],
                    "conditional_premises": [],
                    "resolution_reason": "",
                    "obligation_ledger_error": "judgment row is not an object",
                    "unmatched_source_conclusions": [],
                    "unmatched_source_inputs": [],
                    "unjustified_lean_inputs": [],
                    "unmatched_lean_conclusions": [],
                    "obligation_alignment": [],
                    "semantic_scope_review": {},
                    "prompt_version": payload_prompt_version,
                    "prompt_version_stale": payload_prompt_version_stale,
                }
    return out


def _validated_unique_source_component_target_sha256(
    judgment: Mapping[str, Any],
) -> str:
    """Return one component target only after full source-route validation.

    The dashboard paper text may be an aggregate parent used for display.  A
    component-routed judgment instead reviews the exact entry-local component,
    but that narrower digest is trustworthy only when the generic source-route
    validator accepted the complete route and exactly one component route pins
    that target.  Route keys and declaration names are deliberately ignored.
    """

    if judgment.get("source_route_validation_performed") is not True:
        return ""
    if "source_route_error" not in judgment or str(
        judgment.get("source_route_error") or ""
    ).strip():
        return ""
    routes = judgment.get("source_routes")
    if not isinstance(routes, list):
        return ""
    recorded_target = str(
        judgment.get("paper_statement_sha256") or ""
    ).strip().lower()
    targets = [
        str(route.get("source_statement_sha256") or "").strip().lower()
        for route in routes
        if isinstance(route, Mapping)
        and str(route.get("route_kind") or "").strip().lower()
        == "source_component"
    ]
    matching_targets = [
        target
        for target in targets
        if target == recorded_target
        and SOURCE_ARTIFACT_SHA256_RE.fullmatch(target)
    ]
    if len(matching_targets) != 1:
        return ""
    return matching_targets[0]


def _llm_statement_judgment_is_stale(
    judgment: dict[str, Any],
    *,
    signature_sha256: str,
    lean_statement: str,
    paper_statement: str,
    agent_statement: str,
    source_input_bundle_sha256: str = "",
) -> bool:
    """Re-evaluate statement evidence against the current audit contract.

    The elaborated signature is necessary but not a substitute for the exact
    current declaration text.  Canonicalizer upgrades can preserve or rewrite
    a signature representation, and an old sidecar field must not make a newly
    added theorem premise look current merely because its source and TeX pins
    still match.
    """

    if not judgment:
        return False
    recorded_signature = str(judgment.get("lean_signature_sha256") or "").strip()
    recorded_lean = str(judgment.get("lean_statement_sha256") or "").strip()
    recorded_paper = str(judgment.get("paper_statement_sha256") or "").strip()
    recorded_tex = str(judgment.get("tex_statement_sha256") or "").strip()
    is_v11 = (
        str(judgment.get("prompt_version") or "").strip()
        == REQUIRED_LLM_STATEMENT_PROMPT_VERSION
    )
    if is_v11:
        recorded_source_input = str(
            judgment.get("source_input_bundle_sha256") or ""
        ).strip().lower()
        return (
            not recorded_signature
            or not recorded_lean
            or not source_input_bundle_sha256
            or recorded_signature != signature_sha256
            or recorded_lean != statement_digest(lean_statement)
            # The semantic target is the literal source text supplied to the
            # reviewer.  The distinct bundle digest binds that text to its
            # byte-pinned anchors and permitted context.
            or recorded_paper != statement_digest(paper_statement)
            or recorded_source_input != source_input_bundle_sha256
            or str(judgment.get("source_input_protocol") or "").strip()
            != "verbatim_source_anchor_bundle_v1"
            or str(judgment.get("lean_target_protocol") or "").strip()
            != "expanded_paperinterface_spec_v1"
            or bool(judgment.get("prompt_version_stale"))
            or bool(judgment.get("metadata_missing"))
            or bool(judgment.get("obligation_ledger_error"))
            or not signature_sha256
        )
    if not normalize_statement(paper_statement):
        return True
    component_target = _validated_unique_source_component_target_sha256(judgment)
    paper_digest_is_current = recorded_paper == statement_digest(
        paper_statement
    ) or bool(component_target and recorded_paper == component_target)
    return (
        not recorded_signature
        or not recorded_lean
        or not recorded_paper
        or not recorded_tex
        or recorded_signature != signature_sha256
        or recorded_lean != statement_digest(lean_statement)
        or not paper_digest_is_current
        or recorded_tex != statement_digest(agent_statement)
        or bool(judgment.get("prompt_version_stale"))
        or bool(judgment.get("metadata_missing"))
        or bool(judgment.get("obligation_ledger_error"))
        or not signature_sha256
    )


def _semantic_statement_judgment_identity(
    judgment: dict[str, Any],
) -> tuple[str, ...] | None:
    """Return a judgment's exact semantic reuse identity, never its row name."""

    fields = (
        "lean_signature_sha256",
        "paper_statement_sha256",
        "tex_statement_sha256",
    )
    values = tuple(str(judgment.get(field) or "").strip().lower() for field in fields)
    if (
        not all(re.fullmatch(r"[0-9a-f]{64}", value) for value in values)
        or values[1] == statement_digest("")
    ):
        return None
    if str(judgment.get("prompt_version") or "").strip() == REQUIRED_LLM_STATEMENT_PROMPT_VERSION:
        source_input = str(
            judgment.get("source_input_bundle_sha256") or ""
        ).strip().lower()
        direct_lean = str(judgment.get("lean_statement_sha256") or "").strip().lower()
        if not (
            SOURCE_ARTIFACT_SHA256_RE.fullmatch(source_input)
            and SOURCE_ARTIFACT_SHA256_RE.fullmatch(direct_lean)
        ):
            return None
        return ("v11", values[0], source_input, direct_lean)
    return values


def _semantic_statement_judgment_index(
    judgments: Mapping[str, dict[str, Any]],
) -> dict[tuple[str, ...], list[tuple[str, dict[str, Any]]]]:
    """Index judgments once by exact content identity, preserving ambiguity."""

    index: dict[tuple[str, str, str], list[tuple[str, dict[str, Any]]]] = {}
    for key, judgment in judgments.items():
        identity = _semantic_statement_judgment_identity(judgment)
        if identity is not None:
            index.setdefault(identity, []).append((key, judgment))
    return index


def _current_semantic_statement_judgment_for_item(
    item: ReviewItem,
    judgments: dict[str, dict[str, Any]],
    *,
    identity_index: Mapping[
        tuple[str, ...], list[tuple[str, dict[str, Any]]]
    ]
    | None = None,
) -> tuple[str, dict[str, Any] | None, bool]:
    """Resolve one current semantic judgment through exact content pins.

    The match deliberately ignores sidecar storage keys and Lean declaration
    spelling.  A key rename can be reused only when exactly one judgment has
    the current elaborated signature plus current source-facing and translated
    statement digests.  Multiple candidates are an ambiguity, not a reason to
    choose the familiar name.
    """

    return _current_semantic_statement_judgment(
        signature_sha256=item.lean_signature_sha256,
        lean_statement=item.lean_statement,
        paper_statement=item.paper_statement,
        agent_statement=item.agent_statement,
        source_input_bundle_sha256=item.source_input_bundle_sha256,
        judgments=judgments,
        identity_index=identity_index,
    )


def _current_semantic_statement_judgment(
    *,
    signature_sha256: str,
    lean_statement: str,
    paper_statement: str,
    agent_statement: str,
    source_input_bundle_sha256: str = "",
    judgments: dict[str, dict[str, Any]],
    identity_index: Mapping[
        tuple[str, ...], list[tuple[str, dict[str, Any]]]
    ]
    | None = None,
) -> tuple[str, dict[str, Any] | None, bool]:
    """Resolve one judgment before or after a ``ReviewItem`` is materialized."""

    signature = str(signature_sha256 or "").strip().lower()
    identity: tuple[str, ...] = (
        ("v11", signature, source_input_bundle_sha256, statement_digest(lean_statement))
        if source_input_bundle_sha256
        else (
            signature,
            statement_digest(paper_statement),
            statement_digest(agent_statement),
        )
    )
    if not re.fullmatch(r"[0-9a-f]{64}", signature):
        return "", None, False
    identity_candidates = (
        identity_index.get(identity, [])
        if identity_index is not None
        else [
            (key, judgment)
            for key, judgment in judgments.items()
            if _semantic_statement_judgment_identity(judgment) == identity
        ]
    )
    if not identity_candidates:
        translated_digest = statement_digest(agent_statement)
        identity_candidates = [
            (key, judgment)
            for key, judgment in judgments.items()
            if str(judgment.get("lean_signature_sha256") or "")
            .strip()
            .lower()
            == signature
            and str(judgment.get("tex_statement_sha256") or "")
            .strip()
            .lower()
            == translated_digest
            and bool(_validated_unique_source_component_target_sha256(judgment))
        ]
    candidates = [
        (key, judgment)
        for key, judgment in identity_candidates
        if not _llm_statement_judgment_is_stale(
            judgment,
            signature_sha256=signature_sha256,
            lean_statement=lean_statement,
            paper_statement=paper_statement,
            agent_statement=agent_statement,
            source_input_bundle_sha256=source_input_bundle_sha256,
        )
    ]
    if len(candidates) == 1:
        return candidates[0][0], candidates[0][1], False
    return "", None, len(candidates) > 1


def load_llm_paper_coverage_audit(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, Any]:
    """Load optional LLM audit of source-paper statement coverage by review rows."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_llm_paper_coverage_audit(folder)
    path = llm_paper_coverage_file(folder)
    if not _dashboard_is_file(path):
        return {}
    payload = _dashboard_json_payload(path)
    if payload is None:
        return {}
    payload_non_evidence_scaffold = is_non_evidence_scaffold_payload(payload)
    if payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, folder.name}:
        return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        raw_items = {}
    items: dict[str, dict[str, Any]] = {}
    payload_validator = str(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
        or path.name
    ).strip()
    payload_has_validator = bool(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
    )
    payload_validator_type = str(
        payload.get("validator_type")
        or payload.get("generator_type")
        or ("model" if payload.get("model") else "agent" if payload.get("judge") else "")
    ).strip()
    payload_validated_at = str(
        payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
        or ""
    ).strip()
    payload_has_validated_at = bool(payload_validated_at)
    payload_audit_kind = str(
        payload.get("audit_kind")
        or payload.get("coverage_audit_kind")
        or payload.get("kind")
        or ""
    ).strip()
    payload_prompt_version = str(payload.get("prompt_version") or "").strip()
    payload_prompt_version_stale = (
        payload_prompt_version != REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION
    )
    payload_source_grounded = bool(payload.get("source_grounded") is True)
    payload_source_input_protocol = str(
        payload.get("source_input_protocol") or ""
    ).strip()
    payload_seed_scaffold = (
        payload_non_evidence_scaffold
        or bool(payload.get("seed_scaffold") is True)
        or payload_audit_kind in PAPER_COVERAGE_SCAFFOLD_KINDS
    )
    for raw_key, raw_value in raw_items.items():
        key = str(raw_key or "").strip()
        if not key:
            continue
        if isinstance(raw_value, dict):
            raw_judgment = (
                raw_value.get("coverage")
                or raw_value.get("judgment")
                or raw_value.get("verdict")
                or raw_value.get("status")
                or raw_value.get("covered")
            )
            items[key] = {
                "coverage": _normalize_paper_coverage_judgment(raw_judgment),
                "review_rows": _normalize_string_list(
                    raw_value.get("review_rows")
                    or raw_value.get("rows")
                    or raw_value.get("lean_rows")
                    or raw_value.get("declarations")
                ),
                "review_row_signature_sha256": _normalize_review_row_signature_pins(
                    raw_value.get("review_row_signature_sha256")
                ),
                "support_declarations": _normalize_string_list(
                    raw_value.get("support_declarations")
                    or raw_value.get("support_rows")
                    or raw_value.get("support_lean_declarations")
                    or raw_value.get("support_lean")
                ),
                "reason": str(
                    raw_value.get("reason")
                    or raw_value.get("notes")
                    or raw_value.get("explanation")
                    or ""
                ).strip(),
                "source_evidence": str(raw_value.get("source_evidence") or "").strip(),
                "source_scope_judgment": str(
                    raw_value.get("source_scope_judgment") or ""
                ).strip(),
                "source_anchor_quote_sha256": str(
                    raw_value.get("source_anchor_quote_sha256") or ""
                ).strip().lower(),
                "source_anchor_quote_identity_sha256": str(
                    raw_value.get("source_anchor_quote_identity_sha256") or ""
                ).strip().lower(),
                "target_kind": str(raw_value.get("target_kind") or "").strip().lower(),
                "archival_statement_sha256": str(
                    raw_value.get("archival_statement_sha256") or ""
                ).strip().lower(),
                "corrected_target_sha256": str(
                    raw_value.get("corrected_target_sha256") or ""
                ).strip().lower(),
                "governing_defect_ids": _normalize_string_list(
                    raw_value.get("governing_defect_ids")
                ),
                "archival_equivalence_claimed": raw_value.get(
                    "archival_equivalence_claimed"
                ),
                "dashboard_evidence": str(
                    raw_value.get("dashboard_evidence")
                    or raw_value.get("lean_evidence")
                    or ""
                ).strip(),
                "statement_sha256": str(raw_value.get("statement_sha256") or "").strip(),
                "source_item_coverage_digest_schema": raw_value.get(
                    "source_item_coverage_digest_schema"
                ),
                "source_item_coverage_sha256": str(
                    raw_value.get("source_item_coverage_sha256") or ""
                ).strip().lower(),
                "validator": str(
                    raw_value.get("validator")
                    or raw_value.get("model")
                    or raw_value.get("judge")
                    or raw_value.get("agent")
                    or raw_value.get("generator")
                    or payload_validator
                ).strip(),
                "metadata_missing": not bool(
                    (
                        raw_value.get("validator")
                        or raw_value.get("model")
                        or raw_value.get("judge")
                        or raw_value.get("agent")
                        or raw_value.get("generator")
                        or payload_has_validator
                    )
                    and (
                        raw_value.get("validated_at")
                        or raw_value.get("timestamp")
                        or raw_value.get("generated_at")
                        or payload_has_validated_at
                    )
                ),
                "validator_type": str(
                    raw_value.get("validator_type")
                    or raw_value.get("generator_type")
                    or (
                        "model"
                        if raw_value.get("model")
                        else "agent"
                        if raw_value.get("judge")
                        else ""
                    )
                    or payload_validator_type
                ).strip(),
                "validated_at": str(
                    raw_value.get("validated_at")
                    or raw_value.get("timestamp")
                    or raw_value.get("generated_at")
                    or payload_validated_at
                ).strip(),
                "audit_kind": str(raw_value.get("audit_kind") or payload_audit_kind).strip(),
                "prompt_version": payload_prompt_version,
                "prompt_version_stale": payload_prompt_version_stale,
                "source_grounded": bool(
                    raw_value.get("source_grounded") is True or payload_source_grounded
                ),
                "seed_scaffold": bool(raw_value.get("seed_scaffold") is True or payload_seed_scaffold),
            }
        else:
            items[key] = {
                "coverage": _normalize_paper_coverage_judgment(raw_value),
                "review_rows": [],
                "review_row_signature_sha256": None,
                "support_declarations": [],
                "reason": "",
                "source_evidence": "",
                "source_scope_judgment": "",
                "source_anchor_quote_sha256": "",
                "source_anchor_quote_identity_sha256": "",
                "target_kind": "",
                "archival_statement_sha256": "",
                "corrected_target_sha256": "",
                "governing_defect_ids": [],
                "archival_equivalence_claimed": None,
                "dashboard_evidence": "",
                "statement_sha256": "",
                "source_item_coverage_digest_schema": None,
                "source_item_coverage_sha256": "",
                "validator": payload_validator,
                "validator_type": payload_validator_type,
                "validated_at": payload_validated_at,
                "metadata_missing": not bool(payload_has_validator and payload_has_validated_at),
                "audit_kind": payload_audit_kind,
                "prompt_version": payload_prompt_version,
                "prompt_version_stale": payload_prompt_version_stale,
                "source_grounded": payload_source_grounded,
                "seed_scaffold": payload_seed_scaffold,
            }
    return {
        "source": path.name,
        "validator": payload_validator,
        "validator_type": payload_validator_type,
        "validated_at": payload_validated_at,
        "metadata_missing": not bool(payload_has_validator and payload_has_validated_at),
        "audit_kind": payload_audit_kind,
        "prompt_version": payload_prompt_version,
        "prompt_version_stale": payload_prompt_version_stale,
        "source_grounded": payload_source_grounded,
        "source_input_protocol": payload_source_input_protocol,
        "seed_scaffold": payload_seed_scaffold,
        "comment": str(payload.get("comment") or payload.get("notes") or "").strip(),
        "paper_statement_inventory_sha256": str(
            payload.get("paper_statement_inventory_sha256")
            or payload.get("statement_inventory_sha256")
            or payload.get("inventory_sha256")
            or ""
        ).strip(),
        "review_surface_sha256": str(payload.get("review_surface_sha256") or "").strip(),
        "source_coverage_mode": str(payload.get("source_coverage_mode") or "").strip(),
        "source_artifact_path": str(payload.get("source_artifact_path") or "").strip(),
        "source_artifact_sha256": str(
            payload.get("source_artifact_sha256") or ""
        ).strip().lower(),
        "items": items,
    }


def llm_review_surface_file(folder: Path) -> Path:
    """Return the preferred LLM review-surface audit sidecar for a paper."""

    tracked_path = paper_relative_file(folder, DEFAULT_LLM_REVIEW_SURFACE_FILE, "review_surface_llm.json")
    if _dashboard_audit_inputs() is not None or _dashboard_is_file(tracked_path):
        return tracked_path
    return folder / ".review_traces" / "review_surface_llm.json"


def _normalize_surface_audit_judgment(raw: Any) -> str:
    """Normalize review-surface audit verdicts for dashboard display."""

    if isinstance(raw, bool):
        return "passes" if raw else "needs_curation"
    value = str(raw or "").strip().lower()
    if value in {
        "pass",
        "passes",
        "ok",
        "good",
        "paper_facing",
        "paper-facing",
        "only_paper_facing",
        "only paper facing",
    }:
        return "passes"
    if value in {
        "fail",
        "fails",
        "needs_curation",
        "needs curation",
        "too_broad",
        "too broad",
        "not_paper_facing",
        "not paper facing",
    }:
        return "needs_curation"
    if value in {"uncertain", "unknown", "unsure", "needs_review", "needs review"}:
        return "uncertain"
    return value


def load_llm_review_surface_audit(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, Any]:
    """Load optional LLM audit of whether dashboard rows are paper-facing."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_llm_review_surface_audit(folder)
    path = llm_review_surface_file(folder)
    if not _dashboard_is_file(path):
        return {}
    payload = _dashboard_json_payload(path)
    if payload is None:
        return {}
    non_evidence_scaffold = is_non_evidence_scaffold_payload(payload)
    if payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, folder.name}:
        return {}
    raw_judgment = (
        payload.get("judgment")
        or payload.get("verdict")
        or payload.get("status")
        or payload.get("paper_facing")
    )
    payload_prompt_version = str(payload.get("prompt_version") or "").strip()
    payload_validator = str(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
        or ""
    ).strip()
    payload_validated_at = str(
        payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
        or ""
    ).strip()
    return {
        "judgment": _normalize_surface_audit_judgment(raw_judgment),
        "reason": str(payload.get("reason") or payload.get("notes") or "").strip(),
        "source": path.name,
        "validator": payload_validator,
        "validated_at": payload_validated_at,
        "metadata_missing": not bool(payload_validator and payload_validated_at),
        "review_rows": payload.get("review_rows"),
        "review_surface_sha256": str(payload.get("review_surface_sha256") or "").strip(),
        "prompt_version": payload_prompt_version,
        "prompt_version_stale": payload_prompt_version
        != REQUIRED_LLM_REVIEW_SURFACE_PROMPT_VERSION,
        "non_evidence_scaffold": non_evidence_scaffold,
    }


def llm_assumption_judgments_file(folder: Path) -> Path:
    """Return the preferred LLM paper-assumption provenance sidecar."""

    tracked_path = paper_relative_file(folder, DEFAULT_LLM_ASSUMPTION_JUDGE_FILE, "assumption_match_llm.json")
    if _dashboard_audit_inputs() is not None or _dashboard_is_file(tracked_path):
        return tracked_path
    return folder / ".review_traces" / "assumption_match_llm.json"


def _normalize_assumption_judgment(raw: Any) -> str:
    """Normalize LLM verdicts for paper-assumption provenance."""

    if isinstance(raw, bool):
        return "paper_assumption" if raw else "not_paper_assumption"
    value = str(raw or "").strip().lower()
    if value in {
        "paper_assumption",
        "paper assumption",
        "source_assumption",
        "source assumption",
        "model_assumption",
        "model assumption",
        "match",
        "matches",
        "yes",
        "true",
    }:
        return "paper_assumption"
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
        "mismatch",
        "no",
        "false",
    }:
        return "not_paper_assumption"
    if value in {"uncertain", "unknown", "unsure", "needs_review", "needs review", "partial"}:
        return "uncertain"
    return value


def _normalize_premise_text(raw: str) -> str:
    """Normalize a Lean premise line for robust JSON/source comparisons."""

    return re.sub(r"\s+", " ", str(raw or "").strip())


def _assumption_premise_judgments(raw_value: Any) -> dict[str, dict[str, str]]:
    """Extract nested premise-level provenance judgments from an assumption row."""

    if not isinstance(raw_value, dict):
        return {}
    raw_items = (
        raw_value.get("premise_judgments")
        or raw_value.get("premise_items")
        or raw_value.get("premise_validations")
        or raw_value.get("premises_judged")
    )
    out: dict[str, dict[str, Any]] = {}

    def add_item(raw_premise: Any, raw_item: Any) -> None:
        premise = _normalize_premise_text(str(raw_premise or ""))
        if not premise:
            return
        if isinstance(raw_item, dict):
            raw_judgment = (
                raw_item.get("judgment")
                or raw_item.get("verdict")
                or raw_item.get("status")
                or raw_item.get("source_text_judgment")
            )
            out[premise] = {
                "judgment": _normalize_assumption_judgment(raw_judgment),
                "reason": str(
                    raw_item.get("reason")
                    or raw_item.get("notes")
                    or raw_item.get("explanation")
                    or ""
                ).strip(),
                "source_location": str(raw_item.get("source_location") or "").strip(),
            }
        else:
            out[premise] = {
                "judgment": _normalize_assumption_judgment(raw_item),
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


def load_llm_assumption_judgments(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, dict[str, Any]]:
    """Load optional LLM judgments that listed assumptions are source assumptions."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_llm_assumption_judgments(folder)
    path = llm_assumption_judgments_file(folder)
    if not _dashboard_is_file(path):
        return {}
    payload = _dashboard_json_payload(path)
    if payload is None:
        return {}
    if payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, folder.name}:
        return {}
    items = payload.get("items")
    if not isinstance(items, dict):
        return {}
    source = path.name
    payload_validator = str(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
        or source
    ).strip()
    payload_has_validator = bool(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
    )
    payload_validator_type = str(
        payload.get("validator_type")
        or payload.get("generator_type")
        or ("model" if payload.get("model") else "agent" if payload.get("judge") else "")
    ).strip()
    payload_validated_at = str(
        payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
        or ""
    ).strip()
    payload_has_validated_at = bool(payload_validated_at)
    payload_comment = str(
        payload.get("comment")
        or payload.get("notes")
        or payload.get("reason")
        or payload.get("explanation")
        or ""
    ).strip()
    payload_prompt_version = str(payload.get("prompt_version") or "").strip()
    payload_prompt_version_stale = payload_prompt_version != REQUIRED_LLM_ASSUMPTION_PROMPT_VERSION
    out: dict[str, dict[str, str]] = {}
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
            reason = str(
                raw_value.get("reason")
                or raw_value.get("notes")
                or raw_value.get("explanation")
                or ""
            ).strip()
            validator = str(
                raw_value.get("validator")
                or raw_value.get("model")
                or raw_value.get("judge")
                or raw_value.get("agent")
                or raw_value.get("generator")
                or payload_validator
            ).strip()
            has_validator = bool(
                raw_value.get("validator")
                or raw_value.get("model")
                or raw_value.get("judge")
                or raw_value.get("agent")
                or raw_value.get("generator")
                or payload_has_validator
            )
            validator_type = str(
                raw_value.get("validator_type")
                or raw_value.get("generator_type")
                or ("model" if raw_value.get("model") else "agent" if raw_value.get("judge") else "")
                or payload_validator_type
            ).strip()
            validated_at = str(
                raw_value.get("validated_at")
                or raw_value.get("timestamp")
                or raw_value.get("generated_at")
                or payload_validated_at
            ).strip()
            has_validated_at = bool(
                raw_value.get("validated_at")
                or raw_value.get("timestamp")
                or raw_value.get("generated_at")
                or payload_has_validated_at
            )
            comment = str(
                raw_value.get("comment")
                or raw_value.get("notes")
                or raw_value.get("reason")
                or raw_value.get("explanation")
                or payload_comment
                or ""
            ).strip()
            out[name] = {
                "judgment": _normalize_assumption_judgment(raw_judgment),
                "reason": reason,
                "source": source,
                "validator": validator,
                "validator_type": validator_type,
                "validated_at": validated_at,
                "comment": comment,
                "prompt_version": payload_prompt_version,
                "prompt_version_stale": payload_prompt_version_stale,
                "metadata_missing": not bool(has_validator and has_validated_at),
                "lean_statement_sha256": str(raw_value.get("lean_statement_sha256") or "").strip(),
                "lean_signature_sha256": str(raw_value.get("lean_signature_sha256") or "").strip(),
                "paper_statement_sha256": str(raw_value.get("paper_statement_sha256") or "").strip(),
                "premise_judgments": _assumption_premise_judgments(raw_value),
                "source_record_semantic_parent_v1": (
                    dict(raw_value["source_record_semantic_parent_v1"])
                    if isinstance(
                        raw_value.get("source_record_semantic_parent_v1"), dict
                    )
                    else None
                ),
            }
        else:
            judgment = _normalize_assumption_judgment(raw_value)
            if judgment:
                out[name] = {
                    "judgment": judgment,
                    "reason": "",
                    "source": source,
                    "validator": payload_validator,
                    "validator_type": payload_validator_type,
                    "validated_at": payload_validated_at,
                    "comment": payload_comment,
                    "prompt_version": payload_prompt_version,
                    "prompt_version_stale": payload_prompt_version_stale,
                    "metadata_missing": not bool(payload_has_validator and payload_has_validated_at),
                    "premise_judgments": {},
                }
    return out


def llm_lean_to_tex_drafts_file(folder: Path) -> Path:
    """Return the preferred Lean-to-TeX draft sidecar for a paper."""

    tracked_path = paper_relative_file(folder, DEFAULT_LLM_LEAN_TO_TEX_FILE, "lean_to_tex_llm.json")
    if _dashboard_audit_inputs() is not None or _dashboard_is_file(tracked_path):
        return tracked_path
    return folder / ".review_traces" / "lean_to_tex_llm.json"


def _run_pdftotext_bbox(pdf_path: Path, page: int) -> str:
    """Return pdftotext bbox-layout XML for one page, or empty on failure."""

    try:
        proc = subprocess.run(
            [
                "pdftotext",
                "-bbox-layout",
                "-f",
                str(page),
                "-l",
                str(page),
                str(pdf_path),
                "-",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired):
        return ""
    if proc.returncode != 0:
        return ""
    return proc.stdout


def _parse_pdf_bbox_words(xml_text: str) -> tuple[float, float, list[dict[str, Any]]]:
    """Parse pdftotext bbox XML into page dimensions and word boxes."""

    if not xml_text.strip():
        return 0.0, 0.0, []
    try:
        root = ElementTree.fromstring(xml_text)
    except ElementTree.ParseError:
        return _parse_pdf_bbox_words_with_regex(xml_text)
    page_node = next((node for node in root.iter() if node.tag.endswith("page")), None)
    if page_node is None:
        return 0.0, 0.0, []
    try:
        page_width = float(page_node.attrib.get("width", "0"))
        page_height = float(page_node.attrib.get("height", "0"))
    except ValueError:
        page_width = 0.0
        page_height = 0.0
    words: list[dict[str, Any]] = []
    for word_node in root.iter():
        if not word_node.tag.endswith("word"):
            continue
        text = "".join(word_node.itertext()).strip()
        if not text:
            continue
        try:
            words.append(
                {
                    "text": text,
                    "x_min": float(word_node.attrib["xMin"]),
                    "y_min": float(word_node.attrib["yMin"]),
                    "x_max": float(word_node.attrib["xMax"]),
                    "y_max": float(word_node.attrib["yMax"]),
                }
            )
        except (KeyError, ValueError):
            continue
    return page_width, page_height, words


def _parse_pdf_bbox_words_with_regex(xml_text: str) -> tuple[float, float, list[dict[str, Any]]]:
    """Fallback bbox parser for PDFs whose extracted XHTML has invalid glyph bytes."""

    page_match = re.search(
        r"<page\b[^>]*\bwidth=\"([0-9.]+)\"[^>]*\bheight=\"([0-9.]+)\"",
        xml_text,
    )
    if not page_match:
        return 0.0, 0.0, []
    try:
        page_width = float(page_match.group(1))
        page_height = float(page_match.group(2))
    except ValueError:
        return 0.0, 0.0, []

    word_re = re.compile(
        r"<word\b[^>]*\bxMin=\"([0-9.]+)\"[^>]*\byMin=\"([0-9.]+)\""
        r"[^>]*\bxMax=\"([0-9.]+)\"[^>]*\byMax=\"([0-9.]+)\"[^>]*>(.*?)</word>",
        flags=re.DOTALL,
    )
    words: list[dict[str, Any]] = []
    for match in word_re.finditer(xml_text):
        text = re.sub(r"<[^>]+>", "", match.group(5))
        text = html.unescape(text).strip()
        if not text:
            continue
        try:
            words.append(
                {
                    "text": text,
                    "x_min": float(match.group(1)),
                    "y_min": float(match.group(2)),
                    "x_max": float(match.group(3)),
                    "y_max": float(match.group(4)),
                }
            )
        except ValueError:
            continue
    return page_width, page_height, words


def _find_statement_start_y(words: list[dict[str, Any]], kind: str, number: str) -> float | None:
    """Locate a statement heading in bbox word output."""

    for index, word in enumerate(words[:-1]):
        if word["text"].strip(".,") != kind:
            continue
        nxt = words[index + 1]
        if nxt["text"].strip(".,") != number:
            continue
        if abs(float(nxt["y_min"]) - float(word["y_min"])) > 6.0:
            continue
        return float(word["y_min"])
    return None


def _find_statement_stop_y(words: list[dict[str, Any]], top_y: float, current_bottom: float) -> float:
    """Find an earlier paper-proof/section boundary inside a candidate crop."""

    stop_sequences = [
        ("Proof",),
        ("Proof.",),
        ("To", "prove"),
        ("The", "proof"),
        ("What", "does"),
    ]
    for index, word in enumerate(words):
        y_min = float(word["y_min"])
        if y_min <= top_y + 18.0 or y_min >= current_bottom:
            continue
        if float(word["x_min"]) > 115.0:
            continue
        row_words = [
            str(candidate["text"]).strip(".,:;")
            for candidate in words[index : index + 4]
            if abs(float(candidate["y_min"]) - y_min) <= 3.0
        ]
        if any(row_words[: len(sequence)] == list(sequence) for sequence in stop_sequences):
            return y_min - 10.0
    return current_bottom


def _render_pdf_page_to_png(pdf_path: Path, page: int, output_dir: Path, digest: str) -> Path | None:
    """Render a single PDF page to a PNG cache file."""

    page_path = output_dir / f"page-{page}-{digest[:12]}.png"
    if page_path.exists():
        return page_path
    prefix = output_dir / f"page-{page}-{digest[:12]}"
    try:
        proc = subprocess.run(
            [
                "pdftoppm",
                "-f",
                str(page),
                "-l",
                str(page),
                "-r",
                "180",
                "-png",
                str(pdf_path),
                str(prefix),
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=20,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if proc.returncode != 0:
        return None
    rendered = sorted(output_dir.glob(f"{prefix.name}-*.png"))
    if not rendered:
        return None
    try:
        rendered[0].replace(page_path)
    except OSError:
        return None
    for stale in rendered[1:]:
        try:
            stale.unlink()
        except OSError:
            pass
    return page_path


def attach_rendered_statement_images(folder: Path, items: list[ReviewItem]) -> None:
    """Attach cropped PDF-rendered statement images when a source PDF is available."""

    pdf_path = find_paper_pdf(folder)
    if pdf_path is None:
        return
    locations = parse_paper_text_statement_locations(folder)
    if not locations:
        return

    location_by_key = {str(location["key"]): location for location in locations}
    next_on_same_page: dict[str, dict[str, Any]] = {}
    for index, location in enumerate(locations):
        for later in locations[index + 1 :]:
            if later.get("page") == location.get("page"):
                next_on_same_page[str(location["key"])] = later
                break
            if int(later.get("page") or 0) > int(location.get("page") or 0):
                break

    digest = _file_sha256(pdf_path) or statement_digest(str(pdf_path))
    output_dir = folder / ".review_traces" / PAPER_RENDERED_STATEMENT_DIR
    output_dir.mkdir(parents=True, exist_ok=True)
    bbox_cache: dict[int, tuple[float, float, list[dict[str, Any]]]] = {}

    try:
        from PIL import Image
    except Exception:  # noqa: BLE001 - optional runtime rendering dependency
        Image = None  # type: ignore[assignment]

    for item in items:
        keys = paper_statement_candidate_keys(item.name, item.name)
        location = next((location_by_key[key] for key in keys if key in location_by_key), None)
        if location is None:
            continue
        page = int(location.get("page") or 0)
        if page <= 0:
            continue
        key = str(location["key"])
        crop_path = output_dir / f"{key}-{digest[:12]}.png"
        if crop_path.exists():
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, crop_path)
            continue
        page_png = _render_pdf_page_to_png(pdf_path, page, output_dir, digest)
        if page_png is None:
            continue
        if Image is None:
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
            continue
        if page not in bbox_cache:
            bbox_cache[page] = _parse_pdf_bbox_words(_run_pdftotext_bbox(pdf_path, page))
        page_width, page_height, words = bbox_cache[page]
        if not page_width or not page_height:
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
            continue
        top_y = _find_statement_start_y(
            words, str(location.get("kind") or ""), str(location.get("number") or "")
        )
        if top_y is None:
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
            continue
        next_location = next_on_same_page.get(key)
        bottom_y = page_height - 48.0
        if next_location is not None:
            next_top = _find_statement_start_y(
                words,
                str(next_location.get("kind") or ""),
                str(next_location.get("number") or ""),
            )
            if next_top is not None and next_top > top_y + 20.0:
                bottom_y = next_top - 10.0
        bottom_y = _find_statement_stop_y(words, top_y, bottom_y)
        try:
            with Image.open(page_png) as image:
                scale_x = image.width / page_width
                scale_y = image.height / page_height
                left = max(0, int(54.0 * scale_x))
                upper = max(0, int((top_y - 14.0) * scale_y))
                right = min(image.width, int((page_width - 54.0) * scale_x))
                lower = min(image.height, int((bottom_y + 4.0) * scale_y))
                if lower <= upper + 20 or right <= left + 20:
                    item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
                    continue
                cropped = image.crop((left, upper, right, lower))
                cropped.save(crop_path)
        except OSError:
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
            continue
        item.paper_statement_image_url = paper_rendered_statement_url(folder.name, crop_path)


def paper_statement_candidate_keys(name: str, full_name: str) -> list[str]:
    """Return paper-statement keys likely to correspond to a Lean declaration."""

    raw_candidates = [
        full_name,
        name,
        name.split(".")[-1],
        full_name.split(".")[-1],
        _normalize_name_key(full_name),
        _normalize_name_key(name),
    ]
    for base in [name, full_name.split(".")[-1]]:
        for kind in ("definition", "theorem", "lemma", "proposition", "corollary", "claim", "remark"):
            match = re.search(rf"(?:^|_){kind}([A-Za-z]?\d+(?:_\d+)*)", base, flags=re.IGNORECASE)
            if match:
                raw_candidates.append(f"{kind}{match.group(1).lower()}")
                raw_candidates.append(f"{kind}_{match.group(1).lower()}")
    out: list[str] = []
    for candidate in raw_candidates:
        if not candidate:
            continue
        for variant in {candidate, _normalize_name_key(candidate), candidate.lower(), _normalize_name_key(candidate).lower()}:
            if variant and variant not in out:
                out.append(variant)
    return out


def _safe_slice_id(value: str) -> str:
    """Normalize a dashboard slice identifier for local filtering."""

    cleaned = re.sub(r"[^A-Za-z0-9_.-]+", "-", value.strip()).strip("-")
    return cleaned or "all"


def collect_export_names(lines: list[str], start: int) -> tuple[list[str], int] | None:
    """Collect names from a Lean `export Foo (...)` block."""

    match = EXPORT_OPEN_RE.match(lines[start])
    if not match:
        return None
    chunks = [match.group("rest")]
    i = start
    while i < len(lines):
        if ")" in chunks[-1]:
            break
        i += 1
        if i >= len(lines):
            return None
        chunks.append(lines[i])
    text = "\n".join(chunks)
    before_close = text.split(")", 1)[0]
    names = EXPORT_NAME_RE.findall(before_close)
    return names, i + 1


def load_review_slice_payload(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, Any]:
    """Load paper-local review-surface metadata from status.json."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_review_slice_payload(folder)
    status_path = folder / DEFAULT_PAPER_STATUS_FILE
    if _dashboard_is_file(status_path):
        status_payload = _dashboard_json_payload(status_path) or {}
        if isinstance(status_payload, dict):
            review_surface = status_payload.get("review_surface")
            if isinstance(review_surface, dict):
                payload: dict[str, Any] = {"schema": REVIEW_SURFACE_SCHEMA}
                include_names = review_surface.get("include_names")
                slices = review_surface.get("slices")
                assumption_names = review_surface.get("assumption_names")
                auxiliary_names = review_surface.get("auxiliary_names")
                quarantined_auxiliary_names = review_surface.get(
                    "quarantined_auxiliary_names"
                )
                source_definition_names = review_surface.get("source_definition_names")
                proposition_spec_proofs = review_surface.get("proposition_spec_proofs")
                source_component_statement_routes = review_surface.get(
                    "source_component_statement_routes"
                )
                source_file = review_surface.get("source_file")
                human_source_file = review_surface.get("human_source_file")
                proof_file = review_surface.get("proof_file")
                proof_module = review_surface.get("proof_module")
                assumption_source_file = review_surface.get("assumption_source_file")
                assumption_policy = review_surface.get("assumption_policy")
                paper_coverage_required = review_surface.get("paper_coverage_required")
                if isinstance(source_file, str) and source_file.strip():
                    payload["source_file"] = source_file
                if isinstance(human_source_file, str) and human_source_file.strip():
                    payload["human_source_file"] = human_source_file
                if isinstance(proof_file, str) and proof_file.strip():
                    payload["proof_file"] = proof_file
                if isinstance(proof_module, str) and proof_module.strip():
                    payload["proof_module"] = proof_module
                if isinstance(include_names, list):
                    payload["include_names"] = include_names
                if isinstance(slices, list):
                    payload["slices"] = slices
                if isinstance(assumption_names, list):
                    payload["assumption_names"] = assumption_names
                if isinstance(auxiliary_names, list):
                    payload["auxiliary_names"] = auxiliary_names
                if isinstance(quarantined_auxiliary_names, list):
                    payload["quarantined_auxiliary_names"] = (
                        quarantined_auxiliary_names
                    )
                if isinstance(source_definition_names, list):
                    payload["source_definition_names"] = source_definition_names
                if isinstance(proposition_spec_proofs, dict):
                    payload["proposition_spec_proofs"] = proposition_spec_proofs
                if isinstance(source_component_statement_routes, list):
                    payload["source_component_statement_routes"] = (
                        source_component_statement_routes
                    )
                if isinstance(assumption_source_file, str) and assumption_source_file.strip():
                    payload["assumption_source_file"] = assumption_source_file
                if isinstance(assumption_policy, str):
                    payload["assumption_policy"] = assumption_policy
                if isinstance(paper_coverage_required, (bool, str)):
                    payload["paper_coverage_required"] = paper_coverage_required
                if (
                    "include_names" in payload
                    or "slices" in payload
                    or "assumption_names" in payload
                    or "auxiliary_names" in payload
                    or "quarantined_auxiliary_names" in payload
                    or "source_definition_names" in payload
                    or "proposition_spec_proofs" in payload
                    or "source_component_statement_routes" in payload
                    or "source_file" in payload
                    or "human_source_file" in payload
                    or "proof_file" in payload
                    or "proof_module" in payload
                    or "assumption_source_file" in payload
                    or "assumption_policy" in payload
                    or "paper_coverage_required" in payload
                ):
                    return payload

    return {}


def review_slice_rules(folder: Path) -> list[dict[str, Any]]:
    """Return validated slice rules for a paper folder."""

    payload = load_review_slice_payload(folder)
    raw_slices = payload.get("slices", [])
    if not isinstance(raw_slices, list):
        return []
    out: list[dict[str, Any]] = []
    for index, raw_slice in enumerate(raw_slices, start=1):
        if not isinstance(raw_slice, dict):
            continue
        title = str(raw_slice.get("title") or raw_slice.get("id") or f"Slice {index}").strip()
        if not title:
            title = f"Slice {index}"
        rule = dict(raw_slice)
        rule["id"] = _safe_slice_id(str(raw_slice.get("id") or title))
        rule["title"] = title
        out.append(rule)
    return out


def review_filter_names(folder: Path) -> set[str] | None:
    """Return an optional paper-local whitelist for human-review rows."""

    payload = load_review_slice_payload(folder)
    names = payload.get("include_names")
    if not isinstance(names, list):
        return None
    out = {str(name).strip() for name in names if str(name).strip()}
    return out if out else None


def review_assumption_names(folder: Path) -> set[str]:
    """Return explicit paper-assumption declarations from status.json."""

    payload = load_review_slice_payload(folder)
    names = payload.get("assumption_names")
    if not isinstance(names, list):
        return set()
    return {str(name).strip() for name in names if str(name).strip()}


def review_auxiliary_names(folder: Path) -> set[str]:
    """Return proof-facing declarations intentionally excluded from statement review."""

    payload = load_review_slice_payload(folder)
    names = payload.get("auxiliary_names")
    if not isinstance(names, list):
        return set()
    return {str(name).strip() for name in names if str(name).strip()}


def review_quarantined_auxiliary_names(folder: Path) -> set[str]:
    """Return auxiliary proof rows barred from paper-claim review credit."""

    payload = load_review_slice_payload(folder)
    names = payload.get("quarantined_auxiliary_names")
    if not isinstance(names, list):
        return set()
    return {str(name).strip() for name in names if str(name).strip()}


def quarantined_support_review_items(folder: Path) -> dict[str, ReviewItem]:
    """Return exact cached support rows without exposing them as paper claims."""

    return QUARANTINED_SUPPORT_REVIEW_ITEM_CACHE.get(str(folder.resolve()), {})


def review_source_definition_names(folder: Path) -> set[str]:
    """Return reviewed Prop definitions explicitly classified as source definitions."""

    payload = load_review_slice_payload(folder)
    names = payload.get("source_definition_names")
    if not isinstance(names, list):
        return set()
    return {str(name).strip() for name in names if str(name).strip()}


def review_proposition_spec_proofs(folder: Path) -> dict[str, str]:
    """Return explicit Prop-spec to proof-row routing from status.json."""

    payload = load_review_slice_payload(folder)
    raw = payload.get("proposition_spec_proofs")
    if not isinstance(raw, dict):
        return {}
    return {
        str(spec).strip(): str(proof).strip()
        for spec, proof in raw.items()
        if str(spec).strip() and str(proof).strip()
    }


def _configured_proposition_spec_proof_declaration(
    specification: ReviewItem,
) -> str:
    """Resolve one configured proof name relative to its exact Spec namespace.

    ``status.json`` deliberately permits concise proof names because the
    specification card already fixes the namespace.  The resulting full name
    is nevertheless an exact declaration coordinate: no global short-name
    lookup or spelling heuristic is used for Lean-Meta proof credit.
    """

    proof_name = str(specification.proposition_spec_proof or "").strip()
    if not proof_name:
        return ""
    if "." in proof_name:
        return proof_name
    specification_name = str(specification.full_name or "").strip()
    if "." not in specification_name:
        return ""
    return specification_name.rsplit(".", 1)[0] + "." + proof_name


def attach_current_lean_semantic_contract_results(
    folder: Path,
    interface_path: Path,
    items: list[ReviewItem],
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider,
) -> None:
    """Attach artifact-pinned Lean verdicts to configured Spec/proof rows.

    Declaration names only identify the requested endpoints. Lean compares the
    elaborated propositions and walks the paper-local dependency graph; Python
    does not recreate either semantic operation.
    """

    source_contract_routes: dict[str, tuple[str, str, str]] = {}
    source_map = paper_statement_map_payload(folder)
    if isinstance(source_map, Mapping) and typed_route_validation_required(source_map):
        route_set = EvidenceRouteSet.from_source_map(
            source_map,
        )
        for route in route_set.result_routes():
            if route.evidence_mode in {"proves", "definitionally_realizes"}:
                source_contract_routes[route.spec_declaration] = (
                    route.spec_declaration,
                    route.evidence_declaration,
                    route.evidence_mode,
                )

    requested: list[tuple[ReviewItem, tuple[str, str, str]]] = []
    for specification in items:
        route = source_contract_routes.get(str(specification.full_name or ""))
        if route is None:
            if specification.proposition_spec_role != "proof_routed":
                continue
            proof_full_name = _configured_proposition_spec_proof_declaration(
                specification
            )
            if not specification.full_name or not proof_full_name:
                continue
            route = (specification.full_name, proof_full_name, "proves")
        requested.append((specification, route))

    if not requested:
        return

    import_module = review_proof_module(folder, interface_path)
    paper_modules = paper_owned_module_names_in_import_closure(
        ROOT,
        folder,
        import_module,
        provider=build_input_provider,
    )
    try:
        matches = run_lean_semantic_contract_matches(
            ROOT,
            import_module,
            [route for _specification, route in requested],
            build_input_provider=build_input_provider,
        )
        transparency = run_lean_semantic_contract_transparency_checks(
            ROOT,
            import_module,
            sorted({route[0] for _specification, route in requested}),
            paper_modules,
            build_input_provider=build_input_provider,
        )
    except Exception:  # noqa: BLE001 - unavailable Lean evidence fails closed.
        matches = {}
        transparency = {}

    for specification, route in requested:
        match_result = matches.get(route)
        specification.semantic_contract_lean_match_verified = (
            match_result if isinstance(match_result, bool) else None
        )
        transparency_result = transparency.get(route[0])
        passes = (
            transparency_result.get("passes")
            if isinstance(transparency_result, dict)
            else None
        )
        specification.semantic_contract_lean_transparency_verified = (
            passes if isinstance(passes, bool) else None
        )


def cached_semantic_contract_results_need_refresh(
    folder: Path,
    items: Iterable[ReviewItem],
) -> bool:
    """Return whether a selected exact source contract lacks a Lean verdict."""

    source_map = paper_statement_map_payload(folder)
    specs: set[str] = set()
    if isinstance(source_map, Mapping) and typed_route_validation_required(source_map):
        route_set = EvidenceRouteSet.from_source_map(
            source_map,
        )
        specs = {
            route.spec_declaration
            for route in route_set.result_routes()
            if route.evidence_mode in {"proves", "definitionally_realizes"}
        }
    return any(
        str(item.full_name or "").strip() in specs
        and (
            not isinstance(item.semantic_contract_lean_match_verified, bool)
            or not isinstance(
                item.semantic_contract_lean_transparency_verified, bool
            )
        )
        for item in items
    )


def is_assumption_item_name(name: str) -> bool:
    """Heuristic for assumption declarations before status.json has been filled."""

    return bool(ASSUMPTION_DECL_NAME_RE.search(name))


def review_row_matches_slice_rule(
    name: str,
    line_number: int,
    rule: Mapping[str, Any],
) -> bool:
    """Check one typed row coordinate against a configured review slice."""

    names = rule.get("names")
    if isinstance(names, list) and name in {str(value) for value in names}:
        return True

    prefixes = rule.get("prefixes")
    if isinstance(prefixes, list) and any(
        name.startswith(str(prefix)) for prefix in prefixes
    ):
        return True

    pattern = rule.get("name_regex")
    if isinstance(pattern, str) and pattern.strip():
        try:
            if re.search(pattern, name):
                return True
        except re.error:
            pass

    line_start = rule.get("line_start")
    line_end = rule.get("line_end")
    if isinstance(line_start, int) or isinstance(line_end, int):
        start_ok = not isinstance(line_start, int) or line_number >= line_start
        end_ok = not isinstance(line_end, int) or line_number <= line_end
        if start_ok and end_ok:
            return True

    return False


def review_item_matches_slice_rule(item: ReviewItem, rule: dict[str, Any]) -> bool:
    """Check whether a legacy parsed item belongs to one review slice rule."""

    return review_row_matches_slice_rule(item.name, item.line_number, rule)


def _review_name_survives_surface_filter(
    name: str,
    include_names: set[str] | None,
    assumption_names: set[str],
    auxiliary_names: set[str],
) -> bool:
    """Apply the name filter shared by review selection and Lean elaboration."""

    if (
        include_names is not None
        and name not in include_names
        and name not in assumption_names
    ):
        return False
    return name not in auxiliary_names


def apply_review_slices(folder: Path, items: list[ReviewItem]) -> list[ReviewItem]:
    """Attach paper-local review slice labels to parsed dashboard rows."""

    include_names = review_filter_names(folder)
    assumption_names = review_assumption_names(folder)
    auxiliary_names = review_auxiliary_names(folder)
    items = [
        item
        for item in items
        if _review_name_survives_surface_filter(
            item.name, include_names, assumption_names, auxiliary_names
        )
    ]

    rules = review_slice_rules(folder)
    if not rules:
        for item in items:
            item.slice_id = "all"
            item.slice_title = "All statements"
        return items

    payload = load_review_slice_payload(folder)
    fallback_title = str(payload.get("fallback_title") or "Other statements")
    fallback_id = _safe_slice_id(str(payload.get("fallback_id") or "other"))
    for item in items:
        for rule in rules:
            if review_item_matches_slice_rule(item, rule):
                item.slice_id = str(rule["id"])
                item.slice_title = str(rule["title"])
                break
        else:
            item.slice_id = fallback_id
            item.slice_title = fallback_title
    return items


def summarize_review_slices(items: list[ReviewItem]) -> list[dict[str, Any]]:
    """Summarize slices present in a paper's current dashboard rows."""

    order: list[str] = []
    by_id: dict[str, dict[str, Any]] = {}
    for item in items:
        slice_id = item.slice_id or "all"
        if slice_id not in by_id:
            order.append(slice_id)
            by_id[slice_id] = {
                "id": slice_id,
                "title": item.slice_title or slice_id,
                "count": 0,
                "first_line": item.line_number or None,
                "last_line": item.line_number or None,
            }
        row = by_id[slice_id]
        row["count"] += 1
        if item.line_number:
            first_line = row.get("first_line")
            last_line = row.get("last_line")
            row["first_line"] = item.line_number if first_line is None else min(first_line, item.line_number)
            row["last_line"] = item.line_number if last_line is None else max(last_line, item.line_number)
    return [by_id[slice_id] for slice_id in order]


def filter_items_by_slice(
    items: list[ReviewItem], paper_name: str, slice_filter: str | None
) -> list[ReviewItem]:
    """Filter dashboard rows to one slice id or paper-qualified slice id."""

    if not slice_filter:
        return items
    normalized = slice_filter.strip()
    if not normalized:
        return items
    paper_part = ""
    slice_part = normalized
    if "::" in normalized:
        paper_part, slice_part = normalized.split("::", 1)
        if paper_part and paper_part != paper_name:
            return []
    slice_part = _safe_slice_id(slice_part)
    filtered = [item for item in items if item.slice_id == slice_part]
    if filtered:
        return filtered
    if items and {item.slice_id for item in items} == {"all"}:
        return items
    return filtered


def attach_review_slices_to_mappings(
    folder: Path,
    rows: Iterable[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """Attach navigation slices to an already selected typed claim surface.

    Current-protocol presentation never needs to manufacture a parser-shaped
    ``ReviewItem`` merely to assign navigation labels. Claim selection already
    belongs to ``PreparedReviewSurface``; legacy include/auxiliary filters must
    not run again here. The same slice predicate remains shared with historical
    parsed rows above.
    """

    selected: list[dict[str, Any]] = []
    for raw in rows:
        row = dict(raw)
        name = str(row.get("name") or "").strip()
        if not name:
            raise ValueError("typed prepared claim has no navigation name")
        selected.append(row)

    rules = review_slice_rules(folder)
    if not rules:
        for row in selected:
            row["slice_id"] = "all"
            row["slice_title"] = "All statements"
        return selected

    payload = load_review_slice_payload(folder)
    fallback_title = str(payload.get("fallback_title") or "Other statements")
    fallback_id = _safe_slice_id(str(payload.get("fallback_id") or "other"))
    for row in selected:
        name = str(row.get("name") or "").strip()
        line_number = row.get("line_number")
        line = line_number if isinstance(line_number, int) else 0
        for rule in rules:
            if review_row_matches_slice_rule(name, line, rule):
                row["slice_id"] = str(rule["id"])
                row["slice_title"] = str(rule["title"])
                break
        else:
            row["slice_id"] = fallback_id
            row["slice_title"] = fallback_title
    return selected


def filter_mapping_rows_by_slice(
    rows: list[dict[str, Any]],
    paper_name: str,
    slice_filter: str | None,
) -> list[dict[str, Any]]:
    """Apply the historical slice-selector semantics to typed rows."""

    if not slice_filter or not slice_filter.strip():
        return rows
    normalized = slice_filter.strip()
    paper_part = ""
    slice_part = normalized
    if "::" in normalized:
        paper_part, slice_part = normalized.split("::", 1)
        if paper_part and paper_part != paper_name:
            return []
    slice_part = _safe_slice_id(slice_part)
    filtered = [row for row in rows if row.get("slice_id") == slice_part]
    if filtered:
        return filtered
    if rows and {str(row.get("slice_id") or "") for row in rows} == {"all"}:
        return rows
    return filtered


def summarize_mapping_review_slices(
    rows: Iterable[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """Summarize typed review slices without a legacy row conversion."""

    order: list[str] = []
    by_id: dict[str, dict[str, Any]] = {}
    for row in rows:
        slice_id = str(row.get("slice_id") or "all")
        line_number = row.get("line_number")
        line = line_number if isinstance(line_number, int) else 0
        if slice_id not in by_id:
            order.append(slice_id)
            by_id[slice_id] = {
                "id": slice_id,
                "title": str(row.get("slice_title") or slice_id),
                "count": 0,
                "first_line": line or None,
                "last_line": line or None,
            }
        summary = by_id[slice_id]
        summary["count"] += 1
        if line:
            first_line = summary.get("first_line")
            last_line = summary.get("last_line")
            summary["first_line"] = (
                line if first_line is None else min(first_line, line)
            )
            summary["last_line"] = (
                line if last_line is None else max(last_line, line)
            )
    return [by_id[slice_id] for slice_id in order]


def _is_interface_decl_boundary(line: str) -> bool:
    """Return true when a line starts a new top-level interface item."""

    stripped = line.strip()
    if not stripped:
        return True
    return bool(
        COMMENT_START_RE.match(line)
        or DECL_RE.match(line)
        or NAMESPACE_OPEN_RE.match(stripped)
        or SECTION_OPEN_RE.match(stripped)
        or END_SCOPE_RE.match(stripped)
    )


def _declaration_assignment_index(
    line: str,
    *,
    delimiters: list[str],
    block_comment_depth: int,
    in_string: bool,
    top_level_let: int | None,
) -> tuple[int | None, list[str], int, bool, int | None]:
    """Find an outer declaration `:=` while preserving theorem `let` types.

    Lean theorem types can contain local `let` bindings, including an inner
    `:=`.  This lightweight lexer intentionally recognizes only enough Lean
    surface syntax to distinguish those from the declaration assignment.  A
    top-level `let` is carried as its layout indentation rather than a Boolean:
    its body starts at that indentation on a later line, after which a later
    `:=` is the declaration assignment.  A failure to recognize an outer
    assignment is a cache miss, never a source binding to a truncated theorem
    statement.
    """

    matching = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⟪": "⟫", "⟦": "⟧"}
    leading_indent = len(line) - len(line.lstrip())
    if (
        top_level_let is not None
        and line.strip()
        and leading_indent <= top_level_let
        and not line.lstrip().startswith("let ")
    ):
        # Layout marks the end of a multiline `let` binding.  The following
        # source proposition may itself contain the declaration's outer `:=`.
        top_level_let = None
    i = 0
    while i < len(line):
        if block_comment_depth:
            if line.startswith("/-", i):
                block_comment_depth += 1
                i += 2
                continue
            if line.startswith("-/", i):
                block_comment_depth -= 1
                i += 2
                continue
            i += 1
            continue
        if in_string:
            if line[i] == "\\":
                i += 2
                continue
            if line[i] == '"':
                in_string = False
            i += 1
            continue
        if line.startswith("--", i):
            break
        if line.startswith("/-", i):
            block_comment_depth += 1
            i += 2
            continue
        if line[i] == '"':
            in_string = True
            i += 1
            continue
        character = line[i]
        if character in matching:
            delimiters.append(matching[character])
            i += 1
            continue
        if delimiters and character == delimiters[-1]:
            delimiters.pop()
            i += 1
            continue
        if not delimiters and character == ";":
            top_level_let = None
            i += 1
            continue
        if not delimiters and line.startswith(":=", i) and not top_level_let:
            return i, delimiters, block_comment_depth, in_string, top_level_let
        if not delimiters and (character.isalpha() or character == "_"):
            end = i + 1
            while end < len(line) and (line[end].isalnum() or line[end] in "_'"):
                end += 1
            if line[i:end] == "let":
                top_level_let = leading_indent
            i = end
            continue
        i += 1
    return None, delimiters, block_comment_depth, in_string, top_level_let


def collect_review_decl_text(lines: list[str], start: int, kind: str) -> tuple[str, int] | None:
    """Collect the text shown for one paper-interface declaration."""

    sig_lines: list[str] = []
    delimiters: list[str] = []
    block_comment_depth = 0
    in_string = False
    top_level_let: int | None = None
    j = start
    while j < len(lines):
        sig_line = lines[j]
        sig_lines.append(sig_line)
        if kind in {"axiom", "structure", "class", "inductive"} and (
            j + 1 >= len(lines) or _is_interface_decl_boundary(lines[j + 1])
        ):
            return "\n".join(sig_lines).strip(), j + 1
        (
            assignment_index,
            delimiters,
            block_comment_depth,
            in_string,
            top_level_let,
        ) = _declaration_assignment_index(
            sig_line,
            delimiters=delimiters,
            block_comment_depth=block_comment_depth,
            in_string=in_string,
            top_level_let=top_level_let,
        )
        if assignment_index is not None:
            if kind in {"def", "abbrev", "instance"}:
                while j + 1 < len(lines) and not _is_interface_decl_boundary(lines[j + 1]):
                    j += 1
                    sig_lines.append(lines[j])
            else:
                sig_lines[-1] = sig_line[:assignment_index]
            return "\n".join(sig_lines).strip(), j + 1
        j += 1
    return None


def parse_review_source_declarations(
    source_path: Path,
    *,
    source_text: str | None = None,
) -> list[tuple[str, str, str, str, str | None, int, Path]]:
    """Parse dashboard-visible Lean declarations from one source file."""

    if source_text is None and not _dashboard_is_file(source_path):
        return []
    lines = (
        source_text if source_text is not None else _dashboard_read_text(source_path)
    ).splitlines()
    parsed: list[tuple[str, str, str, str, str | None, int, Path]] = []
    namespace_stack: list[str] = []
    section_depth = 0
    pending_comment: str | None = None
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        namespace_match = NAMESPACE_OPEN_RE.match(stripped)
        if namespace_match:
            namespace_stack.extend(namespace_match.group(1).split("."))
            i += 1
            continue

        section_match = SECTION_OPEN_RE.match(stripped)
        if section_match:
            section_depth += 1
            i += 1
            continue

        end_match = END_SCOPE_RE.match(stripped)
        if end_match:
            end_name = end_match.group(1)
            if end_name and namespace_stack and namespace_stack[-1] == end_name:
                namespace_stack.pop()
            elif end_name:
                if section_depth > 0:
                    section_depth -= 1
            else:
                if section_depth > 0:
                    section_depth -= 1
                elif namespace_stack:
                    namespace_stack.pop()
            i += 1
            continue

        if COMMENT_START_RE.match(line):
            comment, after = parse_block_comment(lines, i)
            if "/-!" in line or line.lstrip().startswith("/-"):
                pending_comment = clean_comment(comment)
            i = after
            continue

        if stripped.startswith("@[") and stripped.endswith("]"):
            i += 1
            continue

        exported = collect_export_names(lines, i)
        if exported is not None:
            names, next_i = exported
            for name in names:
                full_name = ".".join(namespace_stack + [name]) if namespace_stack else name
                parsed.append(
                    (
                        "theorem",
                        name,
                        full_name,
                        f"exported declaration `{full_name}`",
                        pending_comment,
                        i + 1,
                        source_path,
                    )
                )
            pending_comment = None
            i = next_i
            continue

        m = DECL_RE.match(line)
        if m:
            name = m.group("name")
            kind = m.group("kind")
            full_name = ".".join(namespace_stack + [name]) if namespace_stack else name
            collected = collect_review_decl_text(lines, i, kind)
            if collected is not None:
                raw_sig, next_i = collected
                parsed.append((kind, name, full_name, raw_sig, pending_comment, i + 1, source_path))
            else:
                next_i = i + 1
            pending_comment = None
            i = next_i
            continue

        if stripped and not stripped.startswith("--") and not stripped.startswith("/-"):
            pending_comment = None
        i += 1
    return parsed


def parse_interface_items(
    interface_path: Path,
    report_path: Path | None,
    paper_folder: Path | None = None,
    *,
    render_lean_previews: bool = True,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    audit_inputs: DashboardAuditInputs | None = None,
    progress: Callable[[str], None] | None = None,
) -> list[ReviewItem]:
    """Combine declaration signatures and paper statements for one paper folder."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return parse_interface_items(
                interface_path,
                report_path,
                paper_folder,
                render_lean_previews=render_lean_previews,
                build_input_provider=build_input_provider,
                progress=progress,
            )
    owns_build_input_provider = build_input_provider is None
    if build_input_provider is None:
        build_input_provider = RepositoryBuildInputSnapshotProvider(ROOT)
    if paper_folder is None:
        paper_folder = interface_path.parent
    paper_statements = collected_paper_statements(paper_folder, report_path)
    llm_tex_drafts = load_llm_lean_to_tex_drafts(paper_folder)
    include_names = review_filter_names(paper_folder)
    assumption_names = review_assumption_names(paper_folder)
    auxiliary_names = review_auxiliary_names(paper_folder)
    quarantined_auxiliary_names = review_quarantined_auxiliary_names(
        paper_folder
    )
    source_definition_names = review_source_definition_names(paper_folder)
    proposition_spec_proofs = review_proposition_spec_proofs(paper_folder)
    assumption_judgments = load_llm_assumption_judgments(paper_folder)

    parsed = parse_review_source_declarations(interface_path)
    assumption_path = assumption_source_file(paper_folder)
    if (
        assumption_names
        and assumption_path != interface_path
        and _dashboard_is_file(assumption_path)
    ):
        for row in parse_review_source_declarations(assumption_path):
            _kind, name, full_name, _raw_sig, _comment, _line_number, _source_path = row
            if name in assumption_names or full_name in assumption_names or is_assumption_item_name(name):
                parsed.append(row)
    component_navigation_routes = review_source_component_statement_routes(
        paper_folder
    )
    component_statement_routes = resolved_review_source_component_statement_routes(
        paper_folder,
        parsed,
        component_routes=component_navigation_routes,
    )
    direct_statement_routes = resolved_direct_source_statement_routes(
        paper_folder,
        parsed,
    )
    direct_source_item_routes = resolved_direct_source_item_routes(
        paper_folder,
        parsed,
    )

    semantic_parsed = parsed
    if include_names is not None:
        semantic_parsed = [
            row
            for row in parsed
            if _review_name_survives_surface_filter(
                row[1], include_names, assumption_names, auxiliary_names
            )
            or row[1] in quarantined_auxiliary_names
            or row[2] in quarantined_auxiliary_names
        ]

    check_maps: dict[Path, dict[str, str]] = {}
    signature_maps: dict[Path, dict[str, dict[str, Any]]] = {}
    for source_path in sorted({row[6] for row in semantic_parsed}):
        source_module = review_source_module(paper_folder, source_path)
        dependency_modules = paper_owned_module_names_in_import_closure(
            ROOT,
            paper_folder,
            source_module,
            provider=build_input_provider,
        )
        declaration_names = [
            full_name
            for (
                kind,
                _name,
                full_name,
                _raw_sig,
                _comment,
                _line_number,
                row_source,
            ) in semantic_parsed
            if kind in REVIEW_DECL_KINDS and row_source == source_path
        ]
        resume_bindings: dict[str, dict[str, str]] = {}
        duplicate_resume_bindings: set[str] = set()
        for (
            kind,
            _name,
            full_name,
            raw_signature,
            _comment,
            _line_number,
            row_source,
        ) in semantic_parsed:
            if kind not in REVIEW_DECL_KINDS or row_source != source_path:
                continue
            if full_name in duplicate_resume_bindings:
                continue
            if full_name in resume_bindings:
                resume_bindings.pop(full_name, None)
                duplicate_resume_bindings.add(full_name)
                continue
            binding = _manifest_resume_binding(
                paper_folder,
                qualified_declaration=full_name,
                declaration_kind=kind,
                lean_source_declaration=raw_signature,
                source_path=source_path,
            )
            if binding is not None:
                resume_bindings[full_name] = binding
        check_maps[source_path] = (
            run_lean_check_previews(
                paper_folder,
                declaration_names,
                source_file=source_path,
            )
            if render_lean_previews
            else {}
        )
        if not dependency_modules:
            signature_maps[source_path] = {}
            continue
        resume_context = signature_manifest_cache_context(
            ROOT,
            source_module,
            semantic_dependency_modules=dependency_modules,
            build_input_provider=build_input_provider,
        )
        resumed = (
            _prime_manifest_resume_cache(
                paper_folder,
                import_module=source_module,
                semantic_dependency_modules=dependency_modules,
                context=resume_context,
                bindings=resume_bindings,
                progress=progress,
            )
            if isinstance(resume_context, Mapping)
            else set()
        )
        if progress is not None and resumed:
            progress(
                "non-authoritative manifest resume cache reused "
                f"{len(resumed)} declaration(s)"
            )
        if progress is not None:
            progress(
                f"Lean manifest surface {source_module}: "
                f"{len(declaration_names)} declarations started"
            )

        def checkpoint(
            context: Mapping[str, Any],
            completed: Mapping[str, Mapping[str, Any]],
        ) -> None:
            _checkpoint_manifest_resume_cache(
                paper_folder, resume_bindings, context, completed
            )

        def manifest_batch_progress(event: Mapping[str, Any]) -> None:
            if progress is None:
                return
            batch = int(event.get("batch_number") or 0)
            total = int(event.get("batch_total") or 0)
            roots = int(event.get("root_count") or 0)
            status = str(event.get("status") or "unknown")
            message = (
                f"Lean manifest surface {source_module}: "
                f"batch {batch}/{total} {status} ({roots} roots"
            )
            if status == "finished":
                message += (
                    f"; {int(event.get('completed_count') or 0)} complete; "
                    f"{int(event.get('missing_count') or 0)} missing"
                )
            progress(message + ")")

        manifest_progress_kwargs: dict[str, object] = {}
        if progress is not None:
            manifest_progress_kwargs["progress_callback"] = (
                manifest_batch_progress
            )
        signature_maps[source_path] = run_lean_signature_manifests(
            ROOT,
            source_module,
            declaration_names,
            timeout_seconds=300,
            semantic_dependency_modules=dependency_modules,
            build_input_provider=build_input_provider,
            manifest_checkpoint=checkpoint,
            **manifest_progress_kwargs,
        )
        missing_declarations = sorted(
            set(declaration_names) - set(signature_maps[source_path])
        )
        if progress is not None:
            progress(
                f"Lean manifest surface {source_module}: "
                f"{len(signature_maps[source_path])} available, "
                f"{len(missing_declarations)} missing"
            )
        if missing_declarations:
            sample = ", ".join(missing_declarations[:8])
            suffix = "" if len(missing_declarations) <= 8 else ", ..."
            print(
                "review-dashboard: exact Lean signature extraction incomplete "
                f"for {source_module} ({len(missing_declarations)} missing: "
                f"{sample}{suffix})",
                file=sys.stderr,
            )

    signature_manifests: dict[str, dict[str, Any]] = {}
    ambiguous_short_names: set[str] = set()
    for kind, name, full_name, _raw_sig, _comment, _line_number, source_path in parsed:
        if kind not in REVIEW_DECL_KINDS:
            continue
        manifest = signature_maps.get(source_path, {}).get(full_name)
        if manifest is None:
            continue
        signature_manifests[full_name] = manifest
        if name in signature_manifests and signature_manifests[name] is not manifest:
            ambiguous_short_names.add(name)
        else:
            signature_manifests[name] = manifest
    for name in ambiguous_short_names:
        signature_manifests.pop(name, None)
    SIGNATURE_MANIFEST_CACHE[str(paper_folder.resolve())] = signature_manifests
    llm_judgments = load_llm_statement_judgments(
        paper_folder, signature_manifests
    )
    semantic_judgment_index = _semantic_statement_judgment_index(llm_judgments)

    out: list[ReviewItem] = []
    for kind, name, full_name, raw_sig, doc_comment, line_number, source_path in parsed:
        if kind not in REVIEW_DECL_KINDS:
            continue
        check_map = check_maps.get(source_path, {})
        signature_manifest = signature_maps.get(source_path, {}).get(full_name)
        signature_sha256 = str(
            (signature_manifest or {}).get("sha256") or ""
        ).strip()
        check_statement = check_map.get(full_name) or check_map.get(name)
        definition_kinds = {"def", "abbrev", "structure", "class", "inductive"}
        lean_statement = raw_sig if kind in definition_kinds else (
            f"@{full_name} :\n{check_statement}" if check_statement else raw_sig
        )
        paper_text = paper_statement_for_review_row(
            paper_statements,
            component_statement_routes,
            name,
            full_name,
            component_navigation_keys=component_navigation_routes,
            direct_statement_routes=direct_statement_routes,
        )
        comment_text, source_status, source_note = split_source_metadata(doc_comment or "")
        source_item_key = ""
        source_input_bundle_sha256 = ""
        verbatim_source_input = ""
        direct_source_item = direct_source_item_routes.get(full_name)
        if direct_source_item is not None:
            source_item_key, source_item = direct_source_item
            (
                verbatim_source_input,
                source_input_bundle_sha256,
                source_input_error,
            ) = source_semantic_input_bundle(source_item)
            if source_input_error:
                verbatim_source_input = ""
                source_input_bundle_sha256 = ""
                source_note = (
                    f"{source_note}; " if source_note else ""
                ) + f"raw semantic source input unavailable: {source_input_error}"
        if verbatim_source_input:
            # This is the only source text that a v11 semantic judgment may
            # receive.  It is intentionally distinct from the map's readable
            # ``statement`` summary, which remains navigation metadata.
            displayed_paper_statement = verbatim_source_input
            source_status = source_status or "byte-pinned verbatim source input"
        elif paper_text:
            displayed_paper_statement = paper_text
            source_status = source_status or "direct source text"
        else:
            displayed_paper_statement = comment_text
        agent_statement = (
            llm_tex_drafts.get(name)
            or llm_tex_drafts.get(full_name)
            or agent_preview_comment(
                doc_comment,
                lean_statement,
                None if kind in definition_kinds else check_statement,
            )
        )
        _semantic_key, semantic_judgment, semantic_ambiguous = (
            _current_semantic_statement_judgment(
                signature_sha256=signature_sha256,
                lean_statement=lean_statement,
                paper_statement=displayed_paper_statement,
                agent_statement=agent_statement,
                source_input_bundle_sha256=source_input_bundle_sha256,
                judgments=llm_judgments,
                identity_index=semantic_judgment_index,
            )
        )
        judgment = (
            semantic_judgment
            if semantic_judgment is not None
            else {}
            if semantic_ambiguous
            else llm_judgments.get(name) or llm_judgments.get(full_name) or {}
        )
        llm_match_stale = _llm_statement_judgment_is_stale(
            judgment,
            signature_sha256=signature_sha256,
            lean_statement=lean_statement,
            paper_statement=displayed_paper_statement,
            agent_statement=agent_statement,
            source_input_bundle_sha256=source_input_bundle_sha256,
        )
        is_assumption = name in assumption_names or full_name in assumption_names or is_assumption_item_name(name)
        is_proposition_spec = is_proposition_specification_manifest(signature_manifest)
        proposition_spec_proof = (
            proposition_spec_proofs.get(name)
            or proposition_spec_proofs.get(full_name)
            or ""
        )
        if not is_proposition_spec:
            proposition_spec_role = ""
        elif is_assumption:
            proposition_spec_role = "source_assumption"
        elif name in source_definition_names or full_name in source_definition_names:
            proposition_spec_role = "source_definition"
        elif proposition_spec_proof:
            proposition_spec_role = "proof_routed"
        else:
            proposition_spec_role = "unproved_spec"
        assumption_judgment = (
            assumption_judgments.get(name)
            or assumption_judgments.get(full_name)
            or {}
        )
        llm_assumption_stale = False
        if assumption_judgment:
            recorded_lean = assumption_judgment.get("lean_statement_sha256", "")
            recorded_paper = assumption_judgment.get("paper_statement_sha256", "")
            llm_assumption_stale = (
                not recorded_lean
                or not recorded_paper
                or
                (
                    recorded_lean not in lean_statement_digest_candidates(lean_statement, raw_sig)
                )
                or (recorded_paper != statement_digest(displayed_paper_statement))
                or bool(assumption_judgment.get("prompt_version_stale"))
                or bool(assumption_judgment.get("metadata_missing"))
            )
            semantic_parent_receipt = assumption_judgment.get(
                "source_record_semantic_parent_v1"
            )
            if isinstance(semantic_parent_receipt, dict):
                llm_assumption_stale = llm_assumption_stale or (
                    assumption_judgment.get("lean_signature_sha256")
                    != signature_sha256
                    or str(
                        semantic_parent_receipt.get("lean_signature_sha256") or ""
                    ).strip().lower()
                    != signature_sha256
                )
        out.append(
            ReviewItem(
                name=name,
                kind=kind,
                lean_statement=lean_statement,
                paper_statement=displayed_paper_statement,
                agent_statement=agent_statement,
                full_name=full_name,
                interface_source=raw_sig,
                lean_signature_manifest=signature_manifest,
                lean_signature_sha256=signature_sha256,
                source_status=source_status,
                source_note=source_note,
                llm_match_judgment=judgment.get("judgment", ""),
                llm_match_reason=judgment.get("reason", "") or judgment.get("comment", ""),
                llm_match_stale=llm_match_stale,
                llm_match_source=judgment.get("source", ""),
                llm_match_validator=judgment.get("validator", ""),
                llm_match_validator_type=judgment.get("validator_type", ""),
                llm_match_validated_at=judgment.get("validated_at", ""),
                llm_match_lean_statement_sha256=judgment.get("lean_statement_sha256", ""),
                llm_match_lean_signature_sha256=judgment.get("lean_signature_sha256", ""),
                llm_match_paper_statement_sha256=judgment.get("paper_statement_sha256", ""),
                llm_match_tex_statement_sha256=judgment.get("tex_statement_sha256", ""),
                llm_match_resolution=judgment.get("resolution", ""),
                llm_match_boundary_type=judgment.get("boundary_type", ""),
                llm_match_boundary_names=judgment.get("boundary_names") or [],
                llm_match_conditional_premises=judgment.get("conditional_premises") or [],
                llm_match_resolution_reason=judgment.get("resolution_reason", ""),
                llm_match_source_routes=(
                    judgment.get("source_routes")
                    if isinstance(judgment.get("source_routes"), list)
                    else []
                ),
                llm_match_component_target_sha256=(
                    _validated_unique_source_component_target_sha256(judgment)
                ),
                is_assumption=is_assumption,
                is_proposition_spec=is_proposition_spec,
                proposition_spec_role=proposition_spec_role,
                proposition_spec_proof=proposition_spec_proof,
                llm_assumption_judgment=assumption_judgment.get("judgment", ""),
                llm_assumption_reason=assumption_judgment.get("reason", "")
                or assumption_judgment.get("comment", ""),
                llm_assumption_stale=llm_assumption_stale,
                llm_assumption_source=assumption_judgment.get("source", ""),
                llm_assumption_validator=assumption_judgment.get("validator", ""),
                llm_assumption_validator_type=assumption_judgment.get("validator_type", ""),
                llm_assumption_validated_at=assumption_judgment.get("validated_at", ""),
                llm_assumption_lean_statement_sha256=assumption_judgment.get("lean_statement_sha256", ""),
                llm_assumption_paper_statement_sha256=assumption_judgment.get("paper_statement_sha256", ""),
                llm_assumption_premise_judgments=assumption_judgment.get("premise_judgments") or {},
                source_item_key=source_item_key,
                source_input_bundle_sha256=source_input_bundle_sha256,
                verbatim_source_input=verbatim_source_input,
                line_number=line_number,
            )
        )
    attach_current_lean_semantic_contract_results(
        paper_folder,
        interface_path,
        out,
        build_input_provider=build_input_provider,
    )
    support_items: dict[str, ReviewItem] = {}
    for item in out:
        if (
            item.name in quarantined_auxiliary_names
            or item.full_name in quarantined_auxiliary_names
        ):
            support_items[item.name] = item
            if item.full_name:
                support_items[item.full_name] = item
    QUARANTINED_SUPPORT_REVIEW_ITEM_CACHE[
        str(paper_folder.resolve())
    ] = support_items
    result = apply_review_slices(paper_folder, out)
    if (
        owns_build_input_provider
        and not build_input_provider.finalize_unchanged()
    ):
        raise RuntimeError(
            f"repository build inputs changed while extracting {paper_folder.name}"
        )
    return result


def collected_paper_statements(
    paper_folder: Path, report_path: Path | None = None
) -> dict[str, str]:
    """Collect display statements without elaborating any Lean declarations."""

    paper_statements = (
        parse_report_texts(report_path)
        if report_path is not None and _dashboard_is_file(report_path)
        else {}
    )
    source_statements = parse_paper_tex_statements(paper_folder)
    if not source_statements:
        source_statements = parse_paper_text_statements(paper_folder)
    paper_statements.update(source_statements)
    paper_statements.update(parse_paper_statement_map(paper_folder))
    # Preserve the legacy display collection API for callers that inspect raw
    # navigation keys. Extraction and cache rebind do not trust these aliases:
    # they resolve each route to one exact full declaration and exclude the raw
    # navigation keys from ordinary heuristic fallback.
    paper_statements.update(
        {
            row: str(component.get("statement") or "")
            for row, component in review_source_component_statement_routes(
                paper_folder
            ).items()
            if str(component.get("statement") or "").strip()
        }
    )
    return paper_statements


def _statement_rebind_review_rows(
    folder: Path,
) -> list[tuple[str, str, str, str, str | None, int, Path]]:
    """Return every current declaration that can contribute a cached row."""

    parsed = parse_review_source_declarations(review_source_file(folder))
    assumption_names = review_assumption_names(folder)
    assumption_path = assumption_source_file(folder)
    if assumption_names and assumption_path != review_source_file(folder):
        if _dashboard_is_file(assumption_path):
            parsed.extend(parse_review_source_declarations(assumption_path))
    return parsed


def cached_direct_source_route_statements_are_current(
    folder: Path, items: Iterable[ReviewItem]
) -> bool:
    """Whether cached direct-route displays equal current map statements.

    This is a lightweight cache invariant.  It does not inspect semantic
    sidecars or Lean names heuristically: it compares each cached row's exact
    qualified declaration against the source map's explicit direct route.
    Rows without one such route retain their ordinary display policy.
    """

    parsed = _statement_rebind_review_rows(folder)
    direct_routes = resolved_direct_source_statement_routes(folder, parsed)
    direct_source_items = resolved_direct_source_item_routes(folder, parsed)
    by_name: dict[str, list[tuple[str, str, str, str, str | None, int, Path]]] = {}
    for row in parsed:
        if row[0] in REVIEW_DECL_KINDS:
            by_name.setdefault(row[1], []).append(row)
    for item in items:
        candidates = [
            row
            for row in by_name.get(item.name, [])
            if row[0] == item.kind and row[3] == item.interface_source
        ]
        if len(candidates) != 1:
            # The ordinary cache rebind validates this carrier identity before
            # it can use a row.  Do not guess a direct route here.
            continue
        full_name = candidates[0][2]
        source_item_route = direct_source_items.get(full_name)
        if source_item_route is not None:
            source_key, source_item = source_item_route
            source_input, source_identity, error = source_semantic_input_bundle(source_item)
            if (
                error
                or item.source_item_key != source_key
                or item.source_input_bundle_sha256 != source_identity
                or item.verbatim_source_input != source_input
                or item.paper_statement != source_input
            ):
                return False
            continue
        expected = direct_routes.get(full_name)
        if expected and normalize_statement(item.paper_statement) != expected:
            return False
    return True


def rebind_cached_report_statements(
    folder: Path, items: list[ReviewItem]
) -> bool:
    """Refresh report-derived display text without repeating Lean Meta work.

    A report can change a dashboard row's human-facing source text while the
    review-surface Lean declarations are byte-for-byte unchanged.  Reparse the
    lightweight declaration comments and report/source text, then preserve the
    cached elaborated manifests only when every cached row still identifies the
    same declaration.  Any source mismatch falls back to the normal full
    extraction path.
    """

    report_path = paper_relative_file(
        folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md"
    )
    paper_statements = collected_paper_statements(folder, report_path)
    parsed = _statement_rebind_review_rows(folder)
    component_navigation_routes = review_source_component_statement_routes(folder)
    component_statement_routes = resolved_review_source_component_statement_routes(
        folder,
        parsed,
        component_routes=component_navigation_routes,
    )
    direct_statement_routes = resolved_direct_source_statement_routes(folder, parsed)
    direct_source_item_routes = resolved_direct_source_item_routes(folder, parsed)

    by_name: dict[str, list[tuple[str, str, str, str, str | None, int, Path]]] = {}
    for row in parsed:
        kind, name, _full_name, _raw_sig, _comment, _line_number, _source_path = row
        if kind in REVIEW_DECL_KINDS:
            by_name.setdefault(name, []).append(row)

    for item in items:
        candidates = [
            row
            for row in by_name.get(item.name, [])
            if row[0] == item.kind and row[3] == item.interface_source
        ]
        if len(candidates) != 1:
            return False
        _kind, name, full_name, _raw_sig, doc_comment, _line_number, _source_path = candidates[0]
        item.full_name = full_name
        paper_text = paper_statement_for_review_row(
            paper_statements,
            component_statement_routes,
            name,
            full_name,
            component_navigation_keys=component_navigation_routes,
            direct_statement_routes=direct_statement_routes,
        )
        comment_text, source_status, source_note = split_source_metadata(doc_comment or "")
        source_item_route = direct_source_item_routes.get(full_name)
        if source_item_route is not None:
            source_key, source_item = source_item_route
            source_input, source_input_identity, source_input_error = (
                source_semantic_input_bundle(source_item)
            )
            item.source_item_key = source_key
            item.verbatim_source_input = "" if source_input_error else source_input
            item.source_input_bundle_sha256 = (
                "" if source_input_error else source_input_identity
            )
        else:
            item.source_item_key = ""
            item.verbatim_source_input = ""
            item.source_input_bundle_sha256 = ""
        if item.verbatim_source_input:
            item.paper_statement = item.verbatim_source_input
            item.source_status = source_status or "byte-pinned verbatim source input"
            item.source_note = source_note
        elif paper_text:
            item.paper_statement = paper_text
            item.source_status = source_status or "direct source text"
            item.source_note = source_note
        else:
            item.paper_statement = comment_text
            item.source_status = source_status
            item.source_note = source_note
    return True


def rebind_cached_review_status(
    folder: Path, items: list[ReviewItem]
) -> list[ReviewItem] | None:
    """Refresh status-derived row labels and proposition classifications."""

    rebound = apply_review_slices(folder, items)
    if len(rebound) != len(items):
        return None
    interface_path = review_source_file(folder)
    parsed = parse_review_source_declarations(interface_path)
    assumption_names = review_assumption_names(folder)
    assumption_path = assumption_source_file(folder)
    if (
        assumption_names
        and assumption_path.resolve() != interface_path.resolve()
        and _dashboard_is_file(assumption_path)
    ):
        for row in parse_review_source_declarations(assumption_path):
            _kind, name, full_name, _raw_sig, _comment, _line_number, _source_path = row
            if (
                name in assumption_names
                or full_name in assumption_names
                or is_assumption_item_name(name)
            ):
                parsed.append(row)
    source_definition_names = review_source_definition_names(folder)
    proposition_spec_proofs = review_proposition_spec_proofs(folder)
    for item in rebound:
        candidates = [
            row
            for row in parsed
            if row[0] == item.kind
            and row[1] == item.name
            and (not item.interface_source or row[3] == item.interface_source)
        ]
        if item.full_name:
            candidates = [row for row in candidates if row[2] == item.full_name]
        elif len(candidates) > 1 and item.line_number:
            line_candidates = [row for row in candidates if row[5] == item.line_number]
            if len(line_candidates) == 1:
                candidates = line_candidates
        if len(candidates) != 1:
            return None
        item.full_name = candidates[0][2]
        item.interface_source = candidates[0][3]
        prior_proof = item.proposition_spec_proof
        proof = (
            proposition_spec_proofs.get(item.name)
            or proposition_spec_proofs.get(item.full_name)
            or ""
        )
        item.proposition_spec_proof = proof
        if proof != prior_proof:
            item.semantic_contract_lean_match_verified = None
            item.semantic_contract_lean_transparency_verified = None
        if not item.is_proposition_spec:
            item.proposition_spec_role = ""
        elif item.is_assumption:
            item.proposition_spec_role = "source_assumption"
        elif (
            item.name in source_definition_names
            or item.full_name in source_definition_names
        ):
            item.proposition_spec_role = "source_definition"
        elif proof:
            item.proposition_spec_role = "proof_routed"
        else:
            item.proposition_spec_role = "unproved_spec"
    return rebound


def cached_rows_match_current_extraction_surface(
    folder: Path, items: list[ReviewItem]
) -> bool:
    """Check cached row selection against current Lean sources without Lean."""

    interface_path = review_source_file(folder)
    include_names = review_filter_names(folder)
    assumption_names = review_assumption_names(folder)
    auxiliary_names = review_auxiliary_names(folder)
    parsed = parse_review_source_declarations(interface_path)
    assumption_path = assumption_source_file(folder)
    if (
        assumption_names
        and assumption_path.resolve() != interface_path.resolve()
        and _dashboard_is_file(assumption_path)
    ):
        for row in parse_review_source_declarations(assumption_path):
            _kind, name, full_name, _raw_sig, _comment, _line_number, _source_path = row
            if (
                name in assumption_names
                or full_name in assumption_names
                or is_assumption_item_name(name)
            ):
                parsed.append(row)
    expected = sorted(
        (kind, name, raw_sig)
        for kind, name, _full_name, raw_sig, _comment, _line_number, _source_path in parsed
        if kind in REVIEW_DECL_KINDS
        and _review_name_survives_surface_filter(
            name, include_names, assumption_names, auxiliary_names
        )
    )
    recorded = sorted(
        (item.kind, item.name, item.interface_source) for item in items
    )
    return recorded == expected


def paper_title(folder: Path) -> str:
    readme = folder / "README.md"
    if readme.exists():
        for line in readme.read_text(encoding="utf-8").splitlines():
            if line.startswith("# "):
                return line[2:].strip()
    return folder.name


def iter_paper_folders(paper_filter: str | None = None) -> list[Path]:
    """Return paper directories that have a human-review Lean surface."""

    folders: list[Path] = []
    active = active_paper_names() if paper_filter is None else set()
    for folder in sorted(PAPERS_DIR.iterdir()):
        if not folder.is_dir():
            continue
        if folder.name == "TEMPLATE":
            continue
        if paper_filter and folder.name != paper_filter:
            continue
        if folder.name in active:
            continue
        if find_review_source_file(folder) is None:
            continue
        folders.append(folder)
    return folders


def paper_review_log_file(paper: str | Path) -> Path:
    """Return the default per-paper trace file path for a paper."""

    folder = PAPERS_DIR / str(paper)
    if not folder.exists() or not folder.is_dir():
        raise ValueError(f"unknown paper folder: {paper}")
    if find_review_source_file(folder) is None:
        raise ValueError(f"no human review Lean surface for paper: {paper}")
    return folder / ".review_traces" / DEFAULT_PAPER_LOG_FILE


def paper_library_prerequisite_log_file(paper: str | Path) -> Path:
    """Return the local human-review trace for library prerequisite cards."""

    folder = PAPERS_DIR / str(paper)
    if not folder.exists() or not folder.is_dir():
        raise ValueError(f"unknown paper folder: {paper}")
    if find_review_source_file(folder) is None:
        raise ValueError(f"no human review Lean surface for paper: {paper}")
    return folder / ".review_traces" / DEFAULT_LIBRARY_PREREQUISITE_LOG_FILE


def paper_interface_cache_file(paper: str | Path) -> Path:
    """Return the local sidecar file for cached declaration and statement rows."""

    folder = PAPERS_DIR / str(paper)
    if not folder.exists() or not folder.is_dir():
        raise ValueError(f"unknown paper folder: {paper}")
    if find_review_source_file(folder) is None:
        raise ValueError(f"no human review Lean surface for paper: {paper}")
    return folder / ".review_traces" / DEFAULT_PAPER_INTERFACE_CACHE_FILE


def manifest_resume_cache_directory(paper: str | Path) -> Path:
    """Return the ignored, non-authoritative manifest-resume cache directory.

    These files make a resource-bounded dashboard refresh resumable. They are
    intentionally separate from the authenticated manifest authority and may
    never supply audit evidence by themselves.
    """

    folder = Path(paper)
    if not folder.is_absolute():
        # Callers commonly already hold a repository-relative paper directory
        # such as ``papers/Foo``. Prefixing it with ``PAPERS_DIR`` created the
        # separate ignored tree ``papers/papers/Foo`` and discarded reusable
        # manifest work. Normalize the path coordinate once, independently of
        # a paper's declaration or audit content.
        folder = (
            ROOT / folder
            if folder.parts and folder.parts[0] == PAPERS_DIR.name
            else PAPERS_DIR / folder
        )
    return folder / ".review_traces" / MANIFEST_RESUME_CACHE_DIRNAME


def _manifest_resume_binding(
    folder: Path,
    *,
    qualified_declaration: str,
    declaration_kind: str,
    lean_source_declaration: str,
    source_path: Path,
) -> dict[str, str] | None:
    """Bind a resume record to exact current source text, not a row name alone."""

    try:
        resolved_source_path = source_path.resolve()
        source_file = resolved_source_path.relative_to(folder.resolve()).as_posix()
    except (OSError, ValueError):
        return None
    qualified = qualified_declaration.strip()
    source = lean_source_declaration.strip()
    kind = declaration_kind.strip()
    source_file_sha256 = _file_sha256(resolved_source_path)
    if (
        not qualified
        or not source
        or kind not in REVIEW_DECL_KINDS
        or not source_file
        or not re.fullmatch(r"[0-9a-f]{64}", source_file_sha256)
    ):
        return None
    return {
        "qualified_declaration": qualified,
        "source_file": source_file,
        "source_file_sha256": source_file_sha256,
        "declaration_kind": kind,
        "lean_source_declaration": source,
    }


def _manifest_resume_binding_digest(binding: Mapping[str, Any]) -> str:
    """Return the stable path key for one exact source declaration binding."""

    required = {
        "qualified_declaration",
        "source_file",
        "source_file_sha256",
        "declaration_kind",
        "lean_source_declaration",
    }
    if set(binding) != required or any(
        not isinstance(binding.get(field), str) or not binding[field].strip()
        for field in required
    ):
        return ""
    return hashlib.sha256(
        json.dumps(
            dict(binding), ensure_ascii=True, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
    ).hexdigest()


def _manifest_resume_cache_entry_path(
    folder: Path,
    context_sha256: str,
    binding: Mapping[str, Any],
) -> Path | None:
    """Return one deterministic local path for a context/source-bound receipt."""

    if not re.fullmatch(r"[0-9a-f]{64}", context_sha256):
        return None
    binding_sha256 = _manifest_resume_binding_digest(binding)
    if not binding_sha256:
        return None
    return (
        manifest_resume_cache_directory(folder)
        / context_sha256
        / f"{binding_sha256}.json"
    )


def _atomic_write_manifest_resume_payload(path: Path, payload: Mapping[str, Any]) -> None:
    """Atomically write one local optimization record.

    Per-declaration paths avoid a shared mutable index, so an interruption can
    lose at most the row currently being written and concurrent refreshes do
    not overwrite unrelated completed rows.
    """

    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(payload, ensure_ascii=True, sort_keys=True) + "\n"
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            handle.write(encoded)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        # Persist the directory entry as well as the file contents when the
        # host supports directory fsync. A crash can otherwise lose a just
        # checkpointed rename even though the payload was flushed.
        try:
            directory_descriptor = os.open(
                path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
            )
            try:
                os.fsync(directory_descriptor)
            finally:
                os.close(directory_descriptor)
        except OSError:
            pass
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def checkpoint_manifest_resume_records(
    folder: Path,
    bindings: Mapping[str, Mapping[str, str]],
    context: Mapping[str, Any],
    manifests: Mapping[str, Mapping[str, Any]],
) -> set[str]:
    """Persist exact completed manifests as non-authoritative resume records.

    The caller must already have obtained the manifests from a successful Lean
    extraction.  This helper deliberately records neither audit credit nor a
    claim that the caller's source route is current: consumers still require
    the separately tracked authority/carrier pair, an independently rebuilt
    source binding, and the exact compiled context before the record can seed
    a cache.  Returning only successfully checkpointed coordinates lets a
    producer report the optimization without making its raw result depend on
    persistence.
    """

    context_sha256 = signature_manifest_cache_context_sha256(context)
    if not re.fullmatch(r"[0-9a-f]{64}", context_sha256):
        return set()
    checkpointed: set[str] = set()
    for qualified, raw_manifest in manifests.items():
        binding = bindings.get(qualified)
        if not isinstance(binding, Mapping) or not isinstance(raw_manifest, Mapping):
            continue
        path = _manifest_resume_cache_entry_path(folder, context_sha256, binding)
        manifest = dict(raw_manifest)
        signature = str(manifest.get("sha256") or "").strip().lower()
        if (
            path is None
            or not re.fullmatch(r"[0-9a-f]{64}", signature)
            or signature_manifest_digest(manifest) != signature
        ):
            continue
        payload = {
            "schema": MANIFEST_RESUME_CACHE_SCHEMA,
            "paper": folder.name,
            "non_authoritative_resume_cache": MANIFEST_RESUME_CACHE_NON_AUTHORITATIVE,
            "manifest_cache_context_sha256": context_sha256,
            "binding": dict(binding),
            "manifest": manifest,
        }
        try:
            _atomic_write_manifest_resume_payload(path, payload)
        except OSError:
            # The current extraction still has an in-memory receipt. A failed
            # checkpoint merely means a later process must ask Lean again.
            continue
        checkpointed.add(qualified)
    return checkpointed


def _checkpoint_manifest_resume_cache(
    folder: Path,
    bindings: Mapping[str, Mapping[str, str]],
    context: Mapping[str, Any],
    manifests: Mapping[str, Mapping[str, Any]],
) -> None:
    """Compatibility wrapper for existing interrupted-refresh call sites."""

    checkpoint_manifest_resume_records(folder, bindings, context, manifests)


def _load_manifest_resume_cache_entry(
    path: Path,
    *,
    paper: str,
    context_sha256: str,
    binding: Mapping[str, str],
) -> dict[str, Any] | None:
    """Load one cache record only when it binds this exact context and source."""

    try:
        if path.stat().st_size > 256 * 1024 * 1024:
            return None
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return None
    if (
        not isinstance(payload, dict)
        or set(payload)
        != {
            "schema",
            "paper",
            "non_authoritative_resume_cache",
            "manifest_cache_context_sha256",
            "binding",
            "manifest",
        }
        or payload.get("schema") != MANIFEST_RESUME_CACHE_SCHEMA
        or payload.get("paper") != paper
        or payload.get("non_authoritative_resume_cache") is not True
        or payload.get("manifest_cache_context_sha256") != context_sha256
        or payload.get("binding") != dict(binding)
        or not isinstance(payload.get("manifest"), Mapping)
    ):
        return None
    manifest = dict(payload["manifest"])
    signature = str(manifest.get("sha256") or "").strip().lower()
    if (
        not re.fullmatch(r"[0-9a-f]{64}", signature)
        or signature_manifest_digest(manifest) != signature
    ):
        return None
    return manifest


def current_manifest_resume_records(
    folder: Path,
    *,
    context: Mapping[str, Any],
    bindings: Mapping[str, Mapping[str, str]],
) -> dict[str, dict[str, Any]]:
    """Load source-bound local resume records without granting them credit.

    The returned records remain ignored optimization data.  Consumers must pass
    them through exact-context authority/carrier attestation before reuse.
    Keeping the loader separate lets source-record scans use their frozen
    current source bindings instead of consulting a stale prior raw audit.
    """

    context_sha256 = signature_manifest_cache_context_sha256(context)
    if not re.fullmatch(r"[0-9a-f]{64}", context_sha256):
        return {}
    recovered: dict[str, dict[str, Any]] = {}
    for qualified, binding in bindings.items():
        path = _manifest_resume_cache_entry_path(folder, context_sha256, binding)
        if path is None:
            continue
        manifest = _load_manifest_resume_cache_entry(
            path,
            paper=folder.name,
            context_sha256=context_sha256,
            binding=binding,
        )
        if manifest is not None:
            recovered[qualified] = {
                "manifest_cache_context_sha256": context_sha256,
                "binding": dict(binding),
                "manifest": manifest,
            }
    return recovered


def _prime_manifest_resume_cache(
    folder: Path,
    *,
    import_module: str,
    semantic_dependency_modules: tuple[str, ...],
    context: Mapping[str, Any],
    bindings: Mapping[str, Mapping[str, str]],
    progress: Callable[[str], None] | None = None,
) -> set[str]:
    """Seed checkpointed rows only after carrier-backed current validation.

    The journal is not evidence and never supplies a Lean graph for cache
    authority.  It contributes only the exact source binding parsed when its
    completed row was checkpointed.  The authenticated carrier supplies the
    manifest after the record's Lean payload, current source binding, exact
    compiled context, and current reached artifacts all agree.  If that exact
    fast path has no accepted row, a tracked carrier from an earlier context
    may be retained only after every candidate receives a fresh compact Lean
    revalidation.  A miss remains a miss; this helper never treats the journal
    as source or audit evidence.
    """

    recovered = current_manifest_resume_records(
        folder, context=context, bindings=bindings
    )
    if not recovered:
        return set()
    try:
        accepted, exact_diagnostics = prime_exact_context_attested_resume_manifests(
            root=ROOT,
            paper_dir=folder,
            import_module=import_module,
            semantic_dependency_modules=semantic_dependency_modules,
            current_context=context,
            current_bindings=bindings,
            resume_records=recovered,
        )
    except Exception:  # noqa: BLE001 - journal reuse must remain a cache miss.
        return set()
    if isinstance(accepted, Mapping) and accepted:
        return set(accepted)

    # A swapped or otherwise unattested journal payload is not an
    # interrupted current computation.  Do not turn that integrity failure
    # into authority for a recovery revalidation merely because the source
    # coordinate still exists.
    rejected_by_reason = (
        exact_diagnostics.get("rejected_by_reason", {})
        if isinstance(exact_diagnostics, Mapping)
        else {}
    )
    if (
        isinstance(exact_diagnostics, Mapping)
        and exact_diagnostics.get("store_status") == "resume_payload_not_attested"
    ) or (
        isinstance(rejected_by_reason, Mapping)
        and bool(rejected_by_reason.get("resume_payload_not_attested"))
    ):
        return set()

    try:
        recovered_accepted, recovery_diagnostics = (
            prime_attested_resume_manifests_with_current_revalidation(
                root=ROOT,
                paper_dir=folder,
                import_module=import_module,
                semantic_dependency_modules=semantic_dependency_modules,
                current_context=context,
                current_bindings=bindings,
                resume_records=recovered,
            )
        )
    except Exception:  # noqa: BLE001 - journal reuse must remain a cache miss.
        return set()
    accepted_names = (
        set(recovered_accepted)
        if isinstance(recovered_accepted, Mapping)
        else set()
    )
    requested_revalidations = int(
        recovery_diagnostics.get("item_revalidation_requested_count") or 0
    ) if isinstance(recovery_diagnostics, Mapping) else 0
    if progress is not None and requested_revalidations:
        progress(
            "manifest resume recovery compact-Lean revalidated "
            f"{requested_revalidations} checkpointed declaration(s); "
            f"reused {len(accepted_names)}"
        )
    return accepted_names


_LEAN_EXTRACTION_REVIEW_SURFACE_FIELDS = {
    "source_file",
    "human_source_file",
    "assumption_source_file",
    "include_names",
    "assumption_names",
    "auxiliary_names",
}


def _review_surface_static_status_digest(status_source: str) -> str:
    """Hash only status fields that determine extracted review rows.

    LLM sidecar policies, paper status labels, and validation receipts are
    rebound dynamically.  Re-extracting elaborated Lean signatures after any
    of those changes is costly and contributes no additional soundness.
    Review-surface selection and source-file fields remain cache inputs.
    """

    try:
        status_payload = json.loads(status_source)
    except json.JSONDecodeError:
        return statement_digest(status_source)
    if not isinstance(status_payload, dict):
        return statement_digest(status_source)
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return statement_digest("")
    static_surface = {
        key: review_surface.get(key)
        for key in sorted(_LEAN_EXTRACTION_REVIEW_SURFACE_FIELDS)
        if key in review_surface
    }
    return statement_digest(
        json.dumps(static_surface, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    )


def _review_surface_display_status_digest(status_source: str) -> str:
    """Hash status metadata that changes paper-facing statement display."""

    try:
        status_payload = json.loads(status_source)
    except json.JSONDecodeError:
        return statement_digest("")
    if not isinstance(status_payload, dict):
        return statement_digest("")
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return statement_digest("")
    component_routes = review_surface.get("source_component_statement_routes")
    display_identity: dict[str, Any] = {
        "source_component_statement_routes": component_routes
    }
    if isinstance(component_routes, list) and component_routes:
        # Bump only caches that use row-specific component display.  This
        # activates the no-Lean rebind for caches written before qualified,
        # ambiguity-checked component precedence was enforced.
        display_identity["source_component_display_binding_schema"] = (
            SOURCE_COMPONENT_DISPLAY_BINDING_SCHEMA
        )
    return statement_digest(
        json.dumps(
            display_identity,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        )
    )


def _review_surface_rebind_status_digest(status_source: str) -> str:
    """Hash all review metadata that does not require Lean extraction."""

    try:
        status_payload = json.loads(status_source)
    except json.JSONDecodeError:
        return statement_digest("")
    if not isinstance(status_payload, dict):
        return statement_digest("")
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return statement_digest("")
    rebind_surface = {
        key: value
        for key, value in review_surface.items()
        if key not in _LEAN_EXTRACTION_REVIEW_SURFACE_FIELDS
    }
    return statement_digest(
        json.dumps(
            rebind_surface,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        )
    )


def _cache_nonlean_source_hashes(folder: Path) -> dict[str, str]:
    """Hash the direct human-review surface without walking Lean imports.

    This is deliberately limited to the files that determine what the browser
    shows.  It is sufficient to reload an already extracted interactive cache;
    it is *not* a substitute for the current Lean-closure validation used by
    cache refreshes and frozen closeout checks.
    """
    interface_path = review_source_file(folder)
    report_path = paper_relative_file(
        folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md"
    )
    tex_path = find_paper_tex_source(folder)
    text_path = find_paper_text(folder)
    pdf_path = find_paper_pdf(folder)
    statement_map_path = folder / PAPER_STATEMENT_MAP_FILE
    status_path = folder / DEFAULT_PAPER_STATUS_FILE

    interface_source = (
        _dashboard_read_text(interface_path) if _dashboard_is_file(interface_path) else ""
    )
    report_source = (
        _dashboard_read_text(report_path) if _dashboard_is_file(report_path) else ""
    )
    tex_source = _dashboard_read_text(tex_path) if tex_path is not None else ""
    text_source = _dashboard_read_text(text_path) if text_path is not None else ""
    statement_map_source = (
        _dashboard_read_text(statement_map_path)
        if _dashboard_is_file(statement_map_path)
        else ""
    )
    status_source = (
        _dashboard_read_text(status_path) if _dashboard_is_file(status_path) else ""
    )
    return {
        "review_source_file": interface_path.name,
        "interface_sha256": statement_digest(interface_source),
        "report_sha256": statement_digest(report_source),
        "tex_sha256": statement_digest(tex_source),
        "text_sha256": statement_digest(text_source),
        "pdf_sha256": _file_sha256(pdf_path),
        "paper_statement_map_sha256": statement_digest(statement_map_source),
        "review_surface_static_sha256": _review_surface_static_status_digest(
            status_source
        ),
        "review_surface_display_sha256": _review_surface_display_status_digest(
            status_source
        ),
        "review_surface_rebind_sha256": _review_surface_rebind_status_digest(
            status_source
        ),
    }


def _cache_source_hashes(
    folder: Path,
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[str, str]:
    """Hash the direct review surface and its current Lean import closure."""

    owns_build_input_provider = build_input_provider is None
    if build_input_provider is None:
        # Cache writers already pass the run's Lean-authored provider.  A
        # standalone cache reader must use the same authority instead of
        # silently switching repository_build_input_snapshot to its legacy
        # Python import-parser compatibility path.
        build_input_provider = RepositoryBuildInputSnapshotProvider(ROOT)
    interface_path = review_source_file(folder)
    hashes = _cache_nonlean_source_hashes(folder)
    selected_modules = {review_source_module(folder, interface_path)}
    assumption_path = assumption_source_file(folder)
    if _selected_assumption_source_is_required(
        folder, interface_path, assumption_path
    ):
        selected_modules.add(review_source_module(folder, assumption_path))
    lean_source_closure = {
        module: repository_build_input_snapshot(
            ROOT,
            module,
            provider=build_input_provider,
        )
        or ""
        for module in sorted(selected_modules)
    }

    hashes["lean_source_closure_sha256"] = statement_digest(
        json.dumps(
            lean_source_closure,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        )
    )
    if (
        owns_build_input_provider
        and not build_input_provider.finalize_unchanged()
    ):
        raise RuntimeError(
            f"Lean source-closure inputs changed while hashing {folder.name}"
        )
    return hashes


def _selected_assumption_source_is_required(
    folder: Path, interface_path: Path, assumption_path: Path
) -> bool:
    """Whether the separate assumption module contributes a selected row."""

    assumption_names = review_assumption_names(folder)
    if (
        not assumption_names
        or assumption_path.resolve() == interface_path.resolve()
        or not _dashboard_is_file(assumption_path)
    ):
        return False
    include_names = review_filter_names(folder)
    auxiliary_names = review_auxiliary_names(folder)
    for row in parse_review_source_declarations(assumption_path):
        _kind, name, full_name, _raw_sig, _comment, _line_number, _source_path = row
        if (
            name not in assumption_names
            and full_name not in assumption_names
            and not is_assumption_item_name(name)
        ):
            continue
        if _review_name_survives_surface_filter(
            name, include_names, assumption_names, auxiliary_names
        ):
            return True
    return False


def _current_review_signature_contexts(
    folder: Path,
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider,
) -> dict[str, Any] | None:
    """Build review modules and return the cache context for their manifests."""

    folder_root = folder.resolve()
    interface_path = review_source_file(folder)
    source_paths = {interface_path}
    assumption_path = assumption_source_file(folder)
    if _selected_assumption_source_is_required(
        folder, interface_path, assumption_path
    ):
        source_paths.add(assumption_path)
    contexts: dict[str, Any] = {}
    for source_path in sorted(source_paths):
        source_module = review_source_module(folder, source_path)
        dependency_modules = paper_owned_module_names_in_import_closure(
            ROOT,
            folder,
            source_module,
            provider=build_input_provider,
        )
        if not dependency_modules:
            return None
        context = signature_manifest_cache_context(
            ROOT,
            source_module,
            semantic_dependency_modules=dependency_modules,
            build_input_provider=build_input_provider,
        )
        if context is None:
            return None
        try:
            cache_key = str(source_path.resolve().relative_to(folder_root))
        except ValueError:
            return None
        contexts[cache_key] = context
    return contexts


def current_review_signature_contexts(
    folder: Path,
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, Any] | None:
    """Build review modules from one immutable shared fallback snapshot."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return current_review_signature_contexts(
                folder,
                build_input_provider=build_input_provider,
            )
    owns_build_input_provider = build_input_provider is None
    if build_input_provider is None:
        build_input_provider = RepositoryBuildInputSnapshotProvider(ROOT)
    contexts = _current_review_signature_contexts(
        folder,
        build_input_provider=build_input_provider,
    )
    if (
        owns_build_input_provider
        and not build_input_provider.finalize_unchanged()
    ):
        return None
    return contexts


def review_signature_manifest_authority_binding(
    *,
    qualified_declaration: str,
    source_file: str,
    lean_source_declaration: str,
    line_number: int,
    declaration_kind: str,
    elaborated_signature_sha256: str,
    elaborated_proposition_graph_sha256: str,
) -> dict[str, Any]:
    """Return the exact dashboard producer binding for one manifest root."""

    return {
        "qualified_declaration": qualified_declaration,
        "source_file": source_file,
        "lean_source_declaration": lean_source_declaration,
        "line_number": line_number,
        "declaration_kind": declaration_kind,
        "elaborated_signature_sha256": elaborated_signature_sha256,
        "elaborated_proposition_graph_sha256": (
            elaborated_proposition_graph_sha256
        ),
    }


def _review_signature_manifest_declarations(
    folder: Path,
) -> tuple[dict[str, tuple[str, str, int, Path]], set[str]]:
    """Parse the exact dashboard sources into unique qualified coordinates."""

    declarations: dict[str, tuple[str, str, int, Path]] = {}
    duplicates: set[str] = set()
    source_paths = {review_source_file(folder)}
    assumptions = assumption_source_file(folder)
    if _dashboard_is_file(assumptions):
        source_paths.add(assumptions)
    for source_path in sorted(source_paths):
        for (
            kind,
            _name,
            full_name,
            raw_signature,
            _comment,
            line_number,
            parsed_source_path,
        ) in parse_review_source_declarations(source_path):
            if full_name in duplicates:
                continue
            if full_name in declarations:
                declarations.pop(full_name, None)
                duplicates.add(full_name)
                continue
            declarations[full_name] = (
                kind,
                raw_signature,
                line_number,
                parsed_source_path,
            )
    return declarations, duplicates


def current_review_signature_manifest_source_coordinates(
    folder: Path,
) -> tuple[dict[str, dict[str, object]], set[str]]:
    """Return exact current selected review declarations for authority reuse.

    The qualified name is only a join coordinate.  Each returned value binds
    the current parser's exact declaration text, source-relative path, kind,
    and line number.  The tracked manifest authority independently pins the
    same coordinate together with Lean-derived identities; ambiguous routes
    are intentionally omitted and must be extracted again.
    """

    interface_path = review_source_file(folder)
    parsed = parse_review_source_declarations(interface_path)
    include_names = review_filter_names(folder)
    assumption_names = review_assumption_names(folder)
    auxiliary_names = review_auxiliary_names(folder)
    assumptions = assumption_source_file(folder)
    if (
        assumption_names
        and assumptions != interface_path
        and _dashboard_is_file(assumptions)
    ):
        for row in parse_review_source_declarations(assumptions):
            _kind, name, full_name, _raw, _comment, _line, _source = row
            if (
                name in assumption_names
                or full_name in assumption_names
                or is_assumption_item_name(name)
            ):
                parsed.append(row)

    coordinates: dict[str, dict[str, object]] = {}
    duplicates: set[str] = set()
    folder_root = folder.resolve()
    for kind, name, full_name, raw_signature, _comment, line_number, source_path in parsed:
        if (
            kind not in REVIEW_DECL_KINDS
            or not _review_name_survives_surface_filter(
                name, include_names, assumption_names, auxiliary_names
            )
        ):
            continue
        if full_name in duplicates:
            continue
        if full_name in coordinates:
            coordinates.pop(full_name, None)
            duplicates.add(full_name)
            continue
        try:
            source_file = source_path.resolve().relative_to(folder_root).as_posix()
        except (OSError, ValueError):
            duplicates.add(full_name)
            continue
        coordinates[full_name] = {
            "source_file": source_file,
            "lean_source_declaration": raw_signature,
            "line_number": line_number,
            "declaration_kind": kind,
        }
    return coordinates, duplicates


def current_review_signature_manifest_bindings(
    folder: Path,
    validated_configured_review_rows: Iterable[Mapping[str, Any]],
    *,
    semantic_reuse_authority: CurrentSemanticReuseAuthority | None = None,
) -> dict[str, dict[str, Any]]:
    """Project independently validated raw rows onto exact dashboard sources.

    Qualified declaration names are lookup coordinates only.  Cache admission
    remains bound to exact source bytes, the Lean-owned signature/dependency/
    proposition-graph identities, and the separately current compiled context.
    Ambiguous or stale coordinates are omitted and therefore receive fresh Lean
    extraction rather than cache credit.
    """

    declarations, declaration_duplicates = (
        _review_signature_manifest_declarations(folder)
    )
    rows_by_qualified: dict[str, Mapping[str, Any]] = {}
    row_duplicates: set[str] = set()
    for raw_row in validated_configured_review_rows:
        if not isinstance(raw_row, Mapping):
            continue
        qualified = str(raw_row.get("qualified_declaration") or "").strip()
        if not qualified or qualified in row_duplicates:
            continue
        if qualified in rows_by_qualified:
            rows_by_qualified.pop(qualified, None)
            row_duplicates.add(qualified)
            continue
        rows_by_qualified[qualified] = raw_row

    root = ROOT.resolve()
    folder_root = folder.resolve()
    bindings: dict[str, dict[str, Any]] = {}
    for qualified, raw_row in sorted(rows_by_qualified.items()):
        if qualified in declaration_duplicates:
            continue
        declaration = declarations.get(qualified)
        if declaration is None:
            continue
        kind, raw_signature, line_number, source_path = declaration
        source_file = str(raw_row.get("source_file") or "").strip()
        source_sha256 = str(raw_row.get("source_sha256") or "").strip().lower()
        signature_sha256 = str(
            raw_row.get("elaborated_signature_sha256") or ""
        ).strip().lower()
        dependency_sha256 = str(
            raw_row.get("semantic_dependency_sha256") or ""
        ).strip().lower()
        proposition_graph_sha256 = (
            configured_review_row_proposition_graph_sha256(raw_row)
        )
        try:
            recorded_source = Path(source_file)
            if recorded_source.is_absolute():
                continue
            recorded_source = (root / recorded_source).resolve()
            recorded_source.relative_to(root)
            context_key = source_path.resolve().relative_to(folder_root).as_posix()
            exact_source = _dashboard_read_bytes(source_path)
        except (OSError, RuntimeError, ValueError, DashboardFrozenInputError):
            continue
        current_source_sha256 = hashlib.sha256(exact_source).hexdigest()
        semantic_source_revalidated = bool(
            isinstance(semantic_reuse_authority, CurrentSemanticReuseAuthority)
            and qualified in semantic_reuse_authority.reviewed_declarations
            and any(
                relative
                == source_path.resolve().relative_to(root).as_posix()
                and state == "present"
                and digest == current_source_sha256
                for relative, state, digest in (
                    semantic_reuse_authority.watched_repository_material
                )
            )
        )
        if (
            recorded_source != source_path.resolve()
            or not re.fullmatch(r"[0-9a-f]{64}", source_sha256)
            or (
                current_source_sha256 != source_sha256
                and not semantic_source_revalidated
            )
            or not re.fullmatch(r"[0-9a-f]{64}", signature_sha256)
            or not re.fullmatch(r"[0-9a-f]{64}", dependency_sha256)
            or not re.fullmatch(r"[0-9a-f]{64}", proposition_graph_sha256)
        ):
            continue
        authority_binding = review_signature_manifest_authority_binding(
            qualified_declaration=qualified,
            source_file=context_key,
            lean_source_declaration=raw_signature,
            line_number=line_number,
            declaration_kind=kind,
            elaborated_signature_sha256=signature_sha256,
            elaborated_proposition_graph_sha256=proposition_graph_sha256,
        )
        bindings[qualified] = {
            "authority_binding": authority_binding,
            "elaborated_signature_sha256": signature_sha256,
            "semantic_dependency_sha256": dependency_sha256,
            "elaborated_proposition_graph_sha256": proposition_graph_sha256,
        }
    return bindings


def _prior_review_manifest_reuse_inputs(
    folder: Path,
) -> tuple[
    tuple[Mapping[str, Any], ...],
    tuple[Mapping[str, Any], ...],
    dict[str, dict[str, str]],
] | None:
    """Load independently receipt-checked prior rows and their manifest context.

    This path is available only to an ordinary mutable cache refresh. Frozen
    closeout inputs already supply their transaction-owned current rows through
    ``validated_configured_review_rows`` and must not read an ignored carrier or
    mutable row cache behind that snapshot.
    """

    if _dashboard_audit_inputs() is not None:
        return None
    raw_path = folder / PAPER_AUDIT_DIR / "source_record_audit.json"
    cache_path = paper_interface_cache_file(folder)
    try:
        raw_payload = json.loads(raw_path.read_text(encoding="utf-8"))
        cache_payload = json.loads(cache_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return None
    if not isinstance(raw_payload, dict) or not isinstance(cache_payload, dict):
        return None
    try:
        from scripts.audit_evidence_integrity import (
            source_record_raw_scan_completeness_error,
        )
        from scripts.source_record_integrity import (
            source_record_audit_receipt_error,
        )
        if source_record_audit_receipt_error(
            raw_payload
        ) or source_record_raw_scan_completeness_error(raw_payload):
            return None
    except Exception:  # noqa: BLE001 - prior evidence failure is a cache miss.
        return None

    raw_rows = raw_payload.get("configured_review_rows")
    if (
        raw_payload.get("paper") != folder.name
        or not isinstance(raw_rows, list)
        or raw_payload.get("configured_review_rows_count") != len(raw_rows)
        or raw_payload.get("missing_configured_review_rows") != []
        or any(not isinstance(row, Mapping) for row in raw_rows)
        or cache_payload.get("schema") != PAPER_INTERFACE_CACHE_SCHEMA
        or cache_payload.get("paper") != folder.name
        or not isinstance(cache_payload.get("signature_contexts"), Mapping)
    ):
        return None

    declarations, duplicate_declarations = _review_signature_manifest_declarations(
        folder
    )
    current: dict[str, dict[str, str]] = {}
    for raw_row in raw_rows:
        qualified = str(raw_row.get("qualified_declaration") or "").strip()
        declaration = declarations.get(qualified)
        if not qualified or qualified in duplicate_declarations or declaration is None:
            continue
        _kind, raw_signature, _line_number, source_path = declaration
        try:
            source_file = source_path.resolve().relative_to(ROOT).as_posix()
        except (OSError, ValueError):
            continue
        current[qualified] = {
            "lean_source_declaration": raw_signature,
            "source_file": source_file,
        }
    prior_contexts = tuple(
        context
        for context in cache_payload["signature_contexts"].values()
        if isinstance(context, Mapping)
    )
    return (
        tuple(row for row in raw_rows if isinstance(row, Mapping)),
        prior_contexts,
        current,
    )


def prime_review_signature_manifest_store_from_prior(
    folder: Path,
    signature_contexts: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    """Seed unchanged dashboard roots from authenticated prior evidence."""

    inputs = _prior_review_manifest_reuse_inputs(folder)
    if inputs is None:
        return {
            "schema": 1,
            "paper": folder.name,
            "requested_count": 0,
            "candidate_count": 0,
            "seeded_count": 0,
            "seeded_declarations": [],
            "fresh_required_count": 0,
            "rejected_by_reason": {},
            "store_status": "skipped_without_authenticated_prior_rows",
        }
    prior_rows, prior_contexts, current_declarations = inputs
    return prime_authenticated_manifest_store_with_item_revalidation(
        root=ROOT,
        paper_dir=folder,
        authenticated_prior_rows=prior_rows,
        current_declarations=current_declarations,
        prior_contexts=prior_contexts,
        current_contexts=(
            context
            for context in signature_contexts.values()
            if isinstance(context, Mapping)
        ),
    )[1]


def _unavailable_manifest_cache_context(*_args: Any, **_kwargs: Any) -> None:
    """Forbid a closeout cache prime from widening its supplied contexts."""

    return None


def prime_review_signature_manifest_store(
    folder: Path,
    signature_contexts: Mapping[str, Mapping[str, Any]],
    *,
    allow_migration_write: bool = True,
    validated_configured_review_rows: Iterable[Mapping[str, Any]] | None = None,
    semantic_reuse_authority: CurrentSemanticReuseAuthority | None = None,
) -> dict[str, Any]:
    """Seed exact-context roots from current source or closeout bindings.

    Current source bindings are reconstructed only when a tracked authority
    carries that producer format.  Current raw source-record rows remain an
    additional stronger source when available.  Neither path permits
    changed-context item revalidation here: misses reach the ordinary fresh
    manifest extractor, while journal compatibility is handled separately by
    exact authority/carrier attestation.
    """

    # Strict closeout is read-only. The compatibility flag remains part of the
    # public dashboard API but never authorizes a migration or write here.
    _ = allow_migration_write
    configured_rows = (
        list(validated_configured_review_rows)
        if validated_configured_review_rows is not None
        else None
    )
    # A standalone dashboard has no transaction-owned source-record rows from
    # which to establish an independent current request.  Do not even inspect
    # the paper's review surface or authenticated store in that case: the
    # ignored/local cache must remain an ordinary fresh-extraction miss.
    if configured_rows is None:
        return {
            "schema": 1,
            "paper": folder.name,
            "candidate_count": 0,
            "context_count": 0,
            "accepted_context_count": 0,
            "context_provider_call_count": 0,
            "seeded_count": 0,
            "seeded_declarations": [],
            "fresh_required_count": 0,
            "rejected_by_reason": {},
            "store_status": "skipped_without_independent_current_bindings",
            "source_binding_count": 0,
            "source_binding_duplicates": [],
            "source_binding_store_status": "not_requested",
            "binding_conflicts": [],
            "configured_review_row_count": 0,
            "current_declaration_binding_count": 0,
        }
    source_coordinates, source_duplicates = (
        current_review_signature_manifest_source_coordinates(folder)
    )
    source_bindings, source_binding_diagnostics = (
        current_source_bound_manifest_bindings(
            paper_dir=folder,
            current_declarations={
                qualified: coordinate
                for qualified, coordinate in source_coordinates.items()
                if qualified not in source_duplicates
            },
        )
    )
    raw_bindings: dict[str, dict[str, Any]] = {}
    raw_bindings = current_review_signature_manifest_bindings(
        folder,
        configured_rows,
        semantic_reuse_authority=semantic_reuse_authority,
    )
    semantic_revalidated_bindings: dict[str, dict[str, str]] = {}
    if isinstance(semantic_reuse_authority, CurrentSemanticReuseAuthority):
        configured_names = {
            str(row.get("qualified_declaration") or "").strip()
            for row in configured_rows
            if isinstance(row, Mapping)
        }
        if (
            configured_names
            and configured_names
            == set(semantic_reuse_authority.reviewed_declarations)
        ):
            semantic_revalidated_bindings = {
                qualified: {
                    field: str(binding.get(field) or "").strip().lower()
                    for field in (
                        "elaborated_signature_sha256",
                        "semantic_dependency_sha256",
                        "elaborated_proposition_graph_sha256",
                    )
                }
                for qualified, binding in raw_bindings.items()
                if qualified in configured_names
            }
    bindings: dict[str, dict[str, Any]] = {
        qualified: dict(binding)
        for qualified, binding in source_bindings.items()
    }
    binding_conflicts: set[str] = set()
    for qualified, binding in raw_bindings.items():
        existing = bindings.get(qualified)
        if existing is not None and existing != binding:
            bindings.pop(qualified, None)
            binding_conflicts.add(qualified)
        elif qualified not in binding_conflicts:
            bindings[qualified] = dict(binding)
    current_contexts = [
        context
        for context in signature_contexts.values()
        if isinstance(context, Mapping)
    ]
    if bindings:
        _accepted, diagnostics = prime_authenticated_manifest_store(
            root=ROOT,
            paper_dir=folder,
            current_declaration_bindings=bindings,
            current_contexts=current_contexts,
            requested_declarations=bindings,
            semantic_revalidated_bindings=semantic_revalidated_bindings,
            context_provider=_unavailable_manifest_cache_context,
        )
    else:
        diagnostics: dict[str, Any] = {
            "schema": 1,
            "paper": folder.name,
            "candidate_count": 0,
            "context_count": 0,
            "accepted_context_count": 0,
            "context_provider_call_count": 0,
            "seeded_count": 0,
            "seeded_declarations": [],
            "fresh_required_count": 0,
            "rejected_by_reason": {},
            "store_status": "skipped_without_reconstructable_current_bindings",
        }
    diagnostics["source_binding_count"] = len(source_bindings)
    diagnostics["source_binding_duplicates"] = sorted(source_duplicates)
    diagnostics["source_binding_store_status"] = str(
        source_binding_diagnostics.get("store_status") or ""
    )
    diagnostics["binding_conflicts"] = sorted(binding_conflicts)
    diagnostics["configured_review_row_count"] = (
        len(configured_rows) if configured_rows is not None else 0
    )
    diagnostics["current_declaration_binding_count"] = len(bindings)
    fresh_required = int(diagnostics.get("fresh_required_count") or 0)
    if fresh_required:
        raw_rejections = diagnostics.get("rejected_by_reason")
        rejection_summary = ""
        if isinstance(raw_rejections, Mapping) and raw_rejections:
            rejection_summary = "; misses: " + ", ".join(
                f"{reason}={len(declarations)}"
                for reason, declarations in sorted(raw_rejections.items())
                if isinstance(declarations, list)
            )
        print(
            "review-dashboard: authenticated manifest-store prime "
            f"seeded {int(diagnostics.get('seeded_count') or 0)} of "
            f"{int(diagnostics.get('candidate_count') or 0)} candidates; "
            f"{fresh_required} require fresh Lean{rejection_summary}",
            file=sys.stderr,
        )
    return diagnostics


def publish_review_signature_manifest_store(
    folder: Path,
    items: Iterable[ReviewItem],
    signature_contexts: Mapping[str, Mapping[str, Any]],
) -> set[str]:
    """Merge exact manifests from one successful strict dashboard extraction."""

    declarations: dict[str, tuple[str, int, Path]] = {}
    duplicates: set[str] = set()
    source_paths = {review_source_file(folder)}
    assumptions = assumption_source_file(folder)
    if _dashboard_is_file(assumptions):
        source_paths.add(assumptions)
    for source_path in sorted(source_paths):
        for (
            _kind,
            _name,
            full_name,
            raw_signature,
            _comment,
            line_number,
            parsed_source_path,
        ) in parse_review_source_declarations(source_path):
            if full_name in declarations:
                duplicates.add(full_name)
                continue
            declarations[full_name] = (
                raw_signature,
                line_number,
                parsed_source_path,
            )

    candidates: list[dict[str, Any]] = []
    for item in items:
        qualified = str(item.full_name or "").strip()
        declaration = declarations.get(qualified)
        manifest = item.lean_signature_manifest
        if (
            not qualified
            or qualified in duplicates
            or declaration is None
            or not isinstance(manifest, Mapping)
        ):
            continue
        try:
            context_key = str(declaration[2].resolve().relative_to(folder.resolve()))
        except ValueError:
            continue
        context = signature_contexts.get(context_key)
        if not isinstance(context, Mapping):
            continue
        candidates.append(
            {
                "qualified_declaration": qualified,
                "manifest": manifest,
                "context": context,
                "authority_binding": review_signature_manifest_authority_binding(
                    qualified_declaration=qualified,
                    source_file=context_key,
                    lean_source_declaration=declaration[0],
                    line_number=declaration[1],
                    declaration_kind=item.kind,
                    elaborated_signature_sha256=item.lean_signature_sha256,
                    elaborated_proposition_graph_sha256=(
                        elaborated_proposition_graph_sha256(
                            manifest.get("elaborated_proposition_graph")
                        )
                    ),
                ),
            }
        )
    return merge_authenticated_manifest_store(
        paper_dir=folder,
        paper=folder.name,
        candidates=candidates,
    )


def _rebind_cached_v11_source_spec_sidecar(
    folder: Path,
    items: list[ReviewItem],
    *,
    semantic_reuse_authority: CurrentSemanticReuseAuthority | None = None,
) -> None:
    """Project v11 judgments only from an exact-current bounded Lean cache."""

    specification_names = sorted(
        {
            str(item.full_name or "").strip()
            for item in items
            if str(item.full_name or "").strip().endswith("Spec")
        }
    )
    if not specification_names:
        return
    try:
        from scripts.current_closeout import review_surface as packet

        if packet._current_packet_lean_cache(
            folder,
            specification_names,
            semantic_reuse_authority=semantic_reuse_authority,
        ) is None:
            return
    except Exception:  # noqa: BLE001 - unavailable cache fails closed.
        return
    claim_rows = human_review_claim_items(
        folder,
        items,
        semantic_reuse_authority=semantic_reuse_authority,
    )
    bind_current_v11_source_spec_screening(folder, claim_rows)

    _project_v11_claim_rows_onto_review_items(items, claim_rows)


def _project_v11_claim_rows_onto_review_items(
    items: list[ReviewItem],
    claim_rows: list[dict[str, Any]],
) -> None:
    """Project authenticated v11 claim evidence onto strict audit rows.

    Human claim assembly may authenticate a current expanded-Spec target even
    when an older serialized row cache cannot itself be rebound without a
    fresh projection.  Statement and coverage checks consume ``ReviewItem``
    objects, while the dashboard and packet consume claim dictionaries.  Keep
    those two views consistent by copying only the already-authenticated v11
    fields from the latter onto the exact matching declaration.
    """

    claims_by_name = {
        str(row.get("full_name") or "").strip(): row
        for row in claim_rows
        if str(row.get("full_name") or "").strip()
    }
    v11_fields = (
        "llm_match_judgment",
        "llm_match_reason",
        "llm_match_stale",
        "llm_match_source",
        "llm_match_validator",
        "llm_match_validator_type",
        "llm_match_validated_at",
        "llm_match_lean_statement_sha256",
        "llm_match_paper_statement_sha256",
        "llm_match_resolution",
        "llm_match_boundary_type",
        "llm_match_boundary_names",
        "llm_match_conditional_premises",
        "llm_match_resolution_reason",
        "llm_match_source_routes",
    )
    for item in items:
        claim = claims_by_name.get(str(item.full_name or "").strip())
        if not isinstance(claim, Mapping) or claim.get("llm_match_source") != Path(
            V11_RAW_SOURCE_SPEC_SCREENING_FILE
        ).name:
            continue
        for field in v11_fields:
            setattr(item, field, claim.get(field, getattr(item, field)))


def rebind_cached_review_sidecars(
    folder: Path,
    items: list[ReviewItem],
    *,
    semantic_reuse_authority: CurrentSemanticReuseAuthority | None = None,
) -> None:
    """Refresh mutable LLM evidence without re-extracting Lean signatures.

    The cache owns syntactic declarations, elaborated signatures, and source
    statements.  TeX translations and judgment sidecars are independently
    versioned evidence, so they must be reread whenever cached rows are used.
    This keeps cache reuse sound while avoiding a second expensive Lean Meta
    pass merely because an audit sidecar was regenerated.
    """

    drafts = load_llm_lean_to_tex_drafts(folder)
    manifests = {
        item.name: item.lean_signature_manifest
        for item in items
        if isinstance(item.lean_signature_manifest, dict)
    }
    judgments = load_llm_statement_judgments(folder, manifests)
    semantic_judgment_index = _semantic_statement_judgment_index(judgments)
    assumption_judgments = load_llm_assumption_judgments(folder)
    for item in items:
        draft = drafts.get(item.name)
        if draft:
            item.agent_statement = draft

        _semantic_key, semantic_judgment, semantic_ambiguous = (
            _current_semantic_statement_judgment_for_item(
                item,
                judgments,
                identity_index=semantic_judgment_index,
            )
        )
        judgment = (
            semantic_judgment
            if semantic_judgment is not None
            else {}
            if semantic_ambiguous
            else judgments.get(item.name) or {}
        )
        item.llm_match_judgment = str(judgment.get("judgment") or "")
        item.llm_match_reason = str(
            judgment.get("reason") or judgment.get("comment") or ""
        )
        item.llm_match_source = str(judgment.get("source") or "")
        item.llm_match_validator = str(judgment.get("validator") or "")
        item.llm_match_validator_type = str(judgment.get("validator_type") or "")
        item.llm_match_validated_at = str(judgment.get("validated_at") or "")
        item.llm_match_lean_statement_sha256 = str(
            judgment.get("lean_statement_sha256") or ""
        )
        item.llm_match_lean_signature_sha256 = str(
            judgment.get("lean_signature_sha256") or ""
        )
        item.llm_match_paper_statement_sha256 = str(
            judgment.get("paper_statement_sha256") or ""
        )
        item.llm_match_tex_statement_sha256 = str(
            judgment.get("tex_statement_sha256") or ""
        )
        item.llm_match_resolution = _normalize_llm_match_resolution(
            judgment.get("resolution")
        )
        item.llm_match_boundary_type = str(judgment.get("boundary_type") or "")
        item.llm_match_boundary_names = _normalize_string_list(
            judgment.get("boundary_names")
        )
        item.llm_match_conditional_premises = _normalize_string_list(
            judgment.get("conditional_premises")
        )
        item.llm_match_resolution_reason = str(
            judgment.get("resolution_reason") or ""
        )
        item.llm_match_source_routes = (
            judgment.get("source_routes")
            if isinstance(judgment.get("source_routes"), list)
            else []
        )
        item.llm_match_component_target_sha256 = (
            _validated_unique_source_component_target_sha256(judgment)
        )
        item.llm_match_stale = _llm_statement_judgment_is_stale(
            judgment,
            signature_sha256=item.lean_signature_sha256,
            lean_statement=item.lean_statement,
            paper_statement=item.paper_statement,
            agent_statement=item.agent_statement,
            source_input_bundle_sha256=item.source_input_bundle_sha256,
        )

        assumption_judgment = assumption_judgments.get(item.name) or {}
        item.llm_assumption_judgment = str(assumption_judgment.get("judgment") or "")
        item.llm_assumption_reason = str(
            assumption_judgment.get("reason") or assumption_judgment.get("comment") or ""
        )
        item.llm_assumption_source = str(assumption_judgment.get("source") or "")
        item.llm_assumption_validator = str(assumption_judgment.get("validator") or "")
        item.llm_assumption_validator_type = str(
            assumption_judgment.get("validator_type") or ""
        )
        item.llm_assumption_validated_at = str(
            assumption_judgment.get("validated_at") or ""
        )
        item.llm_assumption_lean_statement_sha256 = str(
            assumption_judgment.get("lean_statement_sha256") or ""
        )
        item.llm_assumption_paper_statement_sha256 = str(
            assumption_judgment.get("paper_statement_sha256") or ""
        )
        raw_premise_judgments = assumption_judgment.get("premise_judgments")
        item.llm_assumption_premise_judgments = (
            raw_premise_judgments if isinstance(raw_premise_judgments, dict) else {}
        )
        item.llm_assumption_stale = bool(assumption_judgment) and (
            not item.llm_assumption_lean_statement_sha256
            or not item.llm_assumption_paper_statement_sha256
            or item.llm_assumption_lean_statement_sha256
            not in lean_statement_digest_candidates(
                item.lean_statement, item.interface_source
            )
            or item.llm_assumption_paper_statement_sha256
            != statement_digest(item.paper_statement)
            or bool(assumption_judgment.get("prompt_version_stale"))
            or bool(assumption_judgment.get("metadata_missing"))
        )
    # The v11 raw-source screen is the authoritative row-local semantic
    # judgment for transparent Specs. Project it onto strict coverage rows
    # only when the bounded packet cache authenticates the current expanded
    # Spec surface; never trigger an implicit Lean walk from a cache rebind.
    _rebind_cached_v11_source_spec_sidecar(
        folder,
        items,
        semantic_reuse_authority=semantic_reuse_authority,
    )
    SIGNATURE_MANIFEST_CACHE[str(folder.resolve())] = manifests


def load_cached_review_rows(
    folder: Path,
    *,
    signature_contexts: dict[str, Any] | None = None,
    source_hashes: dict[str, str] | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    persist_rebind: bool = True,
    cache_payload: Mapping[str, Any] | None = None,
    semantic_reuse_authority: CurrentSemanticReuseAuthority | None = None,
) -> list[ReviewItem] | None:
    """Load cached rows when their exact payload still matches current inputs.

    A caller that already acquired and hashed the cache can supply
    ``cache_payload`` so this function does not reopen the mutable path and mix
    rows from a different instant into the caller's transaction.
    """

    cache_path = paper_interface_cache_file(folder)
    if cache_payload is None:
        if not cache_path.exists() or not cache_path.is_file():
            return None
        try:
            payload = json.loads(cache_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return None
    else:
        payload = dict(cache_payload)

    if payload.get("schema") != PAPER_INTERFACE_CACHE_SCHEMA:
        return None
    if payload.get("paper") != folder.name:
        return None
    if (
        signature_contexts is not None
        and payload.get("signature_contexts") != signature_contexts
    ):
        return None

    hashes = (
        source_hashes
        if source_hashes is not None
        else _cache_source_hashes(
            folder,
            build_input_provider=build_input_provider,
        )
    )
    recorded_hashes = payload.get("hashes", {})
    if not isinstance(recorded_hashes, dict):
        return None
    if payload.get("hashes", {}).get("review_source_file") != hashes["review_source_file"]:
        return None
    if payload.get("hashes", {}).get("interface_sha256") != hashes["interface_sha256"]:
        return None
    if (
        payload.get("hashes", {}).get("lean_source_closure_sha256")
        != hashes["lean_source_closure_sha256"]
    ):
        return None
    report_changed = (
        str(recorded_hashes.get("report_sha256") or "")
        != hashes["report_sha256"]
    )
    if payload.get("hashes", {}).get("tex_sha256") != hashes["tex_sha256"]:
        return None
    if payload.get("hashes", {}).get("text_sha256") != hashes["text_sha256"]:
        return None
    if payload.get("hashes", {}).get("pdf_sha256") != hashes["pdf_sha256"]:
        return None
    # The source map supplies paper-facing display text and source-coverage
    # metadata, but it does not choose or elaborate the Lean review surface.
    # Re-extracting every signature manifest after a coverage-mode, anchor, or
    # source-text edit therefore wastes a current Lean receipt.  Rebind the
    # lightweight paper statements below instead; that recomputes judgment
    # staleness against the updated text and fails closed when declarations no
    # longer align.
    statement_map_changed = (
        payload.get("hashes", {}).get("paper_statement_map_sha256")
        != hashes["paper_statement_map_sha256"]
    )
    display_status_changed = (
        str(recorded_hashes.get("review_surface_display_sha256") or "")
        != hashes["review_surface_display_sha256"]
    )
    status_rebind_changed = (
        str(recorded_hashes.get("review_surface_rebind_sha256") or "")
        != hashes["review_surface_rebind_sha256"]
    )
    recorded_static_status = str(
        recorded_hashes.get("review_surface_static_sha256") or ""
    ).strip()
    static_status_changed = (
        recorded_static_status != hashes["review_surface_static_sha256"]
    )

    rows = payload.get("rows")
    if not isinstance(rows, list):
        return None

    out: list[ReviewItem] = []
    for raw_row in rows:
        if not isinstance(raw_row, dict):
            continue
        name = str(raw_row.get("name") or "").strip()
        kind = str(raw_row.get("kind") or "").strip()
        lean_statement = str(raw_row.get("lean_statement") or "").strip()
        paper_statement = str(raw_row.get("paper_statement") or "").strip()
        agent_statement = str(raw_row.get("agent_statement") or "").strip()
        full_name = str(raw_row.get("full_name") or "").strip()
        interface_source = str(raw_row.get("interface_source") or "").strip()
        raw_signature_manifest = raw_row.get("lean_signature_manifest")
        lean_signature_manifest = (
            raw_signature_manifest if isinstance(raw_signature_manifest, dict) else None
        )
        lean_signature_sha256 = str(
            raw_row.get("lean_signature_sha256") or ""
        ).strip()
        source_status = str(raw_row.get("source_status") or "").strip()
        source_note = str(raw_row.get("source_note") or "").strip()
        llm_match_judgment = str(raw_row.get("llm_match_judgment") or "").strip()
        llm_match_reason = str(raw_row.get("llm_match_reason") or "").strip()
        llm_match_stale = bool(raw_row.get("llm_match_stale") or False)
        llm_match_source = str(raw_row.get("llm_match_source") or "").strip()
        llm_match_validator = str(raw_row.get("llm_match_validator") or "").strip()
        llm_match_validator_type = str(raw_row.get("llm_match_validator_type") or "").strip()
        llm_match_validated_at = str(raw_row.get("llm_match_validated_at") or "").strip()
        llm_match_lean_statement_sha256 = str(
            raw_row.get("llm_match_lean_statement_sha256") or ""
        ).strip()
        llm_match_lean_signature_sha256 = str(
            raw_row.get("llm_match_lean_signature_sha256") or ""
        ).strip()
        llm_match_paper_statement_sha256 = str(
            raw_row.get("llm_match_paper_statement_sha256") or ""
        ).strip()
        llm_match_tex_statement_sha256 = str(
            raw_row.get("llm_match_tex_statement_sha256") or ""
        ).strip()
        llm_match_resolution = _normalize_llm_match_resolution(
            raw_row.get("llm_match_resolution")
        )
        llm_match_boundary_type = str(raw_row.get("llm_match_boundary_type") or "").strip()
        llm_match_boundary_names = _normalize_string_list(
            raw_row.get("llm_match_boundary_names")
        )
        llm_match_conditional_premises = _normalize_string_list(
            raw_row.get("llm_match_conditional_premises")
        )
        llm_match_resolution_reason = str(
            raw_row.get("llm_match_resolution_reason") or ""
        ).strip()
        raw_llm_match_source_routes = raw_row.get("llm_match_source_routes")
        llm_match_source_routes = (
            raw_llm_match_source_routes
            if isinstance(raw_llm_match_source_routes, list)
            else []
        )
        llm_match_component_target_sha256 = str(
            raw_row.get("llm_match_component_target_sha256") or ""
        ).strip()
        is_assumption = bool(raw_row.get("is_assumption") or False)
        is_proposition_spec = bool(raw_row.get("is_proposition_spec") or False)
        proposition_spec_role = str(raw_row.get("proposition_spec_role") or "").strip()
        proposition_spec_proof = str(raw_row.get("proposition_spec_proof") or "").strip()
        raw_semantic_contract_match = raw_row.get(
            "semantic_contract_lean_match_verified"
        )
        semantic_contract_lean_match_verified = (
            raw_semantic_contract_match
            if isinstance(raw_semantic_contract_match, bool)
            else None
        )
        raw_semantic_contract_transparency = raw_row.get(
            "semantic_contract_lean_transparency_verified"
        )
        semantic_contract_lean_transparency_verified = (
            raw_semantic_contract_transparency
            if isinstance(raw_semantic_contract_transparency, bool)
            else None
        )
        llm_assumption_judgment = str(raw_row.get("llm_assumption_judgment") or "").strip()
        llm_assumption_reason = str(raw_row.get("llm_assumption_reason") or "").strip()
        llm_assumption_stale = bool(raw_row.get("llm_assumption_stale") or False)
        llm_assumption_source = str(raw_row.get("llm_assumption_source") or "").strip()
        llm_assumption_validator = str(raw_row.get("llm_assumption_validator") or "").strip()
        llm_assumption_validator_type = str(raw_row.get("llm_assumption_validator_type") or "").strip()
        llm_assumption_validated_at = str(raw_row.get("llm_assumption_validated_at") or "").strip()
        llm_assumption_lean_statement_sha256 = str(
            raw_row.get("llm_assumption_lean_statement_sha256") or ""
        ).strip()
        llm_assumption_paper_statement_sha256 = str(
            raw_row.get("llm_assumption_paper_statement_sha256") or ""
        ).strip()
        raw_premise_judgments = raw_row.get("llm_assumption_premise_judgments")
        llm_assumption_premise_judgments = (
            raw_premise_judgments if isinstance(raw_premise_judgments, dict) else {}
        )
        paper_statement_image_url = str(raw_row.get("paper_statement_image_url") or "").strip()
        source_item_key = str(raw_row.get("source_item_key") or "").strip()
        source_input_bundle_sha256 = str(
            raw_row.get("source_input_bundle_sha256") or ""
        ).strip().lower()
        verbatim_source_input = str(raw_row.get("verbatim_source_input") or "")
        line_number = int(raw_row.get("line_number") or 0)
        slice_id = _safe_slice_id(str(raw_row.get("slice_id") or "all"))
        slice_title = str(raw_row.get("slice_title") or "All statements").strip()
        if not name or not kind or not lean_statement:
            continue
        out.append(
            ReviewItem(
                name=name,
                kind=kind,
                lean_statement=lean_statement,
                paper_statement=paper_statement,
                agent_statement=agent_statement,
                full_name=full_name,
                interface_source=interface_source,
                lean_signature_manifest=lean_signature_manifest,
                lean_signature_sha256=lean_signature_sha256,
                source_status=source_status,
                source_note=source_note,
                llm_match_judgment=llm_match_judgment,
                llm_match_reason=llm_match_reason,
                llm_match_stale=llm_match_stale,
                llm_match_source=llm_match_source,
                llm_match_validator=llm_match_validator,
                llm_match_validator_type=llm_match_validator_type,
                llm_match_validated_at=llm_match_validated_at,
                llm_match_lean_statement_sha256=llm_match_lean_statement_sha256,
                llm_match_lean_signature_sha256=llm_match_lean_signature_sha256,
                llm_match_paper_statement_sha256=llm_match_paper_statement_sha256,
                llm_match_tex_statement_sha256=llm_match_tex_statement_sha256,
                llm_match_resolution=llm_match_resolution,
                llm_match_boundary_type=llm_match_boundary_type,
                llm_match_boundary_names=llm_match_boundary_names,
                llm_match_conditional_premises=llm_match_conditional_premises,
                llm_match_resolution_reason=llm_match_resolution_reason,
                llm_match_source_routes=llm_match_source_routes,
                llm_match_component_target_sha256=(
                    llm_match_component_target_sha256
                ),
                is_assumption=is_assumption,
                is_proposition_spec=is_proposition_spec,
                proposition_spec_role=proposition_spec_role,
                proposition_spec_proof=proposition_spec_proof,
                semantic_contract_lean_match_verified=(
                    semantic_contract_lean_match_verified
                ),
                semantic_contract_lean_transparency_verified=(
                    semantic_contract_lean_transparency_verified
                ),
                llm_assumption_judgment=llm_assumption_judgment,
                llm_assumption_reason=llm_assumption_reason,
                llm_assumption_stale=llm_assumption_stale,
                llm_assumption_source=llm_assumption_source,
                llm_assumption_validator=llm_assumption_validator,
                llm_assumption_validator_type=llm_assumption_validator_type,
                llm_assumption_validated_at=llm_assumption_validated_at,
                llm_assumption_lean_statement_sha256=llm_assumption_lean_statement_sha256,
                llm_assumption_paper_statement_sha256=llm_assumption_paper_statement_sha256,
                llm_assumption_premise_judgments=llm_assumption_premise_judgments,
                paper_statement_image_url=paper_statement_image_url,
                source_item_key=source_item_key,
                source_input_bundle_sha256=source_input_bundle_sha256,
                verbatim_source_input=verbatim_source_input,
                line_number=line_number,
                slice_id=slice_id,
                slice_title=slice_title or slice_id,
            )
        )
    direct_route_statement_stale = bool(out) and not (
        cached_direct_source_route_statements_are_current(folder, out)
    )
    if static_status_changed and (
        not out or not cached_rows_match_current_extraction_surface(folder, out)
    ):
        return None
    statement_rebind_required = bool(out) and (
        report_changed
        or statement_map_changed
        or display_status_changed
        or direct_route_statement_stale
    )
    if statement_rebind_required:
        if not rebind_cached_report_statements(folder, out):
            return None
    if out and (
        report_changed
        or statement_map_changed
        or display_status_changed
        or status_rebind_changed
        or static_status_changed
    ):
        rebound = rebind_cached_review_status(folder, out)
        if rebound is None:
            return None
        out = rebound
    if out:
        rebind_cached_review_sidecars(
            folder,
            out,
            semantic_reuse_authority=semantic_reuse_authority,
        )
        semantic_contract_rebound = cached_semantic_contract_results_need_refresh(
            folder, out
        )
        if semantic_contract_rebound:
            provider = build_input_provider or RepositoryBuildInputSnapshotProvider(
                ROOT
            )
            attach_current_lean_semantic_contract_results(
                folder,
                review_source_file(folder),
                out,
                build_input_provider=provider,
            )
        if persist_rebind and (
            report_changed
            or statement_map_changed
            or display_status_changed
            or status_rebind_changed
            or static_status_changed
            or direct_route_statement_stale
            or semantic_contract_rebound
        ):
            payload["hashes"] = hashes
            payload["rows"] = [item.__dict__ for item in out]
            try:
                cache_path.write_text(
                    json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
                    encoding="utf-8",
                )
            except OSError:
                # The returned rows remain valid. Failure to persist only
                # causes a later cheap report-text rebind.
                pass
    configured_support = review_quarantined_auxiliary_names(folder)
    support_items: dict[str, ReviewItem] = {}
    raw_support_rows = payload.get("quarantined_support_rows")
    if configured_support:
        if not isinstance(raw_support_rows, list):
            return None
        for raw_row in raw_support_rows:
            if not isinstance(raw_row, dict):
                return None
            name = str(raw_row.get("name") or "").strip()
            full_name = str(raw_row.get("full_name") or "").strip()
            if name not in configured_support and full_name not in configured_support:
                return None
            manifest = raw_row.get("lean_signature_manifest")
            signature = str(raw_row.get("lean_signature_sha256") or "").strip()
            lean_statement = str(raw_row.get("lean_statement") or "").strip()
            if (
                not name
                or not lean_statement
                or not isinstance(manifest, dict)
                or not signature
                or signature_manifest_digest(manifest) != signature
                or str(manifest.get("sha256") or "").strip() != signature
            ):
                return None
            item = ReviewItem(
                name=name,
                kind=str(raw_row.get("kind") or "").strip(),
                lean_statement=lean_statement,
                paper_statement=str(raw_row.get("paper_statement") or ""),
                agent_statement=str(raw_row.get("agent_statement") or ""),
                full_name=full_name,
                interface_source=str(raw_row.get("interface_source") or ""),
                lean_signature_manifest=manifest,
                lean_signature_sha256=signature,
                line_number=int(raw_row.get("line_number") or 0),
            )
            support_items[name] = item
            if full_name:
                support_items[full_name] = item
        resolved_support = {
            configured
            for configured in configured_support
            if configured in support_items
            or configured.rsplit(".", 1)[-1] in support_items
        }
        if resolved_support != configured_support:
            return None
    QUARANTINED_SUPPORT_REVIEW_ITEM_CACHE[str(folder.resolve())] = support_items
    return out or None


def load_interactive_cached_review_rows(
    folder: Path,
    *,
    semantic_reuse_authority: CurrentSemanticReuseAuthority | None = None,
) -> list[ReviewItem] | None:
    """Reuse a cache for human review without rewalking the Lean universe.

    A dashboard page is a statement-review surface, not a new proof-closeout
    run.  Its persisted rows already contain the elaborated interface
    statements and manifests produced during the last cache refresh.  For an
    interactive reload, verify every direct display input and rebind changed
    report/map/status text, while retaining the cache's already-validated Lean
    closure pin.  Strict closeout and explicit cache refreshes still call
    :func:`_cache_source_hashes`, rebuild that closure through Lean, and fail
    closed on any dependency change.

    This separation makes the ordinary reviewer path responsive after a
    completed closeout without weakening any release or audit gate.
    """

    cache_path = paper_interface_cache_file(folder)
    try:
        payload = json.loads(cache_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return None
    if (
        not isinstance(payload, Mapping)
        or payload.get("schema") != PAPER_INTERFACE_CACHE_SCHEMA
        or payload.get("paper") != folder.name
    ):
        return None
    recorded_hashes = payload.get("hashes")
    if not isinstance(recorded_hashes, Mapping):
        return None
    recorded_closure = str(
        recorded_hashes.get("lean_source_closure_sha256") or ""
    ).strip()
    if not re.fullmatch(r"[0-9a-f]{64}", recorded_closure):
        return None

    hashes = _cache_nonlean_source_hashes(folder)
    hashes["lean_source_closure_sha256"] = recorded_closure
    return load_cached_review_rows(
        folder,
        source_hashes=hashes,
        cache_payload=payload,
        semantic_reuse_authority=semantic_reuse_authority,
    )


def write_cached_review_rows(
    folder: Path,
    items: list[ReviewItem],
    *,
    signature_contexts: dict[str, Any] | None = None,
    source_hashes: dict[str, str] | None = None,
) -> None:
    """Persist dashboard rows with source hashes for future reloads."""

    cache_path = paper_interface_cache_file(folder)
    cache_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema": PAPER_INTERFACE_CACHE_SCHEMA,
        "paper": folder.name,
        "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds").replace(
            "+00:00", "Z"
        ),
        "hashes": source_hashes if source_hashes is not None else _cache_source_hashes(folder),
        "rows": [item.__dict__ for item in items],
        "quarantined_support_rows": [
            item.__dict__
            for item in {
                id(item): item
                for item in quarantined_support_review_items(folder).values()
            }.values()
        ],
    }
    if signature_contexts is not None:
        payload["signature_contexts"] = signature_contexts
    cache_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def cached_review_row_hashes_match(
    folder: Path, source_hashes: dict[str, str]
) -> bool:
    """Whether the persisted row cache already carries the verified snapshot."""

    cache_path = paper_interface_cache_file(folder)
    try:
        payload = json.loads(cache_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    return payload.get("hashes") == source_hashes


def review_items_for_paper(
    folder: Path,
    use_cache: bool = True,
    *,
    render_images: bool = True,
    require_current_signatures: bool = False,
    persist_cache_rebind: bool = True,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    audit_inputs: DashboardAuditInputs | None = None,
    validated_configured_review_rows: Iterable[Mapping[str, Any]] | None = None,
    semantic_reuse_authority: CurrentSemanticReuseAuthority | None = None,
    progress: Callable[[str], None] | None = None,
    publish_manifest_store: bool = False,
) -> list[ReviewItem]:
    """Read cached items if possible, else compute from source files.

    Strict repository audits set `require_current_signatures` so cached rows
    are accepted only after the relevant review modules have rebuilt and their
    Lean-manifest context matches the stored cache metadata.
    """

    if audit_inputs is not None:
        semantic_kwargs: dict[str, object] = {}
        if semantic_reuse_authority is not None:
            semantic_kwargs["semantic_reuse_authority"] = (
                semantic_reuse_authority
            )
        with dashboard_audit_input_scope(audit_inputs):
            return review_items_for_paper(
                folder,
                use_cache=use_cache,
                render_images=render_images,
                require_current_signatures=require_current_signatures,
                persist_cache_rebind=persist_cache_rebind,
                build_input_provider=build_input_provider,
                validated_configured_review_rows=(
                    validated_configured_review_rows
                ),
                progress=progress,
                publish_manifest_store=publish_manifest_store,
                **semantic_kwargs,
            )

    # The ordinary browser path needs the current review statements, not a
    # second proof-closeout traversal of every imported module.  Reuse the
    # cached elaborated rows when their direct display inputs still match;
    # `load_interactive_cached_review_rows` rebinds report/map/status text as
    # needed.  Strict checks and explicit cache refreshes deliberately bypass
    # this branch and retain the full Lean-closure validation below.
    if use_cache and not require_current_signatures:
        cached = load_interactive_cached_review_rows(
            folder,
            semantic_reuse_authority=semantic_reuse_authority,
        )
        if cached is not None:
            if render_images:
                attach_rendered_statement_images(folder, cached)
            return cached

    owns_build_input_provider = build_input_provider is None
    if build_input_provider is None:
        build_input_provider = RepositoryBuildInputSnapshotProvider(ROOT)
    build_inputs_finalized = False
    frozen_inputs_active = _dashboard_audit_inputs() is not None

    def emit_progress(message: str) -> None:
        if progress is None:
            return
        try:
            progress(message)
        except Exception:  # noqa: BLE001 - reporting cannot alter audit evidence.
            pass

    def require_unchanged_build_inputs() -> None:
        nonlocal build_inputs_finalized
        if (
            owns_build_input_provider
            and not build_inputs_finalized
            and not build_input_provider.finalize_unchanged()
        ):
            raise RuntimeError(
                f"repository build inputs changed while reviewing {folder.name}; "
                "discarding the result"
            )
        build_inputs_finalized = True

    def finalized(items: list[ReviewItem]) -> list[ReviewItem]:
        require_unchanged_build_inputs()
        return items

    source_hashes_before = (
        _cache_source_hashes(
            folder,
            build_input_provider=build_input_provider,
        )
        if (use_cache or require_current_signatures) and not frozen_inputs_active
        else None
    )
    if require_current_signatures:
        emit_progress("current Lean manifest contexts started")
        signature_contexts = current_review_signature_contexts(
            folder,
            build_input_provider=build_input_provider,
        )
    else:
        signature_contexts = None
    if require_current_signatures and signature_contexts is None:
        raise RuntimeError(f"could not build current Lean signature context for {folder.name}")
    if require_current_signatures and signature_contexts is not None:
        emit_progress(
            f"current Lean manifest contexts ready ({len(signature_contexts)} modules)"
        )
        try:
            semantic_prime_kwargs: dict[str, object] = {}
            if semantic_reuse_authority is not None:
                semantic_prime_kwargs["semantic_reuse_authority"] = (
                    semantic_reuse_authority
                )
            prime_diagnostics = prime_review_signature_manifest_store(
                folder,
                signature_contexts,
                allow_migration_write=persist_cache_rebind,
                validated_configured_review_rows=(
                    validated_configured_review_rows
                ),
                **semantic_prime_kwargs,
            )
            # An interactive refresh has no transaction-owned raw rows, so the
            # primary prime intentionally declines to read mutable cache state.
            # It can nevertheless compactly revalidate exact unchanged items
            # against receipt-validated prior raw evidence and a tracked
            # authority/carrier pair.  This stays strictly outside frozen
            # closeout runs, whose inputs must be wholly transaction-owned.
            if (
                validated_configured_review_rows is None
                and persist_cache_rebind
                and not frozen_inputs_active
            ):
                prime_diagnostics = prime_review_signature_manifest_store_from_prior(
                    folder, signature_contexts
                )
            emit_progress(
                "authenticated manifest reuse finished "
                f"({int(prime_diagnostics.get('seeded_count') or 0)} seeded; "
                f"{int(prime_diagnostics.get('fresh_required_count') or 0)} "
                "require fresh Lean; "
                f"{str(prime_diagnostics.get('store_status') or 'unknown')})"
            )
        except Exception as exc:  # noqa: BLE001 - optimization failure stays a miss.
            emit_progress(
                "authenticated manifest reuse unavailable " + type(exc).__name__
            )

    # The ordinary persisted row cache remains an interactive artifact. A
    # strict closeout can reuse only complete manifests independently rebound
    # to its current raw rows and exact compiled contexts above; every cache
    # miss still receives current Lean extraction. Semantic judgments are then
    # checked item by item against that signature-current manifest surface.
    if use_cache and not require_current_signatures and not frozen_inputs_active:
        cached = load_cached_review_rows(
            folder,
            signature_contexts=signature_contexts,
            source_hashes=source_hashes_before,
            build_input_provider=build_input_provider,
            persist_rebind=(persist_cache_rebind and not require_current_signatures),
        )
        if cached is not None:
            if (
                require_current_signatures
                and _cache_source_hashes(
                    folder,
                    build_input_provider=build_input_provider,
                )
                != source_hashes_before
            ):
                raise RuntimeError(
                    f"paper audit sources changed while loading {folder.name}; "
                    "discarding the cache"
                )
            if (
                require_current_signatures
                and source_hashes_before is not None
                and not cached_review_row_hashes_match(
                    folder, source_hashes_before
                )
            ):
                write_cached_review_rows(
                    folder,
                    cached,
                    signature_contexts=signature_contexts,
                    source_hashes=source_hashes_before,
                )
            require_unchanged_build_inputs()
            if render_images:
                attach_rendered_statement_images(folder, cached)
            return cached

    interface = review_source_file(folder)
    report = paper_relative_file(folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md")
    items = parse_interface_items(
        interface,
        report if _dashboard_is_file(report) else None,
        folder,
        render_lean_previews=not (
            require_current_signatures and not render_images
        ),
        build_input_provider=build_input_provider,
        progress=progress,
    )
    if require_current_signatures:
        stable_contexts = current_review_signature_contexts(
            folder,
            build_input_provider=build_input_provider,
        )
        if stable_contexts is None:
            raise RuntimeError(
                f"could not rebuild Lean signature context after extracting {folder.name}"
            )
        if stable_contexts != signature_contexts:
            raise RuntimeError(
                f"Lean signature context changed while extracting {folder.name}; "
                "discarding the cache"
            )
        source_hashes_after: dict[str, str] | None = None
        if not frozen_inputs_active:
            source_hashes_after = _cache_source_hashes(
                folder,
                build_input_provider=build_input_provider,
            )
            if source_hashes_after != source_hashes_before:
                raise RuntimeError(
                    f"paper audit sources changed while extracting {folder.name}; "
                    "discarding the cache"
                )
        require_unchanged_build_inputs()
        if persist_cache_rebind and source_hashes_after is not None:
            write_cached_review_rows(
                folder,
                items,
                signature_contexts=stable_contexts,
                source_hashes=source_hashes_after,
            )
            emit_progress(f"dashboard row cache written ({len(items)} rows)")
            if publish_manifest_store:
                try:
                    published = publish_review_signature_manifest_store(
                        folder, items, stable_contexts
                    )
                    emit_progress(
                        "authenticated manifest store published "
                        f"({len(published)} entries)"
                    )
                except Exception as exc:  # noqa: BLE001 - persistence is an optimization.
                    emit_progress(
                        "authenticated manifest store publication unavailable "
                        + type(exc).__name__
                    )
    else:
        require_unchanged_build_inputs()
    if render_images:
        attach_rendered_statement_images(folder, items)
    return finalized(items)


def refresh_cached_review_rows(folder: Path) -> None:
    """Force cache regeneration for one paper folder."""

    def progress(message: str) -> None:
        print(
            f"review-dashboard: {folder.name}: {message}",
            file=sys.stderr,
            flush=True,
        )

    review_items_for_paper(
        folder,
        use_cache=False,
        render_images=False,
        require_current_signatures=True,
        progress=progress,
        publish_manifest_store=True,
    )


def review_surface_digest(items: list[ReviewItem]) -> str:
    """Return a stable digest of the human-facing dashboard row surface."""

    payload = [
        {
            "name": item.name,
            "kind": item.kind,
            "lean_statement": normalize_statement(item.lean_statement or item.interface_source),
            "paper_statement": normalize_statement(item.paper_statement),
            "source_input_bundle_sha256": item.source_input_bundle_sha256,
            "source_status": normalize_statement(item.source_status),
            "source_note": normalize_statement(item.source_note),
            "is_assumption": bool(item.is_assumption),
            "is_proposition_spec": bool(item.is_proposition_spec),
            "proposition_spec_role": item.proposition_spec_role,
            "proposition_spec_proof": item.proposition_spec_proof,
        }
        for item in sorted(items, key=lambda row: row.name)
    ]
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def semantic_statement_review_items(
    folder: Path, items: Iterable[ReviewItem]
) -> list[ReviewItem]:
    """Select one semantic source-to-Spec target for each mapped source claim.

    The raw dashboard declaration list remains useful for Lean proof and
    import-closure checks.  It is not the source-semantic surface: a
    transparent Spec and its theorem wrapper share one source claim.  A
    legacy paper without declared Spec contracts retains its ordinary rows so
    that missing migration evidence cannot disappear from the audit.
    """

    all_items = list(items)
    source_map = paper_statement_map_payload(folder)
    raw_items = source_map.get("items") if isinstance(source_map, Mapping) else None
    specs: set[str] = set()
    if isinstance(raw_items, Mapping):
        for record in raw_items.values():
            if not isinstance(record, Mapping):
                continue
            contract = record.get("semantic_contract")
            if isinstance(contract, Mapping):
                spec = str(contract.get("spec_declaration") or "").strip()
                if spec:
                    specs.add(spec)
            values = record.get("spec_lean_declarations")
            if isinstance(values, list):
                specs.update(str(value).strip() for value in values if str(value).strip())
    selected = [
        item
        for item in all_items
        if item.full_name in specs or item.name in specs
    ]
    if selected:
        return selected
    return [
        item
        for item in all_items
        if not item.is_assumption and not is_assumption_item_name(item.name)
    ]


def _current_bound_v11_statement_judgment(
    item: ReviewItem,
) -> dict[str, Any] | None:
    """Return a v11 judgment attached by the current cache-rebind transaction.

    ``_rebind_cached_v11_source_spec_sidecar`` clears/reloads ordinary sidecars
    first and attaches these fields only after the exact current packet cache
    and raw-source/expanded-Spec ledger match.  These checks prevent a partial
    or hand-constructed row from acquiring the same authority after that
    transaction boundary.
    """

    if (
        item.llm_match_source
        != Path(V11_RAW_SOURCE_SPEC_SCREENING_FILE).name
        or item.llm_match_stale
        or not item.full_name.endswith("Spec")
    ):
        return None
    judgment = _normalize_llm_match_judgment(item.llm_match_judgment)
    if judgment not in {
        *POSITIVE_SEMANTIC_MATCH_JUDGMENTS,
        "mismatch",
        "uncertain",
    }:
        return None
    if (
        item.llm_match_paper_statement_sha256
        != statement_digest(item.paper_statement)
        or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(
            item.llm_match_lean_statement_sha256
        )
        or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(
            item.source_input_bundle_sha256
        )
        or not item.llm_match_validator.strip()
        or not item.llm_match_validated_at.strip()
    ):
        return None
    return {
        "judgment": judgment,
        "reason": item.llm_match_reason,
        "source": item.llm_match_source,
        "validator": item.llm_match_validator,
        "validator_type": item.llm_match_validator_type,
        "validated_at": item.llm_match_validated_at,
        "lean_statement_sha256": item.llm_match_lean_statement_sha256,
        "paper_statement_sha256": item.llm_match_paper_statement_sha256,
        "source_input_bundle_sha256": item.source_input_bundle_sha256,
        "current_bound_v11": True,
    }


def review_surface_audit_summary(folder: Path, items: list[ReviewItem]) -> dict[str, Any]:
    """Summarize row-count thresholds and optional LLM review-surface audit status."""

    semantic_items = semantic_statement_review_items(folder, items)
    row_count = len(semantic_items)
    surface_hash = review_surface_digest(semantic_items)
    audit = load_llm_review_surface_audit(folder)
    recorded_rows = audit.get("review_rows")
    recorded_hash = str(audit.get("review_surface_sha256") or "").strip()
    judgment = str(audit.get("judgment") or "").strip()
    has_completed_audit = bool(
        judgment or audit.get("reason") or recorded_hash or (isinstance(recorded_rows, int) and recorded_rows > 0)
    )
    stale = False
    if audit and has_completed_audit:
        if isinstance(recorded_rows, int) and recorded_rows != row_count:
            stale = True
        if recorded_hash and recorded_hash != surface_hash:
            stale = True
        if audit.get("prompt_version_stale"):
            stale = True
        if audit.get("metadata_missing"):
            stale = True
    audit_required = row_count > REVIEW_SURFACE_LLM_AUDIT_THRESHOLD
    missing_required = audit_required and not has_completed_audit
    needs_curation = judgment == "needs_curation"
    uncertain = judgment == "uncertain"
    unknown = bool(has_completed_audit and judgment not in {"passes", "needs_curation", "uncertain"})
    non_evidence_scaffold = bool(audit.get("non_evidence_scaffold"))
    oversize = row_count >= REVIEW_SURFACE_WARN_THRESHOLD
    # An existing broad declaration-level review-surface sidecar is historical
    # once a paper projects paired Specs/proof wrappers to claim rows.  Do not
    # block a compact (below-threshold) human surface merely because that
    # optional old presentation audit has a different row count.
    needs_attention = missing_required or (
        audit_required
        and (
            stale
            or needs_curation
            or uncertain
            or unknown
            or non_evidence_scaffold
        )
    )
    return {
        "row_count": row_count,
        "llm_threshold": REVIEW_SURFACE_LLM_AUDIT_THRESHOLD,
        "warn_threshold": REVIEW_SURFACE_WARN_THRESHOLD,
        "audit_required": audit_required,
        "oversize": oversize,
        "missing_required": missing_required,
        "stale": stale,
        "judgment": judgment,
        "unknown_judgment": unknown,
        "reason": str(audit.get("reason") or "").strip(),
        "source": str(audit.get("source") or "").strip() if has_completed_audit else "",
        "has_completed_audit": has_completed_audit,
        "review_surface_sha256": surface_hash,
        "recorded_review_surface_sha256": recorded_hash,
        "recorded_review_rows": recorded_rows if isinstance(recorded_rows, int) else None,
        "prompt_version": str(audit.get("prompt_version") or "").strip(),
        "prompt_version_stale": bool(audit.get("prompt_version_stale")),
        "metadata_missing": bool(audit.get("metadata_missing")),
        "non_evidence_scaffold": non_evidence_scaffold,
        "needs_attention": needs_attention,
        "has_warning": needs_attention or oversize,
    }


def library_semantic_review_summary(
    folder: Path,
    items: Iterable[ReviewItem],
    *,
    entries_override: Iterable[Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Summarize material source-to-library semantic prerequisites.

    This is deliberately supplementary to the paper-local Spec judgment.  A
    new prerequisite receipt does not rewrite or falsely invalidate an already
    hash-bound source-to-Spec receipt, but a closeout cannot call the combined
    semantic surface complete while a material reused definition is unlinked,
    stale, mismatched, or uncertain.
    """

    entries = (
        [dict(entry) for entry in entries_override]
        if entries_override is not None
        else human_review_library_prerequisites(
            folder,
            [item.__dict__ for item in items],
            semantic_targets_override={},
        )
    )
    return semantic_prerequisite_review_summary(entries)


def semantic_prerequisite_review_summary(
    entries: Iterable[Mapping[str, Any]],
) -> dict[str, Any]:
    """Summarize prepared prerequisite cards without rediscovering them.

    This helper is presentation-only. Its inputs have already been selected
    and source-bound by the typed packet surface; it neither parses Lean nor
    grants closeout acceptance.
    """

    prepared_entries = [dict(entry) for entry in entries]
    pending = [
        str(entry.get("lean_name") or "")
        for entry in prepared_entries
        if not entry.get("verbatim_source_input")
        or str(entry.get("semantic_judgment") or "") == "not recorded"
    ]
    stale = [
        str(entry.get("lean_name") or "")
        for entry in prepared_entries
        if str(entry.get("semantic_judgment") or "") != "not recorded"
        and not bool(entry.get("semantic_current"))
    ]
    mismatch = [
        str(entry.get("lean_name") or "")
        for entry in prepared_entries
        if bool(entry.get("semantic_current"))
        and str(entry.get("semantic_judgment") or "") == "mismatch"
    ]
    uncertain = [
        str(entry.get("lean_name") or "")
        for entry in prepared_entries
        if bool(entry.get("semantic_current"))
        and str(entry.get("semantic_judgment") or "") == "uncertain"
    ]
    matches = sum(
        1
        for entry in prepared_entries
        if bool(entry.get("semantic_current"))
        and str(entry.get("semantic_judgment") or "") == "matches"
    )
    return {
        "row_count": len(prepared_entries),
        "current_matches": matches,
        "pending": pending,
        "pending_count": len(pending),
        "stale": stale,
        "stale_count": len(stale),
        "mismatch": mismatch,
        "mismatch_count": len(mismatch),
        "uncertain": uncertain,
        "uncertain_count": len(uncertain),
        "needs_attention": bool(pending or stale or mismatch or uncertain),
    }


def statement_translation_audit_summary(
    folder: Path,
    items: list[ReviewItem],
    *,
    library_summary_override: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Summarize raw-source-to-expanded-Spec semantic statement coverage."""

    statement_items = semantic_statement_review_items(folder, items)
    draft_entries = load_llm_lean_to_tex_draft_entries(folder)
    judgments = load_llm_statement_judgments(
        folder,
        {
            item.name: item.lean_signature_manifest
            for item in items
            if isinstance(item.lean_signature_manifest, dict)
        },
    )
    missing_draft: list[str] = []
    stale_draft: list[str] = []
    missing_judgment: list[str] = []
    stale_judgment: list[str] = []
    missing_obligation_ledger: list[str] = []
    mismatch: list[str] = []
    conditional_boundary: list[str] = []
    unresolved_mismatch: list[str] = []
    uncertain: list[str] = []
    unknown: list[str] = []
    ambiguous_semantic_judgment: list[str] = []
    semantic_rebound_judgment: list[str] = []
    semantic_reused_stale_draft: list[str] = []
    semantic_current_judgment_count = 0
    matches = 0
    library_prerequisites = (
        dict(library_summary_override)
        if library_summary_override is not None
        else library_semantic_review_summary(folder, statement_items)
    )
    semantic_judgment_index = _semantic_statement_judgment_index(judgments)

    for item in statement_items:
        bound_v11_judgment = _current_bound_v11_statement_judgment(item)
        if bound_v11_judgment is not None:
            semantic_key = item.name
            semantic_judgment = bound_v11_judgment
            semantic_ambiguous = False
        else:
            semantic_key, semantic_judgment, semantic_ambiguous = (
                _current_semantic_statement_judgment_for_item(
                    item,
                    judgments,
                    identity_index=semantic_judgment_index,
                )
            )
        if semantic_ambiguous:
            ambiguous_semantic_judgment.append(item.name)
        if semantic_judgment is not None:
            semantic_current_judgment_count += 1
            if bound_v11_judgment is None and semantic_key != item.name:
                semantic_rebound_judgment.append(item.name)

        # Lean-to-TeX drafts are optional explanatory renderings.  They are
        # never v11 semantic inputs and therefore cannot make a raw-source /
        # expanded-Spec judgment stale or complete.
        draft = draft_entries.get(item.name)
        if draft:
            recorded_lean = str(draft.get("lean_statement_sha256") or "").strip()
            stale = (
                (
                    recorded_lean
                    and recorded_lean
                    not in lean_statement_digest_candidates(item.lean_statement, item.interface_source)
                )
                or not recorded_lean
                or bool(draft.get("prompt_version_stale"))
                or bool(draft.get("metadata_missing"))
            )
            if stale and str((semantic_judgment or {}).get("judgment") or "").strip() == "matches":
                semantic_reused_stale_draft.append(item.name)

        # Prefer the current exact semantic identity over the sidecar key. A
        # stale or nonmatching named entry remains visible below; an ambiguous
        # exact identity is treated as no evidence rather than guessed from a
        # familiar declaration name.
        judgment = semantic_judgment
        if judgment is None and not semantic_ambiguous:
            judgment = judgments.get(item.name)
        if not judgment:
            missing_judgment.append(item.name)
            continue

        value = str(judgment.get("judgment") or "").strip()
        if value in POSITIVE_SEMANTIC_MATCH_JUDGMENTS:
            matches += 1
        elif value == "mismatch":
            mismatch.append(item.name)
            if _is_conditional_boundary_judgment(judgment):
                conditional_boundary.append(item.name)
            else:
                unresolved_mismatch.append(item.name)
        elif value == "uncertain":
            uncertain.append(item.name)
        else:
            unknown.append(item.name)
        if bound_v11_judgment is None and _llm_statement_judgment_is_stale(
            judgment,
            signature_sha256=item.lean_signature_sha256,
            lean_statement=item.lean_statement,
            paper_statement=item.paper_statement,
            agent_statement=item.agent_statement,
            source_input_bundle_sha256=item.source_input_bundle_sha256,
        ):
            stale_judgment.append(item.name)
        if judgment.get("obligation_ledger_error"):
            missing_obligation_ledger.append(item.name)

    all_uncertain = bool(statement_items) and len(uncertain) == len(statement_items)
    needs_attention = bool(
        missing_judgment
        or stale_judgment
        or missing_obligation_ledger
        or unresolved_mismatch
        or uncertain
        or unknown
        or ambiguous_semantic_judgment
        or library_prerequisites["needs_attention"]
    )
    return {
        "row_count": len(statement_items),
        "draft_count": len(draft_entries),
        "judgment_count": max(len(judgments), semantic_current_judgment_count),
        "matches": matches,
        "mismatch_count": len(mismatch),
        "conditional_boundary_count": len(conditional_boundary),
        "unresolved_mismatch_count": len(unresolved_mismatch),
        "uncertain_count": len(uncertain),
        "unknown_count": len(unknown),
        "missing_draft_count": len(missing_draft),
        "stale_draft_count": len(stale_draft),
        "missing_judgment_count": len(missing_judgment),
        "stale_judgment_count": len(stale_judgment),
        "missing_obligation_ledger_count": len(missing_obligation_ledger),
        "mismatch": mismatch,
        "conditional_boundary": conditional_boundary,
        "unresolved_mismatch": unresolved_mismatch,
        "uncertain": uncertain,
        "unknown": unknown,
        "ambiguous_semantic_judgment_count": len(ambiguous_semantic_judgment),
        "ambiguous_semantic_judgment": ambiguous_semantic_judgment,
        "semantic_current_judgment_count": semantic_current_judgment_count,
        "semantic_rebound_judgment_count": len(semantic_rebound_judgment),
        "semantic_rebound_judgment": semantic_rebound_judgment,
        "semantic_reused_stale_draft_count": len(semantic_reused_stale_draft),
        "semantic_reused_stale_draft": semantic_reused_stale_draft,
        "missing_draft": missing_draft,
        "stale_draft": stale_draft,
        "missing_judgment": missing_judgment,
        "stale_judgment": stale_judgment,
        "missing_obligation_ledger": missing_obligation_ledger,
        "has_completed_audit": bool(judgments or semantic_current_judgment_count),
        "all_uncertain": all_uncertain,
        "library_prerequisites": library_prerequisites,
        "needs_attention": needs_attention,
    }


def paper_coverage_audit_required(folder: Path, inventory: dict[str, dict[str, Any]]) -> bool:
    """Return whether the paper-level source coverage audit should be enforced."""

    payload = load_review_slice_payload(folder)
    explicit = payload.get("paper_coverage_required")
    explicit_configured = False
    if isinstance(explicit, str):
        normalized_explicit = explicit.strip().lower()
        explicit_configured = normalized_explicit in {
            "0",
            "1",
            "false",
            "true",
            "no",
            "yes",
            "not required",
            "optional",
            "required",
            "off",
            "on",
        }
        explicit_enabled = normalized_explicit in {"1", "true", "yes", "required", "on"}
    elif isinstance(explicit, bool):
        explicit_configured = True
        explicit_enabled = explicit
    else:
        explicit_enabled = False

    status_path = folder / DEFAULT_PAPER_STATUS_FILE
    status_value = ""
    if _dashboard_is_file(status_path):
        status_payload = _dashboard_json_payload(status_path) or {}
        if isinstance(status_payload, dict):
            status_value = str(status_payload.get("status") or "").strip().lower()
    public_facing_status = (
        status_value.startswith("formalized")
        or status_value.startswith("partially formalized")
        or status_value.startswith("conditional")
    )
    if status_value == "paper draft":
        return explicit_enabled if explicit_configured else False
    if public_facing_status:
        return True
    if explicit_configured:
        return explicit_enabled
    return bool(
        inventory
        and _dashboard_is_file(folder / PAPER_STATEMENT_MAP_FILE)
    )


def _is_statement_map_source(source: object) -> bool:
    """Return whether an inventory source label names the statement-map sidecar."""

    return str(source or "") == PAPER_STATEMENT_MAP_FILE


# The broad presentation matcher above also recognizes an in-text theorem
# reference.  Scope exclusions need the narrower question: does the *anchored
# item itself* begin as a labelled formal result?  This pattern intentionally
# requires a source heading/environment (or an anchored heading-style verb),
# so a remark that says "as in Theorem 3" is not misclassified as Theorem 3.
SOURCE_NAMED_RESULT_HEADING_RE = re.compile(
    r"""
    (?imx)
    (?:
        \\begin\s*\{\s*(?:theorem|lemma|proposition|corollary|claim|thm|lem|prop|cor)\*?\s*\}
      | ^\s*(?:\\(?:textbf|emph|textit|paragraph)\s*\{?\s*)?
        \b(?:theorem|lemma|proposition|corollary|claim)\b\s*
        (?:~|\\[,;! ]*|:)?\s*
        (?:
            \\(?:auto|[cC]|eq)?ref\s*\{[^}]+\}
          | \\label\s*\{[^}]+\}
          | \(?\s*(?:(?-i:[A-Z])(?:\.\d+)+(?:[a-z])?|(?-i:[A-Z])?\d+(?:\.\d+)*(?:[a-z])?|(?-i:[A-Z]))\s*\)?
        )
        (?=\s*(?:[.:()]|$|\b(?:states?|proves?|shows?|asserts?|claims?|guarantees?)\b))
    )
    """,
    re.IGNORECASE | re.VERBOSE | re.MULTILINE,
)
# Keep performance detection contextual.  In particular, the words
# ``exponential``, ``quadratic``, ``linear``, and ``polynomial`` alone are
# ordinary mathematical vocabulary (distributions, utilities, regressions,
# etc.), not a complexity assertion.  A finite observed benchmark likewise is
# not promoted merely because it contains a number.  The patterns below look
# for resource terminology, asymptotic notation, or a general algorithmic
# behavior instead.
# The computational-illustration exception is intentionally a narrow positive
# classification.  A Figure/Table/plot label only tells us where source prose
# appears; it does not establish that the prose is a finite numerical,
# simulation, or empirical observation.  These are source-language cues only:
# source-map keys and Lean declarations are deliberately not inputs.
# A source may phrase a paper result in ordinary prose instead of attaching a
# theorem number.  Such a claim is still in scope.  The positive finite-
# observation requirement below catches unrecognised mathematical assertions;
# this pattern gives the common correctness/existence/optimality family a
# direct, audit-visible rejection reason.
SOURCE_RESULT_KINDS = {
    "theorem",
    "proposition",
    "lemma",
    "corollary",
    "claim",
    "runtime_claim",
}


def source_inventory_precheck_summary(folder: Path) -> dict[str, Any]:
    """Check source-map readiness without parsing Lean rows.

    This is deliberately an inexpensive first gate. It separates source-map
    defects that must be repaired before a closeout run spends time extracting
    elaborated signatures from expected source-to-dashboard work that requires
    those rows. It cannot validate row links or semantic theorem fidelity;
    callers must still run the full paper-coverage and source-to-Lean checks
    after refreshing the cache.
    """

    full_inventory, inventory, mode, mode_error = paper_coverage_inventory(folder)
    statement_map_payload = paper_statement_map_payload(folder)
    deep_attestation_error = deep_source_coverage_attestation_error(
        statement_map_payload, mode
    )
    raw_map_items = statement_map_payload.get("items")
    presentation_aliases, _presentation_alias_errors = source_presentation_aliases(
        raw_map_items
    )
    coverage_state = _coverage_binding_freshness(
        folder,
        full_inventory,
        inventory,
        mode,
        statement_map_payload,
        presentation_aliases=presentation_aliases,
    )
    audit = coverage_state.audit
    audit_items = coverage_state.audit_items
    coverage_item_bindings = coverage_state.coverage_item_bindings
    ambiguous_semantic_item_bindings = list(
        coverage_state.ambiguous_semantic_item_bindings
    )
    bound_audit_items = coverage_state.bound_audit_items
    audit_required = paper_coverage_audit_required(folder, inventory)
    mode_migration_error = source_coverage_mode_migration_error(
        statement_map_payload, require_explicit=audit_required
    )
    raw_source_map_errors = paper_source_map_structural_errors(folder)
    source_presentation_classification_errors = sorted(
        set(
            raw_source_map_errors
            if statement_map_payload
            else [
                f"{key}: {error}"
                for key, item in full_inventory.items()
                for error in source_item_scope_classification_errors(item)
            ]
        )
    )
    inventory_hash = coverage_state.inventory_hash
    recorded_inventory_hash = coverage_state.recorded_inventory_hash
    recorded_mode = coverage_state.recorded_mode
    mode_mismatch = coverage_state.mode_mismatch
    missing_coverage = list(coverage_state.missing_coverage)
    extra_coverage = list(coverage_state.extra_coverage)
    out_of_mode_coverage = list(coverage_state.out_of_mode_coverage)
    missing_statement_digest = list(coverage_state.missing_statement_digest)
    stale_statement = list(coverage_state.stale_statement)
    aggregate_current = coverage_state.aggregate_current
    source_artifact_current = coverage_state.source_artifact_current
    stale_source_items = list(coverage_state.stale_source_items)
    semantic_reuse_anchor_errors = coverage_state.semantic_reuse_anchor_errors
    unverified_reused_source_items = list(
        coverage_state.unverified_reused_source_items
    )
    legacy_unpinned_items = list(coverage_state.legacy_unpinned_items)
    missing_source_url = sorted(
        key
        for key, item in inventory.items()
        if _is_statement_map_source(item.get("source"))
        and not str(item.get("source_url") or "").strip()
    )
    missing_source_provenance = sorted(
        key
        for key, item in inventory.items()
        if _is_statement_map_source(item.get("source"))
        and not (
            str(item.get("source_location") or "").strip()
            or str(item.get("source_note") or "").strip()
            or str(item.get("source_status") or "").strip()
        )
    )
    unknown_source_kind = sorted(
        key
        for key, item in inventory.items()
        if _is_statement_map_source(item.get("source"))
        and str(item.get("source_kind") or "").strip()
        and str(item.get("source_kind") or "").strip().lower()
        not in KNOWN_SOURCE_PRESENTATION_KINDS
    )
    source_scope_classification_errors = (
        _source_scope_classification_errors(inventory, bound_audit_items)
        if mode == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
        else []
    )
    user_approved_scope_exclusion_errors = _user_approved_scope_exclusion_errors(
        inventory, bound_audit_items
    )
    def corrected_target_coverage_error_for(key: str) -> str:
        return _corrected_target_coverage_error(
            inventory[key],
            bound_audit_items[key],
            _normalize_paper_coverage_judgment(bound_audit_items[key].get("coverage")),
            source_inventory=full_inventory,
            paper_name=folder.name,
            semantic_contract_schema=statement_map_payload.get(
                "semantic_contract_schema"
            ),
        )

    corrected_target_coverage_errors = sorted(
        f"{key}: {error}"
        for key in inventory
        if key in bound_audit_items
        for error in [corrected_target_coverage_error_for(key)]
        if error
    )
    source_anchor_evidence_errors = _scoped_source_anchor_evidence_errors(folder)
    source_named_result_inventory_errors = _source_named_result_inventory_errors(
        folder
    )
    missing_inventory_digest = bool(
        audit_items
        and not recorded_inventory_hash
        and any(
            not _coverage_item_has_current_source_digest_schema(item)
            for item in bound_audit_items.values()
        )
    )
    # The aggregate digest is a discovery fallback for old unpinned rows, not
    # an independent semantic receipt. Additions/removals and mode drift are
    # already checked explicitly, while every modern row carries its own
    # source identity. Do not reopen those rows merely because their generated
    # aggregate container changed.
    aggregate_receipt_required = any(
        not _coverage_item_has_current_source_digest_schema(item)
        for item in bound_audit_items.values()
    )
    stale_inventory = bool(
        audit_items and not aggregate_current and aggregate_receipt_required
    )
    prompt_version_stale = bool(
        audit_items
        and str(audit.get("prompt_version") or "").strip()
        != REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION
    )
    metadata_missing = bool(audit_items and audit.get("metadata_missing"))
    source_grounded = audit.get("source_grounded") is True
    semantic_audit_kind = str(audit.get("audit_kind") or "").strip()
    audit_not_semantic = bool(
        audit_items
        and (
            semantic_audit_kind not in APPROVED_PAPER_COVERAGE_AUDIT_KINDS
            or not source_grounded
            or bool(audit.get("seed_scaffold"))
        )
    )
    missing_coverage_sidecar = bool(audit_required and not audit_items)

    # A cache refresh needs a well-formed source inventory, but it is often the
    # prerequisite for the semantic source-to-dashboard judgment itself. Keep
    # these categories separate so a blank or intentionally fail-closed
    # scaffold does not instruct users to complete the coverage audit before
    # the current dashboard rows exist.
    pre_manifest_blockers: list[str] = []
    if mode_error:
        pre_manifest_blockers.append("source coverage mode is invalid")
    if mode_migration_error:
        pre_manifest_blockers.append("source coverage mode migration is incomplete")
    if deep_attestation_error:
        pre_manifest_blockers.append("deep source-coverage attestation is invalid")
    if source_presentation_classification_errors:
        pre_manifest_blockers.append(
            f"{len(source_presentation_classification_errors)} source-map structural/classification error(s)"
        )
    if source_named_result_inventory_errors:
        pre_manifest_blockers.append(
            f"{len(source_named_result_inventory_errors)} named-result inventory reconciliation error(s)"
        )
    if missing_source_url:
        pre_manifest_blockers.append(
            f"{len(missing_source_url)} source item(s) lack source URLs"
        )
    if missing_source_provenance:
        pre_manifest_blockers.append(
            f"{len(missing_source_provenance)} source item(s) lack source provenance"
        )
    if unknown_source_kind:
        pre_manifest_blockers.append(
            f"{len(unknown_source_kind)} source item(s) use unknown source_kind values"
        )
    if source_scope_classification_errors:
        pre_manifest_blockers.append(
            f"{len(source_scope_classification_errors)} source-scope classification error(s)"
        )
    if source_anchor_evidence_errors:
        pre_manifest_blockers.append(
            f"{len(source_anchor_evidence_errors)} source-anchor evidence error(s)"
        )

    semantic_coverage_pending: list[str] = []
    if audit_required:
        if missing_coverage_sidecar:
            semantic_coverage_pending.append("missing paper_coverage_llm.json")
        if missing_coverage:
            semantic_coverage_pending.append(
                f"{len(missing_coverage)} source item(s) missing coverage entries"
            )
        if extra_coverage:
            semantic_coverage_pending.append(
                f"{len(extra_coverage)} coverage entries have no source-map item"
            )
        if missing_statement_digest:
            semantic_coverage_pending.append(
                f"{len(missing_statement_digest)} coverage item(s) lack source-statement digests"
            )
        if stale_statement:
            semantic_coverage_pending.append(
                f"{len(stale_statement)} coverage source-statement digest(s) are stale"
            )
        if missing_inventory_digest:
            semantic_coverage_pending.append("coverage sidecar lacks its inventory digest")
        if stale_inventory:
            semantic_coverage_pending.append("coverage sidecar inventory digest is stale")
        if stale_source_items:
            semantic_coverage_pending.append(
                f"{len(stale_source_items)} source-item coverage receipt(s) are stale"
            )
        if unverified_reused_source_items:
            semantic_coverage_pending.append(
                f"{len(unverified_reused_source_items)} reused coverage item(s) lack current source-anchor verification"
            )
        if legacy_unpinned_items:
            semantic_coverage_pending.append(
                f"{len(legacy_unpinned_items)} legacy coverage item(s) need source pins"
            )
        if mode_mismatch:
            semantic_coverage_pending.append("coverage sidecar uses a different source-coverage mode")
        if ambiguous_semantic_item_bindings:
            semantic_coverage_pending.append(
                f"{len(ambiguous_semantic_item_bindings)} ambiguous source-to-coverage bindings"
            )
        if user_approved_scope_exclusion_errors:
            semantic_coverage_pending.append(
                f"{len(user_approved_scope_exclusion_errors)} invalid user-approved scope exclusion(s)"
            )
        if corrected_target_coverage_errors:
            semantic_coverage_pending.append(
                f"{len(corrected_target_coverage_errors)} corrected-target coverage error(s)"
            )
        if prompt_version_stale:
            semantic_coverage_pending.append("coverage prompt version is stale")
        if metadata_missing:
            semantic_coverage_pending.append("coverage sidecar lacks validator/timestamp metadata")
        if audit_not_semantic:
            semantic_coverage_pending.append(
                "coverage sidecar is not a source-grounded semantic audit"
            )

    needs_attention = bool(
        mode_error
        or mode_migration_error
        or deep_attestation_error
        or source_presentation_classification_errors
        or ambiguous_semantic_item_bindings
        or source_named_result_inventory_errors
        or (
            audit_required
            and (
            missing_coverage_sidecar
            or missing_coverage
            or extra_coverage
            or missing_statement_digest
            or stale_statement
            or missing_inventory_digest
            or stale_source_items
            or unverified_reused_source_items
            or legacy_unpinned_items
            or mode_mismatch
            or missing_source_url
            or missing_source_provenance
            or unknown_source_kind
            or source_scope_classification_errors
            or user_approved_scope_exclusion_errors
            or corrected_target_coverage_errors
            or source_anchor_evidence_errors
            or prompt_version_stale
            or metadata_missing
            or audit_not_semantic
            )
        )
    )
    return {
        "paper": folder.name,
        "audit_required": audit_required,
        "source_coverage_mode": mode,
        "source_coverage_mode_error": mode_error,
        "source_coverage_mode_migration_error": mode_migration_error,
        "deep_source_coverage_attestation_error": deep_attestation_error,
        "full_inventory_count": len(full_inventory),
        "inventory_count": len(inventory),
        "coverage_item_count": len(audit_items),
        "paper_statement_inventory_sha256": inventory_hash,
        "recorded_paper_statement_inventory_sha256": recorded_inventory_hash,
        "recorded_source_coverage_mode": recorded_mode,
        "source_coverage_mode_mismatch": mode_mismatch,
        "source_artifact_current": source_artifact_current,
        "missing_coverage_sidecar": missing_coverage_sidecar,
        "missing_coverage": missing_coverage,
        "extra_coverage": extra_coverage,
        "out_of_mode_coverage": out_of_mode_coverage,
        "missing_statement_digest": missing_statement_digest,
        "stale_statement": stale_statement,
        "stale_source_items": stale_source_items,
        "unverified_reused_source_items": unverified_reused_source_items,
        "semantic_reuse_source_anchor_errors": semantic_reuse_anchor_errors,
        "legacy_unpinned_items": legacy_unpinned_items,
        "missing_inventory_digest": missing_inventory_digest,
        "stale_inventory": stale_inventory,
        "missing_source_url": missing_source_url,
        "missing_source_provenance": missing_source_provenance,
        "unknown_source_kind": unknown_source_kind,
        "source_scope_classification_errors": source_scope_classification_errors,
        "source_presentation_classification_errors": source_presentation_classification_errors,
        "source_map_structural_error_count": len(raw_source_map_errors),
        "semantic_item_rebinding_count": sum(
            source_key != audit_key
            for source_key, audit_key in coverage_item_bindings.items()
        ),
        "ambiguous_semantic_item_bindings": ambiguous_semantic_item_bindings,
        "user_approved_scope_exclusion_errors": user_approved_scope_exclusion_errors,
        "corrected_target_coverage_errors": corrected_target_coverage_errors,
        "source_anchor_evidence_errors": source_anchor_evidence_errors,
        "source_named_result_inventory_errors": source_named_result_inventory_errors,
        "source_named_result_inventory_error_count": len(
            source_named_result_inventory_errors
        ),
        "prompt_version_stale": prompt_version_stale,
        "metadata_missing": metadata_missing,
        "audit_not_semantic": audit_not_semantic,
        "pre_manifest_blockers": pre_manifest_blockers,
        "pre_manifest_blocked": bool(pre_manifest_blockers),
        "semantic_coverage_pending": semantic_coverage_pending,
        "needs_attention": needs_attention,
    }
LEAN_PROOF_DECLARATION_KINDS = {"theorem", "lemma"}
LEAN_SPECIFICATION_DECLARATION_KINDS = {"definition"}
SOURCE_REVIEW_TARGET_RE = re.compile(
    r"\b(definition|example|remark|proposition|theorem|corollary|lemma)\b",
    re.IGNORECASE,
)
SOURCE_APPENDIX_RE = re.compile(r"\bappendix\b", re.IGNORECASE)
SOURCE_NON_TARGET_REASONS = (
    "not a separate",
    "not an independent",
    "not a standalone",
    "proof-only",
    "proof step",
    "proof detail",
    "section heading",
    "background",
    "bibliographic",
    "notation-only",
    "purely notational",
    "duplicate restatement",
)


def _source_inventory_item_is_named_claim(key: str, item: dict[str, Any]) -> bool:
    """Compatibility wrapper for the shared source-only claim classifier."""

    del key  # Map keys are navigation metadata, not semantic source evidence.
    return _shared_source_inventory_item_is_named_claim(item)


def _source_inventory_item_scope_classification_error(item: dict[str, Any]) -> str:
    """Compatibility wrapper for shared source-only scope policy."""

    return _shared_source_inventory_item_scope_classification_error(item)


def _source_inventory_item_user_approved_scope_exclusion_error(
    item: dict[str, Any],
) -> str:
    """Compatibility wrapper for shared source-only approval policy."""

    return _shared_source_inventory_item_user_approved_scope_exclusion_error(item)


def _source_inventory_item_is_catalogued_nonformal_observation(
    item: dict[str, Any],
) -> bool:
    """Return whether a source item is an explicitly non-theorem observation.

    This is intentionally driven only by source-curated fields and literal source
    presentation.  A numerical figure, experiment, or simulation does not gain
    theorem scope merely because a Lean helper has a theorem-shaped name.  The
    inverse safeguard matters just as much: a source theorem/proposition/etc.
    cannot escape review by setting ``claim_bearing: false``.
    """

    classification = str(item.get("source_scope_classification") or "").strip().lower()
    return (
        classification
        in {
            NON_NAMED_COMPUTATIONAL_ILLUSTRATION,
            SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION,
        }
        and not _source_inventory_item_scope_classification_error(item)
    )


def _source_scope_classification_errors(
    inventory: dict[str, dict[str, Any]], audit_items: dict[str, Any]
) -> list[str]:
    """Validate source-only scope lanes and reject any Lean coverage credit."""

    out_of_scope_coverage = {
        "out_of_scope",
        "not_a_paper_target",
        "not_a_theorem_statement",
    }
    errors: list[str] = []
    for key, item in inventory.items():
        error = _source_inventory_item_scope_classification_error(item)
        if error:
            errors.append(f"{key}: {error}")
            continue
        if not _source_inventory_item_is_catalogued_nonformal_observation(item):
            continue
        classification = str(
            item.get("source_scope_classification") or ""
        ).strip().lower()
        coverage_item = audit_items.get(key)
        if not isinstance(coverage_item, dict):
            errors.append(
                f"{key}: {classification} requires an explicit "
                "out-of-theorem-scope coverage judgment"
            )
            continue
        coverage = _normalize_paper_coverage_judgment(coverage_item.get("coverage"))
        if coverage not in out_of_scope_coverage:
            errors.append(
                f"{key}: {classification} must use an explicit "
                "out-of-theorem-scope coverage judgment"
            )
        source_quote, quote_error = _source_inventory_anchor_quote_text(item)
        if quote_error:
            # The item-level classifier emits the more precise evidence error;
            # do not invent a digest for untrusted or incomplete quote data.
            continue
        expected_quote_digest = hashlib.sha256(
            source_quote.encode("utf-8")
        ).hexdigest()
        scope_judgment = str(
            coverage_item.get("source_scope_judgment") or ""
        ).strip().lower()
        expected_scope_judgment = (
            "finite_nonclaim_observation"
            if classification == NON_NAMED_COMPUTATIONAL_ILLUSTRATION
            else SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION
        )
        if scope_judgment != expected_scope_judgment:
            errors.append(
                f"{key}: {classification} requires the independent "
                f"source_scope_judgment `{expected_scope_judgment}`"
            )
        if str(coverage_item.get("source_anchor_quote_sha256") or "").strip().lower() != expected_quote_digest:
            errors.append(
                f"{key}: {classification} coverage must pin "
                "source_anchor_quote_sha256 to the byte-verified anchor quote"
            )
        rows = _normalize_string_list(coverage_item.get("review_rows"))
        support = _normalize_string_list(coverage_item.get("support_declarations"))
        row_signature_pins = coverage_item.get("review_row_signature_sha256")
        if rows or row_signature_pins:
            errors.append(
                f"{key}: {classification} cannot claim review_rows or review-row "
                "signature pins"
            )
        if support:
            errors.append(
                f"{key}: {classification} cannot claim support_declarations"
            )
    return sorted(errors)


def _user_approved_scope_exclusion_errors(
    inventory: dict[str, dict[str, Any]], audit_items: dict[str, Any]
) -> list[str]:
    """Validate the separate explicit-user source-claim exclusion lane.

    A valid record is a visible source claim plus an auditable scope decision.
    It must not use the computational-observation classification, must not
    carry Lean rows as proof credit, and must be represented by the dedicated
    coverage verdict.  All routing is driven by structured source evidence,
    not identifiers or declaration names.
    """

    errors: list[str] = []
    for key, item in inventory.items():
        raw_approval = item.get(USER_APPROVED_SCOPE_EXCLUSION)
        coverage_item = audit_items.get(key)
        coverage = (
            _normalize_paper_coverage_judgment(coverage_item.get("coverage"))
            if isinstance(coverage_item, dict)
            else ""
        )
        if raw_approval is not None:
            error = _source_inventory_item_user_approved_scope_exclusion_error(item)
            if error:
                errors.append(f"{key}: {error}")
            if coverage != USER_APPROVED_SCOPE_EXCLUSION:
                errors.append(
                    f"{key}: user_approved_scope_exclusion requires the explicit "
                    "user_approved_scope_exclusion coverage judgment"
                )
        if coverage != USER_APPROVED_SCOPE_EXCLUSION:
            continue
        if raw_approval is None:
            errors.append(
                f"{key}: user_approved_scope_exclusion coverage requires structured "
                "user_approved_scope_exclusion metadata in the source map"
            )
            continue
        rows = _normalize_string_list(coverage_item.get("review_rows"))
        support = _normalize_string_list(coverage_item.get("support_declarations"))
        if rows:
            errors.append(
                f"{key}: user_approved_scope_exclusion cannot claim review_rows"
            )
        if support:
            errors.append(
                f"{key}: user_approved_scope_exclusion cannot claim support_declarations"
            )
    return sorted(set(errors))


def _scoped_source_anchor_evidence_errors(folder: Path) -> list[str]:
    """Return byte-validation failures on the active semantic source surface.

    The classifier above only consumes structured quote records.  Invoke the
    shared integrity gate here as well, so a dashboard/precheck cannot report a
    scoped row clean until those records are proved to be exact slices of the
    pinned source bytes.  Project the map before invoking that gate: a normal
    named-theory audit must validate its selected theorem/definition surface
    (and explicit correction or exclusion obligations), without silently
    turning an unanchored deep-only formula, caption, or algorithm into a
    normal closeout blocker.  Deep mode projects the whole source inventory.
    """

    map_path = folder / PAPER_STATEMENT_MAP_FILE
    if not _dashboard_is_file(map_path):
        return []
    payload = _dashboard_json_payload(map_path)
    if payload is None:
        return []
    if not isinstance(payload, dict):
        return []
    try:
        from scripts.audit_evidence_integrity import (
            scoped_source_map_payload,
            source_anchor_evidence_findings,
        )
        mode, _mode_error = source_coverage_mode_from_map(payload)
        scoped_payload, _scoped_items = scoped_source_map_payload(
            payload,
            mode,
            folder=folder,
            repository_root=ROOT,
        )
        findings = source_anchor_evidence_findings(
            folder,
            "formalized",
            map_path,
            scoped_payload,
            file_bytes_override=_dashboard_file_bytes_override(),
        )
    except Exception as error:  # noqa: BLE001 - evidence validation fails closed.
        return [f"source-anchor evidence validator failed: {error}"]
    return sorted(str(finding.message) for finding in findings)


def _source_named_result_inventory_errors(folder: Path) -> list[str]:
    """Return source-only named-result completeness failures for this paper.

    The dashboard uses this small shared integrity lane before it trusts a
    curated map as a complete ordinary source surface.  It is deliberately
    independent of review-row/map-key spelling and remains cheap compared with
    Lean signature extraction.
    """

    map_path = folder / PAPER_STATEMENT_MAP_FILE
    if not _dashboard_is_file(map_path):
        return []
    payload = _dashboard_json_payload(map_path)
    if payload is None:
        return []
    if not isinstance(payload, dict):
        return []
    status_payload = (
        _dashboard_json_payload(folder / DEFAULT_PAPER_STATUS_FILE) or {}
    )
    status = (
        str(status_payload.get("status") or "paper draft")
        if isinstance(status_payload, dict)
        else "paper draft"
    )
    try:
        from scripts.audit_evidence_integrity import source_named_result_inventory_findings
        findings = source_named_result_inventory_findings(
            folder,
            status,
            map_path,
            payload,
            file_bytes_override=_dashboard_file_bytes_override(),
        )
    except Exception as error:  # noqa: BLE001 - completeness fails closed.
        return [f"source named-result inventory validator failed: {error}"]
    return sorted({str(finding.message) for finding in findings})


def _semantic_reuse_source_anchor_errors(
    folder: Path, source_keys: Iterable[str]
) -> dict[str, list[str]]:
    """Byte-validate only source items proposed for per-item cache reuse.

    A semantic source digest can ignore unrelated changes to the source
    artifact only when the item itself has an exact, current source quote.
    This helper deliberately forces quote validation for the candidate subset
    even if the paper has not requested a full deep-paper anchor audit.
    """

    keys = sorted({str(key).strip() for key in source_keys if str(key).strip()})
    if not keys:
        return {}
    map_path = folder / PAPER_STATEMENT_MAP_FILE
    payload = _dashboard_json_payload(map_path)
    if payload is None:
        return {key: ["source map is unavailable for semantic item reuse"] for key in keys}
    if not isinstance(payload, dict) or not isinstance(payload.get("items"), dict):
        return {key: ["source map items are unavailable for semantic item reuse"] for key in keys}
    raw_items = payload["items"]
    selected: dict[str, Any] = {}
    errors: dict[str, list[str]] = {}
    for key in keys:
        raw_item = raw_items.get(key)
        if not isinstance(raw_item, dict):
            errors[key] = ["current source item is unavailable for semantic item reuse"]
        else:
            selected[key] = raw_item
    if not selected:
        return errors

    scoped_payload = dict(payload)
    scoped_payload["items"] = selected
    # This is a narrow cache-freshness requirement, not a request to audit
    # captions/prose.  Each selected item must nevertheless prove its source
    # quote against the current canonical bytes before its old judgment moves.
    scoped_payload["source_anchor_evidence_required"] = True
    try:
        from scripts.audit_evidence_integrity import source_anchor_evidence_findings
        findings = source_anchor_evidence_findings(
            folder,
            "formalized",
            map_path,
            scoped_payload,
            file_bytes_override=_dashboard_file_bytes_override(),
        )
    except Exception as error:  # noqa: BLE001 - freshness must fail closed.
        message = f"source-anchor reuse validator failed: {error}"
        return {
            key: [message]
            for key in keys
            if key not in errors
        } | errors

    for finding in findings:
        message = str(finding.message)
        matched = [
            key
            for key in selected
            if message.startswith(f"items.{key}.")
            or message.startswith(f"items.{key}:")
        ]
        # Artifact/payload failures have no item prefix and therefore make all
        # proposed semantic reuse unsafe, rather than attributing a global
        # source-byte failure to an arbitrary item.
        for key in matched or list(selected):
            errors.setdefault(key, []).append(message)
    return {key: sorted(set(messages)) for key, messages in errors.items()}


def _source_inventory_item_requires_proof_evidence(
    key: str, item: dict[str, Any]
) -> bool:
    """Compatibility wrapper for the shared source-only proof boundary."""

    del key  # Map keys are navigation metadata, not semantic source evidence.
    return _shared_source_inventory_item_requires_proof_evidence(item)


def _source_inventory_item_is_quarantined_defect(item: dict[str, Any]) -> bool:
    """Return whether the source result is explicitly quarantined as defective."""

    return bool(source_item_effective_route_policy(item)["is_quarantined_source_defect"])


def _review_item_declaration_kind(item: ReviewItem) -> str:
    """Return the declaration kind, preferring the elaborated Lean manifest."""

    manifest = item.lean_signature_manifest
    if isinstance(manifest, dict) and manifest.get("schema") == 2:
        manifest_kind = str(manifest.get("declaration_kind") or "").strip().lower()
        if manifest_kind:
            return manifest_kind
    syntactic_kind = str(item.kind or "").strip().lower()
    if syntactic_kind in {"def", "abbrev"}:
        return "definition"
    return syntactic_kind


SOURCE_PROOF_DEFECT_SNAPSHOT_FIELDS = (
    "id",
    "source_locator",
    "source_claim",
    "defect_kind",
    "affected_source_locators",
    "statement_impact",
    "repair_obligation",
    "acceptance_condition",
    "resolution",
    "resolution_evidence",
)


def source_proof_defect_snapshot(defect: dict[str, Any]) -> dict[str, Any]:
    """Return the exact semantic defect record frozen by support judgments."""

    return {field: defect.get(field) for field in SOURCE_PROOF_DEFECT_SNAPSHOT_FIELDS}


def source_proof_defect_digest(defect: dict[str, Any]) -> str:
    """Hash the source-located mathematics of one validated defect record."""

    encoded = json.dumps(
        source_proof_defect_snapshot(defect),
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _validated_source_proof_defects(folder: Path) -> dict[str, dict[str, Any]]:
    """Return exact records from a fully validated configured defect ledger.

    Quarantine support is a release-relevant claim about a defect in the source,
    so merely finding the same identifier in an arbitrary JSON file is not
    sufficient.  The configured ledger must have completed its defect review and
    pass the source-proof fidelity validator, including source-artifact pins and
    source-located mathematical obligations.
    """

    status_payload = _dashboard_json_payload(folder / DEFAULT_PAPER_STATUS_FILE)
    if not isinstance(status_payload, dict):
        return {}
    ledger_path: Path | None = None
    ledger_error = ""
    try:
        from scripts.audit_evidence_integrity import (
            source_proof_fidelity_config,
            source_proof_fidelity_findings,
            source_proof_fidelity_ledger_path,
        )
        if source_proof_fidelity_config(status_payload) is None:
            return {}
        ledger_path, ledger_error = source_proof_fidelity_ledger_path(folder, status_payload)
        status = str(status_payload.get("status") or "not formalized").strip()
        if source_proof_fidelity_findings(
            folder,
            status,
            status_payload,
            file_bytes_override=_dashboard_file_bytes_override(),
        ):
            return {}
    except Exception:  # noqa: BLE001 - unavailable validation fails closed.
        return {}
    if ledger_error:
        return {}
    if ledger_path is None:
        return {}
    payload = _dashboard_json_payload(ledger_path)
    if payload is None:
        return {}
    if not isinstance(payload, dict) or payload.get("review_status") != "defects_recorded":
        return {}
    raw_defects = payload.get("defects") if isinstance(payload, dict) else None
    if not isinstance(raw_defects, list):
        return {}
    return {
        str(defect.get("id") or "").strip(): defect
        for defect in raw_defects
        if isinstance(defect, dict) and str(defect.get("id") or "").strip()
    }


def _canonical_application(canonical: Any) -> tuple[Any, list[Any]]:
    """Flatten the canonical Lean application spine for tautology checks."""

    arguments: list[Any] = []
    current = canonical
    while isinstance(current, dict) and current.get("tag") == "app":
        arguments.append(current.get("arg"))
        current = current.get("fn")
    arguments.reverse()
    return current, arguments


def _review_item_has_trivial_support_conclusion(item: ReviewItem) -> bool:
    """Reject mechanically obvious tautologies as defect-support evidence."""

    manifest = item.lean_signature_manifest
    if not isinstance(manifest, dict) or manifest.get("schema") != 2:
        return True
    atoms = manifest.get("atoms")
    if not isinstance(atoms, list) or not atoms:
        return True
    conclusions = [
        atom for atom in atoms
        if isinstance(atom, dict) and str(atom.get("role") or "").strip() == "conclusion"
    ]
    if not conclusions:
        return True
    for atom in conclusions:
        canonical = atom.get("canonical")
        display = re.sub(r"\s+", "", str(atom.get("display") or ""))
        if display in {"True", "True.intro"}:
            return True
        head, arguments = _canonical_application(canonical)
        head_name = str(head.get("name") or "") if isinstance(head, dict) else ""
        if head_name == "True" and not arguments:
            return True
        if head_name in {"Eq", "Iff"} and len(arguments) >= 2:
            left = arguments[-2]
            right = arguments[-1]
            if left == right:
                return True
    return False


def defect_support_judgment_error(
    raw: Any,
    *,
    source_key: str,
    source_item: dict[str, Any],
    defect: dict[str, Any],
    support_declaration: str,
    row_item: ReviewItem,
) -> str:
    """Validate one exact semantic defect-to-Lean support judgment."""

    if not isinstance(raw, dict):
        return "judgment row is not an object"

    def required_string(key: str) -> str:
        value = raw.get(key)
        return value.strip() if isinstance(value, str) else ""

    if required_string("source_item") != source_key:
        return "source_item does not match the canonical source inventory key"
    source_statement = str(source_item.get("statement") or "")
    expected_source_digest = statement_digest(source_statement)
    if required_string("source_statement_sha256") != expected_source_digest:
        return "source statement digest is missing or stale"
    defect_id = str(defect.get("id") or "").strip()
    if required_string("defect_id") != defect_id:
        return "defect_id does not match the validated source-proof defect"
    expected_snapshot = source_proof_defect_snapshot(defect)
    if raw.get("source_defect") != expected_snapshot:
        return "source_defect snapshot is missing or stale"
    if required_string("source_defect_sha256") != source_proof_defect_digest(defect):
        return "source defect digest is missing or stale"
    if required_string("support_declaration") != support_declaration:
        return "support_declaration does not match the routed review row"

    lean_statement = str(row_item.lean_statement or "")
    if raw.get("lean_statement") != lean_statement:
        return "exact Lean statement is missing or stale"
    if required_string("lean_statement_sha256") != statement_digest(lean_statement):
        return "Lean statement digest is missing or stale"

    manifest = row_item.lean_signature_manifest
    if not isinstance(manifest, dict):
        return "Lean declaration manifest is unavailable"
    manifest_digest = str(manifest.get("sha256") or "").strip()
    if not manifest_digest or signature_manifest_digest(manifest) != manifest_digest:
        return "Lean declaration manifest has no valid canonical digest"
    if required_string("lean_signature_sha256") != manifest_digest:
        return "Lean declaration manifest digest is missing or stale"
    if _review_item_has_trivial_support_conclusion(row_item):
        return "Lean support conclusion is a trivial or reflexive tautology"

    judgment = required_string("judgment").lower()
    if judgment not in APPROVED_DEFECT_SUPPORT_JUDGMENTS:
        return "judgment is not a positive counterexample/refutation verdict"
    reason = required_string("reason")
    if len(reason) < 20 or NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(reason):
        return "judgment reason is missing, too short, or name-based"

    manifest_atoms = manifest.get("atoms")
    if not isinstance(manifest_atoms, list) or not manifest_atoms:
        return "Lean declaration manifest has no semantic atoms"
    manifest_index: dict[str, tuple[str, str]] = {}
    for atom in manifest_atoms:
        if not isinstance(atom, dict):
            return "Lean declaration manifest contains a malformed atom"
        ref = str(atom.get("ref") or "").strip()
        role = str(atom.get("role") or "").strip().lower()
        digest = signature_manifest_atom_digest(atom)
        if not ref or ref in manifest_index or role not in {
            "parameter", "assumption", "conclusion"
        } or not digest:
            return "Lean declaration manifest contains an invalid semantic atom"
        manifest_index[ref] = (role, digest)

    obligations = raw.get("lean_obligations")
    if not isinstance(obligations, list):
        return "missing lean_obligations list"
    obligation_refs: set[str] = set()
    permitted_relevance = {
        "parameter": {"witness_parameter", "source_model_parameter", "universal_parameter"},
        "assumption": {"source_model_condition", "proved_counterexample_fact"},
        "conclusion": {"counterexample_conclusion", "refutation_conclusion"},
    }
    expected_conclusion_relevance = (
        "counterexample_conclusion"
        if judgment == "valid_counterexample"
        else "refutation_conclusion"
    )
    for obligation in obligations:
        if not isinstance(obligation, dict):
            return "Lean obligation is not an object"
        ref = str(obligation.get("signature_ref") or "").strip()
        if ref not in manifest_index or ref in obligation_refs:
            return "Lean obligation references an unknown or duplicate signature atom"
        role, atom_digest = manifest_index[ref]
        if str(obligation.get("role") or "").strip().lower() != role:
            return f"Lean obligation `{ref}` has the wrong semantic role"
        if str(obligation.get("signature_atom_sha256") or "").strip() != atom_digest:
            return f"Lean obligation `{ref}` has a stale atom digest"
        relevance = str(obligation.get("defect_relevance") or "").strip().lower()
        if relevance not in permitted_relevance[role]:
            return f"Lean obligation `{ref}` has an invalid defect_relevance"
        if role == "conclusion" and relevance != expected_conclusion_relevance:
            return f"Lean conclusion `{ref}` does not match the positive judgment kind"
        explanation = str(obligation.get("semantic_explanation") or "").strip()
        if len(explanation) < 20 or NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(explanation):
            return f"Lean obligation `{ref}` lacks a substantive semantic explanation"
        obligation_refs.add(ref)
    if obligation_refs != set(manifest_index):
        return "Lean obligations do not exactly partition the declaration manifest"

    alignment = raw.get("obligation_alignment")
    if not isinstance(alignment, list) or not alignment:
        return "missing obligation_alignment list"
    aligned_refs: set[str] = set()
    has_claim_conclusion = False
    source_fields = set(SOURCE_PROOF_DEFECT_SNAPSHOT_FIELDS) - {
        "id", "defect_kind", "statement_impact", "resolution"
    }
    expected_relation = DEFECT_SUPPORT_JUDGMENT_RELATIONS[judgment]
    for entry in alignment:
        if not isinstance(entry, dict):
            return "obligation alignment entry is not an object"
        source_field = str(entry.get("source_defect_field") or "").strip()
        lean_ref = str(entry.get("lean_signature_ref") or "").strip()
        relation = str(entry.get("relation") or "").strip().lower()
        if source_field not in source_fields or lean_ref not in manifest_index:
            return "obligation alignment references an unknown defect field or Lean atom"
        role = manifest_index[lean_ref][0]
        if role == "conclusion":
            if relation != expected_relation:
                return "Lean conclusion alignment has the wrong defect relation"
            if source_field == "source_claim":
                has_claim_conclusion = True
        elif relation not in {"instantiates", "satisfies", "derived_from"}:
            return "Lean input alignment has an invalid defect relation"
        basis = str(entry.get("semantic_basis") or "").strip()
        witness = str(entry.get("witness_or_derivation") or "").strip()
        if (
            len(basis) < 20
            or len(witness) < 20
            or NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(basis)
            or NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(witness)
        ):
            return "obligation alignment lacks substantive semantic evidence"
        aligned_refs.add(lean_ref)
    if aligned_refs != set(manifest_index):
        return "obligation alignment does not account for every Lean semantic atom"
    if not has_claim_conclusion:
        return "no Lean conclusion is aligned to the exact source defect claim"
    return ""


def _source_inventory_search_text(key: str, item: dict[str, Any]) -> str:
    """Compatibility wrapper for shared source-only presentation text."""

    del key  # Source-map keys and Lean aliases must not drive semantic routing.
    return _shared_source_inventory_search_text(item)


def _source_inventory_item_is_explicit_proof_support(item: dict[str, Any]) -> bool:
    """Return whether an item is an auditable proof-support record.

    This is deliberately narrower than the generic ``support_only`` route.
    A named intermediate proposition can be essential evidence about a printed
    proof while not being a separate claim on the paper's human-review surface.
    It may take that lane only when the source map says so explicitly and
    names the transparent, proof-routed source result that owns the route.
    The coverage ledger independently checks that that ownership is current.
    """

    if not source_item_effective_route_policy(item)["is_support_only"]:
        return False
    if str(item.get("inventory_role") or "").strip() != "proof_support":
        return False
    if str(item.get("source_kind") or "").strip().lower() not in SOURCE_RESULT_KINDS:
        return False
    return bool(_normalize_string_list(item.get("support_lean_declarations")))


def _proof_support_declaration_names(value: Any) -> list[str]:
    """Normalize configured FQNs to the dashboard's reviewed declaration names."""

    return [
        declaration.rsplit(".", 1)[-1]
        for declaration in _normalize_string_list(value)
    ]


def _proof_support_coverage_error(
    source_item: dict[str, Any],
    coverage_item: dict[str, Any],
    row_items: dict[str, ReviewItem],
) -> str:
    """Return an error unless a support-only item names exact proof-routed Specs.

    This validation is intentionally separate from direct source-to-Spec
    coverage.  It keeps proof-support material byte-pinned and reviewable,
    while preventing it from earning a second paper-claim row or disguising a
    support declaration that points only to a wrapper or implementation helper.
    """

    configured = _proof_support_declaration_names(
        source_item.get("support_lean_declarations")
    )
    recorded = _normalize_string_list(coverage_item.get("support_declarations"))
    if not configured:
        return "proof-support source item has no configured support declaration"
    if len(set(configured)) != len(configured):
        return "configured proof-support declarations are duplicated"
    if len(set(recorded)) != len(recorded):
        return "recorded proof-support declarations are duplicated"
    if set(recorded) != set(configured):
        return "recorded support declarations do not exactly match the source-map proof-support route"
    for declaration in configured:
        row_item = row_items.get(declaration)
        if row_item is None:
            return f"proof-support declaration {declaration} is absent from the current review surface"
        if not row_item.is_proposition_spec:
            return f"proof-support declaration {declaration} is not a transparent proposition Spec"
        if row_item.proposition_spec_role != "proof_routed":
            return f"proof-support declaration {declaration} is not a proof-routed source result"
        if not str(row_item.proposition_spec_proof or "").strip():
            return f"proof-support declaration {declaration} has no paired proof endpoint"
    return ""


def _source_inventory_item_requires_review_row(key: str, item: dict[str, Any]) -> bool:
    """Return whether source-visible material must be represented by dashboard row(s).

    The paper-coverage inventory is source first: a compact dashboard is useful,
    but it must not hide named source material from row-local LLM-as-judge review.
    Main-text definitions, examples, remarks, propositions, theorems, corollaries,
    and lemmas are required review targets. Appendix theorems/corollaries are also
    required. Appendix lemmas remain a judgment call unless a paper marks them as
    active targets elsewhere in the inventory.
    """

    if _source_inventory_item_is_catalogued_nonformal_observation(item):
        return False
    if _source_inventory_item_is_explicit_proof_support(item):
        # The separate coverage lane below still requires a byte-pinned source
        # record, an explicit route to a transparent proof-routed Spec, and a
        # current source-to-Lean audit of that enclosing claim.  The support
        # item is not itself another human-facing paper claim.
        return False
    # An attempted exception is not an exception until every source-facing
    # condition above validates.  Otherwise a malformed pin or mislabeled
    # figure could disappear merely because its prose lacks a theorem keyword.
    if str(item.get("source_scope_classification") or "").strip():
        return True
    text = _source_inventory_search_text(key, item)
    if _source_inventory_item_is_named_algorithm_block(item):
        return True
    if _source_text_has_general_computational_claim(text):
        return True
    if _source_text_has_general_result_assertion(text):
        return True
    if _source_inventory_item_requires_proof_evidence(key, item):
        return True
    source_kind = str(item.get("source_kind") or "").strip().lower()
    # A statement-map example/remark is review-visible by default.  The only
    # computational-outcome exception is the validated source-facing lane
    # returned above; otherwise an arbitrary map classification could suppress
    # a claim without source evidence or a canonical artifact pin.
    if (
        _is_statement_map_source(item.get("source"))
        and source_kind in SOURCE_CATALOGUED_NONFORMAL_OBSERVATION_KINDS
    ):
        return True
    if source_item_effective_route_policy(item)[
        "external_support_only_vocabulary"
    ]:
        return False
    if source_kind in SOURCE_DEFINITION_SEMANTIC_KINDS:
        return True
    lowered = text.lower()
    if any(reason in lowered for reason in SOURCE_NON_TARGET_REASONS):
        return False
    match = SOURCE_REVIEW_TARGET_RE.search(text)
    if not match:
        return _source_inventory_item_is_named_claim(key, item)
    label = match.group(1).lower()
    in_appendix = bool(SOURCE_APPENDIX_RE.search(text))
    if in_appendix and label == "lemma":
        return False
    return True


def _coverage_link_label(source_key: str, row_name: str) -> str:
    return f"{source_key} -> {row_name}"


def _coverage_review_row_signature_errors(
    source_key: str,
    rows: list[str],
    raw_pins: Any,
    row_items: dict[str, ReviewItem],
    *,
    current_signature_by_row: Mapping[str, str],
) -> list[str]:
    """Return failures for the elaborated-signature binding of one coverage link.

    A source-to-Lean coverage judgment is about the exact elaborated theorem
    type the reviewer inspected.  A declaration name or source route can find
    that theorem, but neither survives an unrecorded change to its normalized
    binders, premises, or conclusion.  Require an exact map from every linked
    row to the current canonical manifest digest.
    """

    if not rows:
        # The caller separately reports a direct coverage item with no rows.
        return []
    pins = _normalize_review_row_signature_pins(raw_pins)
    if pins is None:
        return [
            f"{source_key}: missing or malformed review_row_signature_sha256 map"
        ]

    errors: list[str] = []
    if len(set(rows)) != len(rows):
        errors.append(f"{source_key}: review_rows contains duplicate row names")
    if set(pins) != set(rows):
        errors.append(
            f"{source_key}: review_row_signature_sha256 keys do not exactly match review_rows"
        )

    for row_name in sorted(set(rows)):
        row_item = row_items.get(row_name)
        if row_item is None:
            # `invalid_row_links` gives the primary diagnosis for an absent row.
            continue
        current_digest = str(current_signature_by_row.get(row_name) or "")
        if not current_digest:
            errors.append(
                f"{_coverage_link_label(source_key, row_name)}: current typed semantic-review target identity is unavailable or invalid"
            )
            continue
        if pins.get(row_name) != current_digest:
            errors.append(
                f"{_coverage_link_label(source_key, row_name)}: review-target semantic identity digest is missing or stale"
            )
    return errors


def _review_item_statement_audit_target_sha256(row_item: ReviewItem) -> str:
    """Return the current exact paper target reviewed by one row.

    Most rows review their displayed paper statement. A component-routed row
    can instead review one exact clause of an aggregate definition. Accept the
    narrower target only when the statement loader already validated that
    unique route, the judgment is current, and all entry-local pins agree.
    """

    displayed_target = statement_digest(row_item.paper_statement)
    if row_item.is_assumption or row_item.llm_match_stale:
        return displayed_target
    component_target = str(
        row_item.llm_match_component_target_sha256 or ""
    ).strip().lower()
    recorded_target = str(
        row_item.llm_match_paper_statement_sha256 or ""
    ).strip().lower()
    route_targets = [
        str(route.get("source_statement_sha256") or "").strip().lower()
        for route in row_item.llm_match_source_routes or []
        if isinstance(route, Mapping)
        and str(route.get("route_kind") or "").strip().lower()
        == "source_component"
    ]
    if (
        SOURCE_ARTIFACT_SHA256_RE.fullmatch(component_target)
        and component_target == recorded_target
        and route_targets == [component_target]
    ):
        return component_target
    return displayed_target


def _row_statement_match_record(
    source_key: str,
    source_item: dict[str, Any],
    coverage: str,
    row_name: str,
    row_item: ReviewItem,
) -> dict[str, Any]:
    """Return a compact JSON record linking source coverage to row-local LLM audit."""

    _source_statement, source_statement_sha256 = _source_item_coverage_statement(
        source_item
    )
    source_input, _source_input_bundle_sha256, source_input_error = (
        source_semantic_input_bundle(source_item)
    )
    if not source_input_error and source_input:
        source_statement_sha256 = statement_digest(source_input)
    row_paper_statement_sha256 = statement_digest(row_item.paper_statement)
    row_statement_audit_target_sha256 = (
        _review_item_statement_audit_target_sha256(row_item)
    )
    if row_item.is_assumption:
        correctness_lane = "assumption_provenance"
        judgment = str(row_item.llm_assumption_judgment or "").strip()
        resolution = ""
        stale = bool(row_item.llm_assumption_stale)
        source = str(row_item.llm_assumption_source or "")
        validator = str(row_item.llm_assumption_validator or "")
        validated_at = str(row_item.llm_assumption_validated_at or "")
        recorded_paper_statement_sha256 = str(
            row_item.llm_assumption_paper_statement_sha256 or ""
        ).strip()
        recorded_lean_statement_sha256 = str(
            row_item.llm_assumption_lean_statement_sha256 or ""
        ).strip()
        recorded_lean_signature_sha256 = ""
        recorded_tex_statement_sha256 = ""
    else:
        correctness_lane = "statement_match"
        judgment = str(row_item.llm_match_judgment or "").strip()
        resolution = _normalize_llm_match_resolution(row_item.llm_match_resolution)
        stale = bool(row_item.llm_match_stale)
        source = str(row_item.llm_match_source or "")
        validator = str(row_item.llm_match_validator or "")
        validated_at = str(row_item.llm_match_validated_at or "")
        recorded_paper_statement_sha256 = str(
            row_item.llm_match_paper_statement_sha256 or ""
        ).strip()
        recorded_lean_statement_sha256 = str(
            row_item.llm_match_lean_statement_sha256 or ""
        ).strip()
        recorded_lean_signature_sha256 = str(
            row_item.llm_match_lean_signature_sha256 or ""
        ).strip()
        recorded_tex_statement_sha256 = str(
            row_item.llm_match_tex_statement_sha256 or ""
        ).strip()
    assumption_judgment = str(row_item.llm_assumption_judgment or "").strip()
    return {
        "source_statement": source_key,
        "source_statement_sha256": source_statement_sha256,
        "review_row": row_name,
        "review_row_is_assumption": bool(row_item.is_assumption),
        "review_row_paper_statement_sha256": row_paper_statement_sha256,
        "review_row_statement_audit_target_sha256": (
            row_statement_audit_target_sha256
        ),
        "review_row_paper_statement_matches_source": bool(
            source_statement_sha256
            and source_statement_sha256 == row_statement_audit_target_sha256
        ),
        "coverage": coverage,
        "row_correctness_lane": correctness_lane,
        "row_correctness_judgment": judgment,
        "row_correctness_resolution": resolution,
        "row_correctness_stale": stale,
        "row_correctness_source": source,
        "row_correctness_validator": validator,
        "row_correctness_validated_at": validated_at,
        "row_correctness_paper_statement_sha256": recorded_paper_statement_sha256,
        "row_correctness_lean_statement_sha256": recorded_lean_statement_sha256,
        "row_correctness_lean_signature_sha256": recorded_lean_signature_sha256,
        "review_row_lean_signature_sha256": row_item.lean_signature_sha256,
        "row_correctness_tex_statement_sha256": recorded_tex_statement_sha256,
        "row_correctness_matches_review_row_statement": bool(
            recorded_paper_statement_sha256
            and recorded_paper_statement_sha256
            == row_statement_audit_target_sha256
        ),
        "row_assumption_provenance_judgment": assumption_judgment,
        "row_assumption_provenance_stale": bool(row_item.llm_assumption_stale),
        "row_assumption_provenance_source": str(row_item.llm_assumption_source or ""),
        "row_assumption_provenance_validator": str(row_item.llm_assumption_validator or ""),
        "row_assumption_provenance_validated_at": str(row_item.llm_assumption_validated_at or ""),
        "row_statement_match_judgment": judgment,
        "row_statement_match_resolution": resolution,
        "row_statement_match_stale": stale,
        "row_statement_match_source": source,
        "row_statement_match_validator": validator,
        "row_statement_match_validated_at": validated_at,
        "row_statement_match_paper_statement_sha256": recorded_paper_statement_sha256,
        "row_statement_match_lean_statement_sha256": recorded_lean_statement_sha256,
        "row_statement_match_tex_statement_sha256": recorded_tex_statement_sha256,
    }


def _current_schema2_review_manifest_error(item: ReviewItem) -> str:
    manifest = item.lean_signature_manifest
    if not isinstance(manifest, dict) or manifest.get("schema") != 2:
        return "has no schema-2 elaborated manifest"
    digest = str(manifest.get("sha256") or "").strip().lower()
    if not digest or signature_manifest_digest(manifest) != digest:
        return "has no valid canonical schema-2 manifest digest"
    if str(item.lean_signature_sha256 or "").strip().lower() != digest:
        return "has no current review-row schema-2 manifest pin"
    proposition_graph = manifest.get("elaborated_proposition_graph")
    dependency_graph = manifest.get("semantic_dependency_graph")
    if (
        not isinstance(proposition_graph, dict)
        or proposition_graph.get("complete") is not True
        or not isinstance(dependency_graph, dict)
        or dependency_graph.get("complete") is not True
        or dependency_graph.get("realization_complete") is not True
    ):
        return "has no complete schema-2 proposition/dependency receipt"
    return ""


def _current_schema2_review_manifest_surface_error(item: ReviewItem) -> str:
    """Require the exact proposition root without duplicating v11 closure."""

    manifest = item.lean_signature_manifest
    if not isinstance(manifest, dict) or manifest.get("schema") != 2:
        return "has no schema-2 elaborated manifest"
    digest = str(manifest.get("sha256") or "").strip().lower()
    if not digest or signature_manifest_digest(manifest) != digest:
        return "has no valid canonical schema-2 manifest digest"
    if str(item.lean_signature_sha256 or "").strip().lower() != digest:
        return "has no current review-row schema-2 manifest pin"
    proposition_graph = manifest.get("elaborated_proposition_graph")
    if not isinstance(proposition_graph, dict) or proposition_graph.get(
        "complete"
    ) is not True:
        return "has no complete schema-2 proposition receipt"
    return ""


def _semantic_contract_spec_lean_receipt_error(specification: ReviewItem) -> str:
    """Require the current Lean-owned evidence common to every Spec contract."""

    current_v11_root = bool(
        specification.llm_match_source
        == Path(V11_RAW_SOURCE_SPEC_SCREENING_FILE).name
        and specification.llm_match_stale is False
        and str(specification.llm_match_judgment or "").strip()
        in POSITIVE_SEMANTIC_MATCH_JUDGMENTS
    )
    # The current v11 transaction already owns complete semantic dependency,
    # proof, import, and axiom closure. Coverage checks its exact proposition
    # root and Lean-Meta Spec/proof contract without requiring an older second
    # recursive-manifest producer to succeed as well. Legacy lanes retain the
    # complete schema-2 dependency requirement above.
    spec_manifest_error = (
        _current_schema2_review_manifest_surface_error(specification)
        if current_v11_root
        else _current_schema2_review_manifest_error(specification)
    )
    if spec_manifest_error:
        return f"semantic-contract Spec {spec_manifest_error}"
    spec_manifest = specification.lean_signature_manifest
    assert isinstance(spec_manifest, dict)
    if (
        _review_item_declaration_kind(specification) != "definition"
        or spec_manifest.get("declaration_kind") != "definition"
        or spec_manifest.get("conclusion_mode") != "type_and_value"
    ):
        return "semantic-contract Spec is not a transparent definition"
    if specification.semantic_contract_lean_transparency_verified is not True:
        return (
            "semantic-contract Spec has no current Lean-AST transitive "
            "transparency proof"
        )
    if specification.semantic_contract_lean_match_verified is not True:
        return (
            "Lean Meta did not establish the exact Spec/evidence semantic contract"
        )
    return ""


def _semantic_contract_spec_evidence_lean_error(
    specification: ReviewItem,
    evidence: ReviewItem,
) -> str:
    """Require the artifact-pinned Lean verdict for a visible Spec/proof pair.

    The schema-2 manifests establish that both visible endpoints are current
    and of the right declaration kinds. Semantic equality and transparent
    dependency expansion are deliberately delegated to Lean Meta.
    """

    spec_error = _semantic_contract_spec_lean_receipt_error(specification)
    if spec_error:
        return spec_error
    evidence_manifest_error = _current_schema2_review_manifest_error(evidence)
    if evidence_manifest_error:
        return f"semantic-contract evidence {evidence_manifest_error}"
    evidence_manifest = evidence.lean_signature_manifest
    assert isinstance(evidence_manifest, dict)
    if (
        _review_item_declaration_kind(evidence) not in LEAN_PROOF_DECLARATION_KINDS
        or str(evidence.kind or "").strip().lower()
        not in LEAN_PROOF_DECLARATION_KINDS
        or evidence.is_assumption
        or evidence_manifest.get("declaration_kind") != "theorem"
        or evidence_manifest.get("conclusion_mode") != "type_only"
    ):
        return "semantic-contract evidence is not an actual proved theorem"
    return ""


def _plain_spec_evidence_contract_declarations(
    source_item: dict[str, Any],
    *,
    semantic_contract_schema: object,
) -> tuple[str, str, str]:
    """Return the exact declaration roles from a valid plain proves contract."""

    if (
        not isinstance(semantic_contract_schema, int)
        or isinstance(semantic_contract_schema, bool)
        or semantic_contract_schema not in {1, 2}
    ):
        return "", "", "source map has no supported semantic-contract schema"
    contract = source_item.get("semantic_contract")
    if not isinstance(contract, dict):
        return "", "", "source item has no explicit Spec/evidence semantic contract"
    allowed_contract_fields = {
        "spec_declaration",
        "evidence_declaration",
        "evidence_mode",
        "semantic_shape",
    }
    spec_declaration = str(contract.get("spec_declaration") or "").strip()
    evidence_declaration = str(contract.get("evidence_declaration") or "").strip()
    if (
        set(contract) != allowed_contract_fields
        or not spec_declaration
        or not evidence_declaration
        or spec_declaration == evidence_declaration
        or str(contract.get("evidence_mode") or "").strip() != "proves"
        or str(contract.get("semantic_shape") or "").strip() != "plain"
    ):
        return "", "", "source item has a malformed proves-mode Spec/evidence contract"
    return spec_declaration, evidence_declaration, ""


def _semantic_contract_spec_coverage_proof_row(
    source_item: dict[str, Any],
    owner: ReviewItem,
    row_items: Mapping[str, ReviewItem],
    *,
    semantic_contract_schema: object,
) -> tuple[ReviewItem | None, str]:
    """Resolve proof credit for one explicit transparent-Spec coverage owner.

    The source item must bind exact qualified Spec/evidence declarations.  The
    owner keeps statement and coverage credit; the returned theorem keeps proof
    credit.  No declaration spelling is treated as mathematical evidence.
    """

    spec_declaration, evidence_declaration, contract_error = (
        _plain_spec_evidence_contract_declarations(
            source_item,
            semantic_contract_schema=semantic_contract_schema,
        )
    )
    if contract_error:
        return None, contract_error
    if str(owner.full_name or "").strip() != spec_declaration:
        return None, "coverage row is not the contract's exact qualified Spec owner"
    configured_evidence_declaration = _configured_proposition_spec_proof_declaration(
        owner
    )
    if (
        owner.is_proposition_spec is not True
        or owner.proposition_spec_role != "proof_routed"
        or configured_evidence_declaration != evidence_declaration
    ):
        return None, "coverage row is not explicitly configured as the contract Spec"

    direct_declarations = source_item_direct_coverage_declarations(source_item)
    if direct_declarations != [evidence_declaration]:
        return None, "contract evidence is not the sole explicit direct source endpoint"
    evidence_candidates = [
        item
        for item in row_items.values()
        if str(item.full_name or "").strip() == evidence_declaration
    ]
    if len(evidence_candidates) > 1:
        return None, "contract evidence does not resolve to one exact reviewed declaration"
    if len(evidence_candidates) == 1:
        evidence = evidence_candidates[0]
        lean_contract_error = _semantic_contract_spec_evidence_lean_error(
            owner, evidence
        )
        if lean_contract_error:
            return None, lean_contract_error
        return evidence, ""

    # The v11 source-statement surface intentionally excludes the paired
    # theorem when a transparent ``Spec : Prop`` owns the source review.  Its
    # exact theorem status and equality to the Spec have already been checked
    # by Lean Meta above; give it proof credit without manufacturing a second
    # source-facing review card or widening the statement-review denominator.
    lean_contract_error = _semantic_contract_spec_lean_receipt_error(owner)
    if lean_contract_error:
        return None, lean_contract_error
    return (
        ReviewItem(
            name=evidence_declaration.rsplit(".", 1)[-1],
            full_name=evidence_declaration,
            kind="theorem",
            lean_statement="",
            paper_statement="",
            agent_statement="",
            source_status="auxiliary Lean-Meta proof credit",
        ),
        "",
    )


def _definitionally_realized_spec_coverage_error(
    source_item: dict[str, Any],
    owner: ReviewItem,
    *,
    semantic_contract_schema: object,
) -> str:
    """Validate a direct source definition owned by a transparent Spec.

    Definitions require semantic realization, not a manufactured theorem.
    Lean Meta already checks that the configured evidence declaration unfolds
    to the transparent Spec; this route only verifies the exact contract roles
    and the current authenticated receipt.
    """

    if (
        not isinstance(semantic_contract_schema, int)
        or isinstance(semantic_contract_schema, bool)
        or semantic_contract_schema not in {1, 2}
    ):
        return "source map has no supported semantic-contract schema"
    contract = source_item.get("semantic_contract")
    if not isinstance(contract, dict):
        return "source item has no explicit Spec/evidence semantic contract"
    allowed_contract_fields = {
        "spec_declaration",
        "evidence_declaration",
        "evidence_mode",
        "semantic_shape",
    }
    spec_declaration = str(contract.get("spec_declaration") or "").strip()
    evidence_declaration = str(contract.get("evidence_declaration") or "").strip()
    if (
        set(contract) != allowed_contract_fields
        or not spec_declaration
        or not evidence_declaration
        or spec_declaration == evidence_declaration
        or str(contract.get("evidence_mode") or "").strip()
        != "definitionally_realizes"
        or str(contract.get("semantic_shape") or "").strip() != "plain"
    ):
        return "source item has a malformed definitionally-realizes Spec/evidence contract"
    if str(owner.full_name or "").strip() != spec_declaration:
        return "coverage row is not the contract's exact qualified Spec owner"
    if source_item_direct_coverage_declarations(source_item) != [evidence_declaration]:
        return "contract evidence is not the sole explicit direct source endpoint"
    return _semantic_contract_spec_lean_receipt_error(owner)


def _coverage_proof_evidence_row(
    source_item: dict[str, Any],
    owner: ReviewItem,
    row_items: Mapping[str, ReviewItem],
    *,
    semantic_contract_schema: object,
) -> tuple[ReviewItem | None, str]:
    """Return the theorem that supplies proof credit for a coverage owner."""

    if _review_item_declaration_kind(owner) in LEAN_PROOF_DECLARATION_KINDS:
        return owner, ""
    return _semantic_contract_spec_coverage_proof_row(
        source_item,
        owner,
        row_items,
        semantic_contract_schema=semantic_contract_schema,
    )


def _coverage_route_error(
    source_key: str,
    source_item: dict[str, Any],
    row_item: ReviewItem,
    *,
    row_items: Mapping[str, ReviewItem] | None = None,
    semantic_contract_schema: object = None,
    source_route_inventory: Mapping[str, dict[str, Any]] | None = None,
) -> str:
    """Check that a coverage link uses the row's exact semantic source route.

    A green row-local statement review establishes only the source statement it
    actually reviewed.  It cannot establish coverage for a different map item
    merely because both items were linked to the same Lean declaration.
    """

    if row_item.is_assumption:
        # Explicit assumptions use the separate provenance lane, whose source
        # digest is checked there rather than in theorem statement routes.
        return ""
    if _source_item_is_corrected_target(source_item):
        target_error = _source_item_corrected_target_metadata_error(source_item)
        if target_error:
            return target_error
    source_kind = str(source_item.get("source_kind") or "").strip().lower()
    routes = row_item.llm_match_source_routes or []
    route_inventory = source_route_inventory or {}
    definition_component_routes: list[dict[str, Any]] = []
    if source_kind in SOURCE_DEFINITION_SEMANTIC_KINDS:
        for route in routes:
            if not isinstance(route, dict):
                continue
            if (
                str(route.get("source_item") or "").strip() == source_key
                and str(route.get("route_kind") or "").strip().lower()
                == "source_component"
            ):
                return (
                    "a source-component route to the whole definition cannot "
                    "masquerade as whole-item coverage"
                )
            component = route_inventory.get(
                str(route.get("source_item") or "").strip()
            )
            if not isinstance(component, dict) or (
                component.get("source_definition_component") is not True
                or str(component.get("source_component_of") or "").strip()
                != source_key
            ):
                continue
            for field in (
                "source_statement_sha256",
                "source_location",
                "source_definition_partition_sha256",
                "source_definition_component_sha256",
            ):
                expected_field = (
                    component.get("statement_sha256")
                    if field == "source_statement_sha256"
                    else component.get(field)
                )
                recorded_value = str(route.get(field) or "").strip()
                expected_value = str(expected_field or "").strip()
                if field != "source_location":
                    recorded_value = recorded_value.lower()
                    expected_value = expected_value.lower()
                if recorded_value != expected_value:
                    return f"definition-component coverage route has a stale {field}"
            if (
                str(route.get("route_kind") or "").strip().lower()
                != "source_component"
                or str(route.get("semantic_relation") or "").strip().lower()
                != SOURCE_DEFINITION_COMPONENT_RELATION
            ):
                return "definition-component coverage route has an invalid route or relation"
            definition_component_routes.append(route)
    allowed_rows = source_item_direct_coverage_declarations(source_item)
    if allowed_rows:
        row_full_name = str(row_item.full_name or "").strip()
        is_direct_owner = any(
            row_full_name == declaration
            or ("." not in declaration and row_item.name == declaration)
            or (
                not row_full_name
                and row_item.name == declaration.rsplit(".", 1)[-1]
            )
            for declaration in allowed_rows
        )
        if not is_direct_owner and not definition_component_routes:
            contract = source_item.get("semantic_contract")
            evidence_mode = (
                str(contract.get("evidence_mode") or "").strip()
                if isinstance(contract, dict)
                else ""
            )
            if evidence_mode == "definitionally_realizes":
                contract_error = _definitionally_realized_spec_coverage_error(
                    source_item,
                    row_item,
                    semantic_contract_schema=semantic_contract_schema,
                )
            else:
                _evidence, contract_error = _semantic_contract_spec_coverage_proof_row(
                    source_item,
                    row_item,
                    row_items or {},
                    semantic_contract_schema=semantic_contract_schema,
                )
            if contract_error:
                return (
                    "row is not an explicit direct source route or an exact "
                    f"semantic-contract Spec owner: {contract_error}"
                )
    _expected_statement, expected_digest = _source_item_coverage_statement(source_item)
    expected_location = _source_item_coverage_location(source_item)
    if not expected_digest or not expected_location:
        return "source item has incomplete canonical route metadata"
    route_policy = source_item_effective_route_policy(source_item)
    required_route_kinds = (
        {CORRECTED_TARGET_ROUTE_KIND}
        if _source_item_is_corrected_target(source_item)
        else (
            {"source_model_convention"}
            if route_policy["is_model_convention"]
            else (
                {"direct"}
                if source_kind in SOURCE_DEFINITION_SEMANTIC_KINDS
                else {"direct", "source_component"}
            )
        )
    )
    exact_routes = [
        route
        for route in routes
        if isinstance(route, dict)
        and str(route.get("source_statement_sha256") or "").strip()
        == expected_digest
        and str(route.get("source_location") or "").strip() == expected_location
    ]
    if definition_component_routes:
        return ""
    if not exact_routes:
        return "row has no exact source route for this coverage item"
    compatible_routes = [
        route
        for route in exact_routes
        if str(route.get("route_kind") or "").strip().lower()
        in required_route_kinds
    ]
    if not compatible_routes:
        return (
            "row route is not one of "
            + ", ".join(f"`{kind}`" for kind in sorted(required_route_kinds))
            + " for this coverage item"
        )
    if any(
        str(route.get("route_kind") or "").strip().lower() == "source_component"
        and str(route.get("semantic_relation") or "").strip().lower()
        not in SOURCE_COMPONENT_ROUTE_RELATIONS
        for route in compatible_routes
    ):
        return "source-component coverage route has an invalid semantic relation"
    return ""


def definition_joint_component_coverage_error(
    source_key: str,
    source_item: dict[str, Any],
    linked_rows: Iterable[ReviewItem],
    *,
    source_route_inventory: Mapping[str, dict[str, Any]],
) -> str:
    """Require exact-set coverage when a definition is split across rows."""

    if (
        str(source_item.get("source_kind") or "").strip().lower()
        not in SOURCE_DEFINITION_SEMANTIC_KINDS
    ):
        return ""
    _statement, parent_digest = _source_item_coverage_statement(source_item)
    parent_location = _source_item_coverage_location(source_item)
    direct_routes = []
    component_keys: list[str] = []
    for row in linked_rows:
        for route in row.llm_match_source_routes or []:
            if not isinstance(route, dict):
                continue
            route_kind = str(route.get("route_kind") or "").strip().lower()
            if (
                str(route.get("source_item") or "").strip() == source_key
                and str(route.get("source_statement_sha256") or "").strip()
                == parent_digest
                and str(route.get("source_location") or "").strip()
                == parent_location
                and route_kind
                in {
                    "direct",
                    CORRECTED_TARGET_ROUTE_KIND,
                }
            ):
                direct_routes.append(route)
            component_key = str(route.get("source_item") or "").strip()
            component = source_route_inventory.get(component_key)
            if (
                isinstance(component, dict)
                and component.get("source_definition_component") is True
                and str(component.get("source_component_of") or "").strip()
                == source_key
            ):
                component_keys.append(component_key)
    if direct_routes:
        if component_keys:
            return "definition coverage mixes a whole-item route with partition components"
        return ""
    if not component_keys:
        return ""

    partition, errors = source_definition_partition_record(source_item)
    if partition is None or errors:
        return "definition component coverage has no valid complete parent partition"
    expected_keys = {
        source_definition_component_route_key(
            source_key,
            component["semantic_clause_sha256"],
            component["source_anchor_sha256"],
        )
        for component in partition["components"]
    }
    seen_keys = set(component_keys)
    if len(component_keys) != len(seen_keys):
        return "definition component coverage duplicates a semantic clause"
    missing = expected_keys - seen_keys
    extra = seen_keys - expected_keys
    if missing or extra:
        return (
            "definition component coverage is not the exact complete partition "
            f"(missing={len(missing)}, extra={len(extra)})"
        )
    return ""


def _corrected_target_contract_spec_navigation_matches(
    source_item: dict[str, Any],
    primary_declaration: str,
    review_rows: list[str],
    source_inventory: object,
    paper_name: str,
    *,
    semantic_contract_schema: object,
) -> bool:
    """Perform only the cheap name-resolution part of Spec routing.

    The source-inventory precheck intentionally does not parse Lean rows.  It
    may therefore accept an exact, unambiguous contract Spec as a provisional
    corrected-target owner, but the full dashboard must still establish the
    schema-2 telescope match and proved theorem before closeout.
    """

    spec_declaration, evidence_declaration, contract_error = (
        _plain_spec_evidence_contract_declarations(
            source_item,
            semantic_contract_schema=semantic_contract_schema,
        )
    )
    if contract_error or evidence_declaration != primary_declaration:
        return False
    if review_rows == [spec_declaration]:
        return True
    if len(review_rows) != 1 or not isinstance(source_inventory, dict):
        return False
    paper_prefix = f"{paper_name}." if paper_name else ""
    short_name = spec_declaration.rsplit(".", 1)[-1]
    if (
        (paper_prefix and not spec_declaration.startswith(paper_prefix))
        or not short_name
        or review_rows != [short_name]
    ):
        return False
    configured_specs: set[str] = set()
    for candidate in source_inventory.values():
        if not isinstance(candidate, dict):
            continue
        candidate_spec, _candidate_evidence, candidate_error = (
            _plain_spec_evidence_contract_declarations(
                candidate,
                semantic_contract_schema=semantic_contract_schema,
            )
        )
        if (
            not candidate_error
            and (not paper_prefix or candidate_spec.startswith(paper_prefix))
            and candidate_spec.rsplit(".", 1)[-1] == short_name
        ):
            configured_specs.add(candidate_spec)
    return configured_specs == {spec_declaration}


def _corrected_target_coverage_error(
    source_item: dict[str, Any],
    coverage_item: dict[str, Any],
    coverage: str,
    *,
    source_inventory: dict[str, dict[str, Any]] | None = None,
    paper_name: str = "",
    row_items: Mapping[str, ReviewItem] | None = None,
    semantic_contract_schema: object = None,
) -> str:
    """Validate the source-side pins required for corrected-target coverage.

    The coverage verdict is intentionally distinct from ordinary ``covered``:
    it credits only the approved target and permanently records that the
    archival paper statement was not established by this Lean result.
    """

    is_corrected = _source_item_is_corrected_target(source_item)
    if not is_corrected:
        if coverage == CORRECTED_TARGET_COVERAGE:
            return "covered_corrected_target names a source item without corrected-target status"
        return ""
    if coverage != CORRECTED_TARGET_COVERAGE:
        return "corrected_source_statement must use coverage `covered_corrected_target`, never ordinary covered"
    target_error = _source_item_corrected_target_metadata_error(source_item)
    if target_error:
        return target_error
    target = _source_item_corrected_target(source_item)
    assert target is not None
    primary_declaration = _corrected_target_primary_declaration(source_item)
    assert primary_declaration is not None
    expected_statement, expected_statement_digest = _source_item_coverage_statement(
        source_item
    )
    del expected_statement
    if str(coverage_item.get("target_kind") or "").strip().lower() != CORRECTED_TARGET_ROUTE_KIND:
        return "covered_corrected_target must record target_kind approved_corrected_target"
    review_rows = _normalize_string_list(coverage_item.get("review_rows"))
    direct_owner_matches = _corrected_target_coverage_rows_match_primary(
        primary_declaration,
        review_rows,
        source_inventory,
        paper_name,
    )
    contract_spec_matches = False
    if not direct_owner_matches and row_items is not None and len(review_rows) == 1:
        owner = row_items.get(review_rows[0])
        if owner is not None:
            evidence, contract_error = _semantic_contract_spec_coverage_proof_row(
                source_item,
                owner,
                row_items,
                semantic_contract_schema=semantic_contract_schema,
            )
            contract_spec_matches = bool(
                not contract_error
                and evidence is not None
                and str(evidence.full_name or "").strip() == primary_declaration
            )
    elif not direct_owner_matches:
        contract_spec_matches = _corrected_target_contract_spec_navigation_matches(
            source_item,
            primary_declaration,
            review_rows,
            source_inventory,
            paper_name,
            semantic_contract_schema=semantic_contract_schema,
        )
    if not direct_owner_matches and not contract_spec_matches:
        return (
            "covered_corrected_target must link exactly the sole corrected-target "
            "endpoint in lean_declarations or its exact contract-backed transparent "
            "Spec; aliases and support rows cannot carry target coverage"
        )
    if str(coverage_item.get("statement_sha256") or "").strip().lower() != expected_statement_digest:
        return "covered_corrected_target has a stale corrected target statement digest"
    if str(coverage_item.get("archival_statement_sha256") or "").strip().lower() != str(
        source_item.get("statement_sha256") or ""
    ).strip().lower():
        return "covered_corrected_target has a stale archival statement digest"
    if str(coverage_item.get("corrected_target_sha256") or "").strip().lower() != corrected_target_digest(target):
        return "covered_corrected_target has a stale corrected-target record digest"
    if _normalize_string_list(coverage_item.get("governing_defect_ids")) != _normalize_string_list(
        target.get("governing_defect_ids")
    ):
        return "covered_corrected_target lacks the exact governing source-statement defect ids"
    if coverage_item.get("archival_equivalence_claimed") is not False:
        return "covered_corrected_target must set archival_equivalence_claimed to false"
    return ""


def paper_coverage_audit_summary(folder: Path, items: list[ReviewItem]) -> dict[str, Any]:
    """Summarize source-paper statement coverage by the review dashboard surface."""

    full_inventory, inventory, source_coverage_mode, source_coverage_mode_error = (
        paper_coverage_inventory(folder)
    )
    statement_map_path = folder / PAPER_STATEMENT_MAP_FILE
    statement_map_payload = paper_statement_map_payload(folder)
    raw_map_items = (
        statement_map_payload.get("items")
        if isinstance(statement_map_payload, dict)
        else None
    )
    presentation_aliases, _presentation_alias_errors = source_presentation_aliases(
        raw_map_items
    )
    deep_source_coverage_attestation = deep_source_coverage_attestation_error(
        statement_map_payload, source_coverage_mode
    )
    inventory_kind = str(statement_map_payload.get("source_inventory_kind") or "").strip()
    inventory_source_curated = statement_map_payload.get("source_curated") is True
    inventory_is_scaffold = (
        inventory_kind in PAPER_COVERAGE_SCAFFOLD_KINDS
        or "dashboard_seeded" in inventory_kind
        or statement_map_payload.get("source_curated") is False
    )
    has_explicit_inventory = bool(inventory) and any(
        _is_statement_map_source(item.get("source"))
        for item in inventory.values()
    )
    surface_hash = review_surface_digest(items)
    coverage_state = _coverage_binding_freshness(
        folder,
        full_inventory,
        inventory,
        source_coverage_mode,
        statement_map_payload,
        presentation_aliases=presentation_aliases,
    )
    audit = coverage_state.audit
    audit_items = coverage_state.audit_items
    coverage_item_bindings = coverage_state.coverage_item_bindings
    ambiguous_semantic_item_bindings = list(
        coverage_state.ambiguous_semantic_item_bindings
    )
    bound_audit_items = coverage_state.bound_audit_items
    inventory_hash = coverage_state.inventory_hash
    audit_required = paper_coverage_audit_required(folder, inventory)
    mode_migration_error = source_coverage_mode_migration_error(
        statement_map_payload, require_explicit=audit_required
    )
    raw_source_map_errors = paper_source_map_structural_errors(folder)
    source_presentation_classification_errors = sorted(
        set(
            raw_source_map_errors
            if statement_map_payload
            else [
                f"{key}: {error}"
                for key, item in full_inventory.items()
                for error in source_item_scope_classification_errors(item)
            ]
        )
    )
    unresolved_statement_map = (
        audit_required
        and _dashboard_is_file(statement_map_path)
        and not has_explicit_inventory
    )
    row_names = {item.name for item in items}
    prerequisite_coverage_rows = paper_semantic_prerequisite_coverage_review_items(
        folder,
        inventory,
        items,
    )
    coverage_row_names = row_names | set(prerequisite_coverage_rows)

    missing_inventory = audit_required and not has_explicit_inventory
    missing_required = audit_required and not audit_items
    inventory_missing_source_url = sorted(
        key
        for key, item in inventory.items()
        if _is_statement_map_source(item.get("source"))
        and not str(item.get("source_url") or "").strip()
    )
    inventory_missing_source_provenance = sorted(
        key
        for key, item in inventory.items()
        if _is_statement_map_source(item.get("source"))
        and not (
            str(item.get("source_location") or "").strip()
            or str(item.get("source_note") or "").strip()
            or str(item.get("source_status") or "").strip()
        )
    )
    inventory_unknown_source_kind = sorted(
        key
        for key, item in inventory.items()
        if _is_statement_map_source(item.get("source"))
        and str(item.get("source_kind") or "").strip()
        and str(item.get("source_kind") or "").strip().lower()
        not in KNOWN_SOURCE_PRESENTATION_KINDS
    )
    source_scope_classification_errors = (
        _source_scope_classification_errors(inventory, bound_audit_items)
        if source_coverage_mode == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
        else []
    )
    user_approved_scope_exclusion_errors = _user_approved_scope_exclusion_errors(
        inventory, bound_audit_items
    )
    source_anchor_evidence_errors = _scoped_source_anchor_evidence_errors(folder)
    source_named_result_inventory_errors = _source_named_result_inventory_errors(
        folder
    )
    missing_coverage = list(coverage_state.missing_coverage)
    extra_coverage = list(coverage_state.extra_coverage)
    out_of_mode_coverage = list(coverage_state.out_of_mode_coverage)
    missing_statement_digest = list(coverage_state.missing_statement_digest)
    stale_statement = list(coverage_state.stale_statement)
    invalid_row_links = sorted(
        {
            row
            for item in bound_audit_items.values()
            for row in _normalize_string_list(item.get("review_rows"))
            if row not in coverage_row_names
        }
    )
    recorded_inventory_hash = coverage_state.recorded_inventory_hash
    recorded_source_coverage_mode = coverage_state.recorded_mode
    source_coverage_mode_mismatch = coverage_state.mode_mismatch
    recorded_surface_hash = str(audit.get("review_surface_sha256") or "").strip()
    aggregate_inventory_current = coverage_state.aggregate_current
    source_artifact_current = coverage_state.source_artifact_current
    aggregate_receipt_required = any(
        not _coverage_item_has_current_source_digest_schema(item)
        for item in bound_audit_items.values()
    )
    stale_inventory = bool(
        audit_items
        and not aggregate_inventory_current
        and aggregate_receipt_required
    )
    stale_source_items = list(coverage_state.stale_source_items)
    semantic_reuse_anchor_errors = coverage_state.semantic_reuse_anchor_errors
    unverified_reused_source_items = list(
        coverage_state.unverified_reused_source_items
    )
    legacy_unpinned_items = list(coverage_state.legacy_unpinned_items)
    stale_surface = bool(audit_items and recorded_surface_hash and recorded_surface_hash != surface_hash)
    audit_kind = str(audit.get("audit_kind") or "").strip()
    audit_source_grounded = bool(audit.get("source_grounded") is True)
    audit_is_scaffold = bool(audit.get("seed_scaffold") is True) or audit_kind in PAPER_COVERAGE_SCAFFOLD_KINDS
    audit_prompt_version = str(audit.get("prompt_version") or "").strip()
    inventory_has_quarantined_defect = any(
        _source_inventory_item_is_quarantined_defect(item)
        for item in inventory.values()
    )
    audit_prompt_version_stale = bool(
        audit_prompt_version != REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION
        and not (
            audit_prompt_version == LEGACY_LLM_PAPER_COVERAGE_PROMPT_VERSION
            and not inventory_has_quarantined_defect
        )
    )
    coverage_source_input_errors: list[str] = []
    if audit_prompt_version == REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION:
        if str(audit.get("source_input_protocol") or "").strip() != "verbatim_source_anchor_bundle_v1":
            coverage_source_input_errors.append(
                "coverage review does not declare the required verbatim_source_anchor_bundle_v1 input protocol"
            )
        for source_key, coverage_item in bound_audit_items.items():
            expected_anchor_identity, anchor_error = source_anchor_quote_identity(
                inventory[source_key]
            )
            recorded_anchor_identity = str(
                coverage_item.get("source_anchor_quote_identity_sha256") or ""
            ).strip().lower()
            if anchor_error:
                coverage_source_input_errors.append(
                    f"{source_key}: {anchor_error}"
                )
            elif recorded_anchor_identity != expected_anchor_identity:
                coverage_source_input_errors.append(
                    f"{source_key}: coverage judgment lacks the current exact "
                    "verbatim source-anchor identity"
                )
    audit_metadata_missing = bool(audit_required and audit_items and audit.get("metadata_missing"))
    missing_source_grounded_audit = bool(
        audit_required
        and audit_items
        and (
            audit_is_scaffold
            or audit_kind not in APPROVED_PAPER_COVERAGE_AUDIT_KINDS
            or not audit_source_grounded
            or audit_prompt_version_stale
            or coverage_source_input_errors
            or audit_metadata_missing
        )
    )
    row_items = {item.name: item for item in items}
    # Source definitions are direct semantic coverage targets even though they
    # are prerequisite cards rather than result-Spec denominator rows.  Reuse
    # their existing reviewed identities; do not manufacture duplicate claim
    # rows or second LLM judgments.
    for name, prerequisite in prerequisite_coverage_rows.items():
        if name not in row_items:
            row_items[name] = prerequisite
    # Counterexample/refutation rows are exact Lean review inputs for the
    # defect-support lane, but never paper claims.  Their cache shares the
    # current interface/status/Lean-closure transaction with `items` above.
    row_items.update(quarantined_support_review_items(folder))
    current_rows_by_signature = _current_row_signature_index(row_items)
    current_signature_by_row = {
        row_name: digest
        for digest, row_names in current_rows_by_signature.items()
        for row_name in row_names
    }
    effective_audit_items: dict[str, dict[str, Any]] = {}
    semantic_row_rebindings: list[str] = []
    for source_key, raw_item in bound_audit_items.items():
        rebound_item, changes, rebound = _semantic_rebound_coverage_item(
            raw_item, current_rows_by_signature
        )
        effective_audit_items[source_key] = rebound_item
        if rebound:
            semantic_row_rebindings.extend(
                f"{source_key}: {change}" for change in changes
            )
    # Re-evaluate row links after a unique signature-based route rebinding.
    # A name change alone is harmless; a missing/ambiguous/different signature
    # deliberately remains an invalid route below.
    invalid_row_links = sorted(
        {
            row
            for item in effective_audit_items.values()
            for row in _normalize_string_list(item.get("review_rows"))
            if row not in coverage_row_names
        }
    )
    require_source_routes = llm_statement_source_routes_required(folder)
    source_route_inventory = dict(full_inventory)
    if require_source_routes:
        source_route_inventory.update(paper_source_component_route_inventory(folder))
        source_route_inventory.update(
            paper_source_definition_component_route_inventory(folder)
        )
    validated_source_defects = _validated_source_proof_defects(folder)
    validated_source_defect_ids = set(validated_source_defects)
    quarantine_support_requested = any(
        key in inventory
        and _source_inventory_item_is_quarantined_defect(inventory[key])
        and str(item.get("coverage") or "").strip()
        in {"covered_by_support", "support_only"}
        for key, item in effective_audit_items.items()
    )
    defect_support_audit = load_llm_defect_support_audit(folder)
    defect_support_items = (
        defect_support_audit.get("items")
        if isinstance(defect_support_audit.get("items"), dict)
        else {}
    )
    defect_support_audit_metadata_error = ""
    if quarantine_support_requested:
        if not defect_support_audit:
            defect_support_audit_metadata_error = (
                "missing audit/defect_support_match_llm.json"
            )
        elif defect_support_audit.get("load_error"):
            defect_support_audit_metadata_error = str(
                defect_support_audit.get("load_error")
            )
        elif defect_support_audit.get("prompt_version_stale"):
            defect_support_audit_metadata_error = "defect-support prompt version is stale"
        elif defect_support_audit.get("audit_kind") not in APPROVED_DEFECT_SUPPORT_AUDIT_KINDS:
            defect_support_audit_metadata_error = "defect-support audit_kind is not semantic"
        elif defect_support_audit.get("source_grounded") is not True:
            defect_support_audit_metadata_error = "defect-support audit is not source-grounded"
        elif defect_support_audit.get("metadata_missing") or not str(
            defect_support_audit.get("validator_type") or ""
        ).strip():
            defect_support_audit_metadata_error = (
                "defect-support audit lacks validator, validator_type, or validated_at"
            )
        elif not defect_support_items:
            defect_support_audit_metadata_error = "defect-support audit has no judgments"

    valid_defect_support_pairs: set[tuple[str, str, str]] = set()
    seen_defect_support_pairs: set[tuple[str, str, str]] = set()
    defect_support_judgment_errors: list[str] = []
    if defect_support_audit_metadata_error:
        defect_support_judgment_errors.append(
            f"audit:{defect_support_audit_metadata_error}"
        )
    elif defect_support_items:
        for judgment_key, raw_judgment in defect_support_items.items():
            label = str(judgment_key or "").strip() or "<unnamed>"
            if not isinstance(raw_judgment, dict):
                defect_support_judgment_errors.append(
                    f"{label}:judgment row is not an object"
                )
                continue
            source_key = str(raw_judgment.get("source_item") or "").strip()
            defect_id = str(raw_judgment.get("defect_id") or "").strip()
            support_name = str(
                raw_judgment.get("support_declaration") or ""
            ).strip()
            pair = (source_key, defect_id, support_name)
            if pair in seen_defect_support_pairs:
                valid_defect_support_pairs.discard(pair)
                defect_support_judgment_errors.append(
                    f"{label}:duplicate source-item/defect/declaration judgment"
                )
                continue
            seen_defect_support_pairs.add(pair)
            source_item = inventory.get(source_key)
            defect = validated_source_defects.get(defect_id)
            row_item = row_items.get(support_name)
            if source_item is None or defect is None or row_item is None:
                defect_support_judgment_errors.append(
                    f"{label}:unknown source item, validated defect, or reviewed declaration"
                )
                continue
            error = defect_support_judgment_error(
                raw_judgment,
                source_key=source_key,
                source_item=source_item,
                defect=defect,
                support_declaration=support_name,
                row_item=row_item,
            )
            if error:
                defect_support_judgment_errors.append(f"{label}:{error}")
            else:
                valid_defect_support_pairs.add(pair)

    covered: list[str] = []
    corrected_target_covered: list[str] = []
    conditional_boundary: list[str] = []
    support_only: list[str] = []
    out_of_scope: list[str] = []
    partial: list[str] = []
    missing: list[str] = []
    uncertain: list[str] = []
    unknown: list[str] = []
    covered_without_rows: list[str] = []
    covered_without_reason: list[str] = []
    covered_with_seed_reason: list[str] = []
    covered_without_source_evidence: list[str] = []
    support_without_declarations: list[str] = []
    support_without_reason: list[str] = []
    support_without_source_evidence: list[str] = []
    out_of_scope_without_reason: list[str] = []
    out_of_scope_without_source_evidence: list[str] = []
    coverage_metadata_missing: list[str] = []
    coverage_route_mismatch: list[str] = []
    corrected_target_coverage_errors: list[str] = []
    coverage_row_signature_errors: list[str] = []
    row_statement_match_links: list[dict[str, Any]] = []
    row_statement_match_missing: list[str] = []
    row_statement_match_stale: list[str] = []
    row_statement_match_mismatch: list[str] = []
    row_statement_match_uncertain: list[str] = []
    row_statement_match_unknown: list[str] = []
    row_statement_match_conditional: list[str] = []
    row_statement_match_conditional_without_coverage_boundary: list[str] = []
    row_statement_match_missing_statement_digest: list[str] = []
    row_statement_match_wrong_statement_digest: list[str] = []
    row_assumption_provenance_missing: list[str] = []
    row_assumption_provenance_stale: list[str] = []
    row_assumption_provenance_mismatch: list[str] = []
    row_assumption_provenance_uncertain: list[str] = []
    row_assumption_provenance_unknown: list[str] = []
    row_assumption_provenance_conditional: list[str] = []
    row_assumption_provenance_conditional_without_coverage_boundary: list[str] = []
    result_covered_without_proof_rows: list[str] = []
    result_covered_only_by_definition_rows: list[str] = []
    result_matched_only_by_definition_rows: list[str] = []
    semantic_contract_spec_proof_links: list[str] = []
    quarantined_defect_support: list[str] = []
    invalid_quarantined_defect_support: list[str] = []
    audited_proof_support: list[str] = []
    invalid_proof_support: list[str] = []
    quarantined_defect_direct_coverage: list[str] = []
    support_only_named_claims: list[str] = []
    support_only_required_source_items: list[str] = []
    user_approved_scope_exclusions: list[str] = []
    required_out_of_scope: list[str] = []
    for key, item in effective_audit_items.items():
        if item.get("metadata_missing"):
            coverage_metadata_missing.append(key)
        coverage = _normalize_paper_coverage_judgment(item.get("coverage"))
        rows = _normalize_string_list(item.get("review_rows"))
        corrected_target_error = _corrected_target_coverage_error(
            inventory[key],
            item,
            coverage,
            source_inventory=full_inventory,
            paper_name=folder.name,
            row_items=row_items,
            semantic_contract_schema=statement_map_payload.get(
                "semantic_contract_schema"
            ),
        )
        if corrected_target_error:
            corrected_target_coverage_errors.append(f"{key}: {corrected_target_error}")
        if coverage in {
            "covered",
            "covered_by_rows",
            "conditional_boundary",
            "covered_with_boundary",
            CORRECTED_TARGET_COVERAGE,
        }:
            if _source_inventory_item_is_quarantined_defect(inventory[key]):
                quarantined_defect_direct_coverage.append(key)
            elif coverage in {"conditional_boundary", "covered_with_boundary"}:
                conditional_boundary.append(key)
            elif coverage == CORRECTED_TARGET_COVERAGE and not corrected_target_error:
                corrected_target_covered.append(key)
            elif _source_item_is_corrected_target(inventory[key]):
                # A malformed ordinary verdict for a corrected item receives no
                # direct-coverage count, even before the aggregate error gate.
                pass
            else:
                covered.append(key)
            if not rows:
                covered_without_rows.append(key)
            coverage_row_signature_errors.extend(
                _coverage_review_row_signature_errors(
                    key,
                    rows,
                    item.get("review_row_signature_sha256"),
                    row_items,
                    current_signature_by_row=current_signature_by_row,
                )
            )
            reason = str(item.get("reason") or "").strip()
            source_evidence = str(item.get("source_evidence") or "").strip()
            if not reason:
                covered_without_reason.append(key)
            if NAME_ONLY_SOURCE_COVERAGE_REASON_RE.search(reason):
                covered_with_seed_reason.append(key)
            if not source_evidence:
                covered_without_source_evidence.append(key)
            linked_row_items = [
                row_items[row_name]
                for row_name in rows
                if row_name in row_items
            ]
            proof_evidence_by_owner: dict[str, ReviewItem] = {}
            for owner in linked_row_items:
                evidence, _proof_evidence_error = _coverage_proof_evidence_row(
                    inventory[key],
                    owner,
                    row_items,
                    semantic_contract_schema=statement_map_payload.get(
                        "semantic_contract_schema"
                    ),
                )
                if evidence is None:
                    continue
                proof_evidence_by_owner[owner.name] = evidence
                if evidence is not owner:
                    semantic_contract_spec_proof_links.append(
                        f"{key}: {owner.name} -> {evidence.name}"
                    )
            if require_source_routes:
                for row_name in rows:
                    row_item = row_items.get(row_name)
                    if row_item is None:
                        continue
                    route_error = _coverage_route_error(
                        key,
                        inventory[key],
                        row_item,
                        row_items=row_items,
                        semantic_contract_schema=statement_map_payload.get(
                            "semantic_contract_schema"
                        ),
                        source_route_inventory=source_route_inventory,
                    )
                    if route_error:
                        coverage_route_mismatch.append(
                            f"{_coverage_link_label(key, row_name)}: {route_error}"
                        )
                joint_component_error = definition_joint_component_coverage_error(
                    key,
                    inventory[key],
                    linked_row_items,
                    source_route_inventory=source_route_inventory,
                )
                if joint_component_error:
                    coverage_route_mismatch.append(
                        f"{key}: {joint_component_error}"
                    )
            result_requires_proof = _source_inventory_item_requires_proof_evidence(
                key, inventory[key]
            )
            if (
                result_requires_proof
                and linked_row_items
                and not proof_evidence_by_owner
            ):
                result_covered_without_proof_rows.append(key)
                if all(
                    _review_item_declaration_kind(row_item)
                    in LEAN_SPECIFICATION_DECLARATION_KINDS
                    for row_item in linked_row_items
                ):
                    result_covered_only_by_definition_rows.append(key)
            matching_row_items = [
                row_item
                for row_item in linked_row_items
                if str(row_item.llm_match_judgment or "").strip()
                in POSITIVE_SEMANTIC_MATCH_JUDGMENTS
            ]
            if (
                result_requires_proof
                and matching_row_items
                and not any(
                    row_item.name in proof_evidence_by_owner
                    for row_item in matching_row_items
                )
                and all(
                    _review_item_declaration_kind(row_item)
                    in LEAN_SPECIFICATION_DECLARATION_KINDS
                    for row_item in matching_row_items
                )
            ):
                result_matched_only_by_definition_rows.append(key)
            for row_name in rows:
                row_item = row_items.get(row_name)
                if row_item is None:
                    continue
                link_label = _coverage_link_label(key, row_name)
                row_statement_match_links.append(
                    _row_statement_match_record(key, inventory[key], coverage, row_name, row_item)
                )
                # Source model conditions are audited in the assumption-provenance
                # lane.  Requiring a second theorem-statement equivalence for the
                # same explicit assumption both duplicates work and misclassifies
                # a condition as a proved paper conclusion.
                if row_item.is_assumption:
                    assumption_judgment = str(row_item.llm_assumption_judgment or "").strip()
                    if row_item.llm_assumption_stale:
                        row_assumption_provenance_stale.append(link_label)
                    if not assumption_judgment:
                        row_assumption_provenance_missing.append(link_label)
                    elif assumption_judgment in {
                        "paper_assumption",
                        "paper_condition",
                        "documented_additional_assumption",
                        "documented_caveat",
                    }:
                        pass
                    elif assumption_judgment == "partial_boundary":
                        row_assumption_provenance_conditional.append(link_label)
                        if coverage not in {"conditional_boundary", "covered_with_boundary"}:
                            row_assumption_provenance_conditional_without_coverage_boundary.append(link_label)
                    elif assumption_judgment == "not_paper_assumption":
                        row_assumption_provenance_mismatch.append(link_label)
                    elif assumption_judgment == "uncertain":
                        row_assumption_provenance_uncertain.append(link_label)
                    else:
                        row_assumption_provenance_unknown.append(link_label)
                    continue
                recorded_paper_digest = str(row_item.llm_match_paper_statement_sha256 or "").strip()
                row_paper_digest = statement_digest(row_item.paper_statement)
                row_audit_target_digest = (
                    _review_item_statement_audit_target_sha256(row_item)
                )
                if not recorded_paper_digest:
                    row_statement_match_missing_statement_digest.append(link_label)
                elif recorded_paper_digest != row_audit_target_digest:
                    row_statement_match_wrong_statement_digest.append(link_label)
                # A corrected-target coverage row can certify only the explicit
                # repaired statement. The v11 row-local review nevertheless
                # receives the literal archival source anchor; its approved
                # target is carried by the exact route and resolution rather
                # than by pretending that the archival quote has corrected
                # wording.
                if _source_item_is_corrected_target(inventory[key]):
                    if row_item.source_input_bundle_sha256:
                        archival_input, _input_identity, archival_input_error = (
                            source_semantic_input_bundle(inventory[key])
                        )
                        if (
                            archival_input_error
                            or row_paper_digest
                            != statement_digest(archival_input)
                        ):
                            row_statement_match_mismatch.append(link_label)
                    else:
                        # Pre-v11 review rows carried the approved target
                        # itself rather than a raw source-input bundle.
                        _target_statement, target_digest = (
                            _source_item_coverage_statement(inventory[key])
                        )
                        if row_paper_digest != target_digest:
                            row_statement_match_mismatch.append(link_label)
                judgment = str(row_item.llm_match_judgment or "").strip()
                resolution = _normalize_llm_match_resolution(row_item.llm_match_resolution)
                if row_item.llm_match_stale:
                    row_statement_match_stale.append(link_label)
                if not judgment:
                    row_statement_match_missing.append(link_label)
                elif judgment in POSITIVE_SEMANTIC_MATCH_JUDGMENTS:
                    if (
                        _source_item_is_corrected_target(inventory[key])
                        and resolution != CORRECTED_TARGET_MATCH_RESOLUTION
                    ):
                        row_statement_match_mismatch.append(link_label)
                    elif (
                        judgment == APPROVED_CORRECTED_TARGET_MATCH
                        and not _source_item_is_corrected_target(inventory[key])
                    ):
                        row_statement_match_mismatch.append(link_label)
                elif judgment == "mismatch" and resolution == CONDITIONAL_BOUNDARY_RESOLUTION:
                    row_statement_match_conditional.append(link_label)
                    if coverage not in {"conditional_boundary", "covered_with_boundary"}:
                        row_statement_match_conditional_without_coverage_boundary.append(link_label)
                elif judgment == "mismatch":
                    row_statement_match_mismatch.append(link_label)
                elif judgment == "uncertain":
                    row_statement_match_uncertain.append(link_label)
                else:
                    row_statement_match_unknown.append(link_label)
        elif coverage == USER_APPROVED_SCOPE_EXCLUSION:
            # This is intentionally a distinct audit disposition.  The source
            # assertion remains in the inventory and is not relabelled as a
            # computational observation or non-claim; validation above ensures
            # its approval and pinned source evidence are complete.
            user_approved_scope_exclusions.append(key)
        elif coverage in {"out_of_scope", "not_a_paper_target", "not_a_theorem_statement"}:
            out_of_scope.append(key)
            reason = str(item.get("reason") or "").strip()
            source_evidence = str(item.get("source_evidence") or "").strip()
            if not reason:
                out_of_scope_without_reason.append(key)
            if not source_evidence:
                out_of_scope_without_source_evidence.append(key)
            if _source_inventory_item_requires_review_row(key, inventory[key]):
                required_out_of_scope.append(key)
        elif coverage in {"covered_by_support", "support_only"}:
            support_only.append(key)
            support_declarations = _normalize_string_list(item.get("support_declarations"))
            reason = str(item.get("reason") or "").strip()
            source_evidence = str(item.get("source_evidence") or "").strip()
            if not support_declarations:
                support_without_declarations.append(key)
            if not reason:
                support_without_reason.append(key)
            if not source_evidence:
                support_without_source_evidence.append(key)
            if _source_inventory_item_is_explicit_proof_support(inventory[key]):
                proof_support_error = _proof_support_coverage_error(
                    inventory[key], item, row_items
                )
                if proof_support_error:
                    invalid_proof_support.append(f"{key}: {proof_support_error}")
                else:
                    audited_proof_support.append(key)
            elif _source_inventory_item_is_quarantined_defect(inventory[key]):
                configured_support = set(
                    _proof_support_declaration_names(
                        inventory[key].get("support_lean_declarations")
                    )
                )
                defect_ids = _normalize_string_list(
                    inventory[key].get("source_defect_ids")
                )
                support_rows = [
                    row_items[name]
                    for name in support_declarations
                    if name in row_items
                ]
                defects_with_semantic_support = {
                    defect_id
                    for defect_id in defect_ids
                    if any(
                        (key, defect_id, support_name)
                        in valid_defect_support_pairs
                        for support_name in support_declarations
                    )
                }
                declarations_with_semantic_support = {
                    support_name
                    for support_name in support_declarations
                    if any(
                        (key, defect_id, support_name)
                        in valid_defect_support_pairs
                        for defect_id in defect_ids
                    )
                }
                valid_quarantine_support = bool(
                    defect_ids
                    and set(defect_ids).issubset(validated_source_defect_ids)
                    and support_declarations
                    and set(support_declarations).issubset(configured_support)
                    and len(support_rows) == len(support_declarations)
                    and all(
                        _review_item_declaration_kind(row_item)
                        in LEAN_PROOF_DECLARATION_KINDS
                        for row_item in support_rows
                    )
                    and defects_with_semantic_support == set(defect_ids)
                    and declarations_with_semantic_support
                    == set(support_declarations)
                )
                if valid_quarantine_support:
                    quarantined_defect_support.append(key)
                else:
                    invalid_quarantined_defect_support.append(key)
            else:
                if _source_inventory_item_requires_proof_evidence(key, inventory[key]):
                    support_only_named_claims.append(key)
                if _source_inventory_item_requires_review_row(key, inventory[key]):
                    support_only_required_source_items.append(key)
        elif coverage == "partially_covered":
            partial.append(key)
        elif coverage == "missing":
            missing.append(key)
        elif coverage in {"uncertain", "unknown", "needs_review", ""}:
            uncertain.append(key)
        else:
            unknown.append(key)

    semantic_contract_spec_proof_links = sorted(
        set(semantic_contract_spec_proof_links)
    )
    coverage_needs_attention = bool(
        source_coverage_mode_error
        or mode_migration_error
        or deep_source_coverage_attestation
        or source_presentation_classification_errors
        or ambiguous_semantic_item_bindings
        or source_named_result_inventory_errors
        or (
            audit_required
            and (
            missing_inventory
            or unresolved_statement_map
            or inventory_is_scaffold
            or missing_required
            or missing_source_grounded_audit
            or coverage_metadata_missing
            or coverage_route_mismatch
            or corrected_target_coverage_errors
            or coverage_row_signature_errors
            or inventory_missing_source_url
            or inventory_missing_source_provenance
            or inventory_unknown_source_kind
            or source_scope_classification_errors
            or user_approved_scope_exclusion_errors
            or source_anchor_evidence_errors
            or source_coverage_mode_mismatch
            or missing_coverage
            or missing_statement_digest
            or stale_statement
            # Aggregate source/dashboard digests are discovery signals.  They
            # do not reopen an unchanged source item whose own source digest
            # and every linked elaborated Lean signature remain current.
            or stale_source_items
            or unverified_reused_source_items
            or legacy_unpinned_items
            or invalid_row_links
            or partial
            or missing
            or uncertain
            or unknown
            or covered_without_rows
            or covered_without_reason
            or covered_with_seed_reason
            or covered_without_source_evidence
            or result_covered_without_proof_rows
            or result_matched_only_by_definition_rows
            or quarantined_defect_direct_coverage
            or support_without_declarations
            or support_without_reason
            or support_without_source_evidence
            or invalid_proof_support
            or invalid_quarantined_defect_support
            or defect_support_judgment_errors
            or required_out_of_scope
            or out_of_scope_without_reason
            or out_of_scope_without_source_evidence
            or extra_coverage
            )
        )
    )
    source_to_lean_needs_attention = bool(
        coverage_needs_attention
        or support_only_named_claims
        or support_only_required_source_items
        or row_statement_match_missing
        or row_statement_match_stale
        or row_statement_match_mismatch
        or row_statement_match_uncertain
        or row_statement_match_unknown
        or row_statement_match_conditional_without_coverage_boundary
        or row_statement_match_missing_statement_digest
        or row_statement_match_wrong_statement_digest
        or row_assumption_provenance_missing
        or row_assumption_provenance_stale
        or row_assumption_provenance_mismatch
        or row_assumption_provenance_uncertain
        or row_assumption_provenance_unknown
        or row_assumption_provenance_conditional_without_coverage_boundary
        or coverage_route_mismatch
        or corrected_target_coverage_errors
        or coverage_row_signature_errors
        or result_covered_without_proof_rows
        or result_matched_only_by_definition_rows
        or quarantined_defect_direct_coverage
        or invalid_proof_support
        or invalid_quarantined_defect_support
        or defect_support_judgment_errors
    )
    return {
        "source_coverage_mode": source_coverage_mode,
        "source_coverage_mode_error": source_coverage_mode_error,
        "source_coverage_mode_migration_error": mode_migration_error,
        "deep_source_coverage_attestation_error": deep_source_coverage_attestation,
        "full_inventory_count": len(full_inventory),
        "inventory_count": len(inventory),
        "has_statement_map_file": _dashboard_is_file(statement_map_path),
        "has_explicit_inventory": has_explicit_inventory,
        "inventory_kind": inventory_kind,
        "inventory_source_curated": inventory_source_curated,
        "inventory_is_scaffold": inventory_is_scaffold,
        "unresolved_statement_map": unresolved_statement_map,
        "covered_count": len(covered),
        "corrected_target_covered_count": len(corrected_target_covered),
        "conditional_boundary_count": len(conditional_boundary),
        "support_only_count": len(support_only),
        "audited_proof_support_count": len(audited_proof_support),
        "invalid_proof_support_count": len(invalid_proof_support),
        "quarantined_defect_support_count": len(quarantined_defect_support),
        "invalid_quarantined_defect_support_count": len(
            invalid_quarantined_defect_support
        ),
        "defect_support_judgment_error_count": len(
            defect_support_judgment_errors
        ),
        "quarantined_defect_direct_coverage_count": len(
            quarantined_defect_direct_coverage
        ),
        "user_approved_scope_exclusion_count": len(
            user_approved_scope_exclusions
        ),
        "user_approved_scope_exclusion_error_count": len(
            user_approved_scope_exclusion_errors
        ),
        "out_of_scope_count": len(out_of_scope),
        "partial_count": len(partial),
        "missing_count": len(missing),
        "uncertain_count": len(uncertain),
        "unknown_count": len(unknown),
        "audit_required": audit_required,
        "missing_inventory": missing_inventory,
        "missing_required": missing_required,
        "inventory_missing_source_url_count": len(inventory_missing_source_url),
        "inventory_missing_source_provenance_count": len(inventory_missing_source_provenance),
        "inventory_unknown_source_kind_count": len(inventory_unknown_source_kind),
        "source_scope_classification_error_count": len(
            source_scope_classification_errors
        ),
        "source_presentation_classification_error_count": len(
            source_presentation_classification_errors
        ),
        "source_map_structural_error_count": len(raw_source_map_errors),
        "semantic_item_rebinding_count": sum(
            source_key != audit_key
            for source_key, audit_key in coverage_item_bindings.items()
        ),
        "semantic_item_rebindings": [
            f"{source_key} <- {audit_key}"
            for source_key, audit_key in sorted(coverage_item_bindings.items())
            if source_key != audit_key
        ],
        "ambiguous_semantic_item_bindings": ambiguous_semantic_item_bindings,
        "semantic_row_rebinding_count": len(semantic_row_rebindings),
        "semantic_row_rebindings": sorted(semantic_row_rebindings),
        "source_anchor_evidence_error_count": len(source_anchor_evidence_errors),
        "source_named_result_inventory_error_count": len(
            source_named_result_inventory_errors
        ),
        "missing_coverage_count": len(missing_coverage),
        "extra_coverage_count": len(extra_coverage),
        "out_of_mode_coverage_count": len(out_of_mode_coverage),
        "missing_statement_digest_count": len(missing_statement_digest),
        "stale_statement_count": len(stale_statement),
        "stale_source_item_count": len(stale_source_items),
        "unverified_reused_source_item_count": len(
            unverified_reused_source_items
        ),
        "legacy_unpinned_item_count": len(legacy_unpinned_items),
        "invalid_row_link_count": len(invalid_row_links),
        "covered_without_rows_count": len(covered_without_rows),
        "covered_without_reason_count": len(covered_without_reason),
        "covered_with_seed_reason_count": len(covered_with_seed_reason),
        "covered_without_source_evidence_count": len(covered_without_source_evidence),
        "result_covered_without_proof_row_count": len(result_covered_without_proof_rows),
        "result_covered_only_by_definition_row_count": len(
            result_covered_only_by_definition_rows
        ),
        "result_matched_only_by_definition_row_count": len(
            result_matched_only_by_definition_rows
        ),
        "semantic_contract_spec_proof_link_count": len(
            semantic_contract_spec_proof_links
        ),
        "support_without_declarations_count": len(support_without_declarations),
        "support_without_reason_count": len(support_without_reason),
        "support_without_source_evidence_count": len(support_without_source_evidence),
        "support_only_named_claim_count": len(support_only_named_claims),
        "support_only_required_source_item_count": len(support_only_required_source_items),
        "required_out_of_scope_count": len(required_out_of_scope),
        "out_of_scope_without_reason_count": len(out_of_scope_without_reason),
        "out_of_scope_without_source_evidence_count": len(out_of_scope_without_source_evidence),
        "row_statement_match_link_count": len(row_statement_match_links),
        "row_statement_match_missing_count": len(row_statement_match_missing),
        "row_statement_match_stale_count": len(row_statement_match_stale),
        "row_statement_match_mismatch_count": len(row_statement_match_mismatch),
        "row_statement_match_uncertain_count": len(row_statement_match_uncertain),
        "row_statement_match_unknown_count": len(row_statement_match_unknown),
        "row_statement_match_conditional_count": len(row_statement_match_conditional),
        "row_statement_match_conditional_without_coverage_boundary_count": len(
            row_statement_match_conditional_without_coverage_boundary
        ),
        "row_statement_match_missing_statement_digest_count": len(row_statement_match_missing_statement_digest),
        "row_statement_match_wrong_statement_digest_count": len(row_statement_match_wrong_statement_digest),
        "row_assumption_provenance_missing_count": len(row_assumption_provenance_missing),
        "row_assumption_provenance_stale_count": len(row_assumption_provenance_stale),
        "row_assumption_provenance_mismatch_count": len(row_assumption_provenance_mismatch),
        "row_assumption_provenance_uncertain_count": len(row_assumption_provenance_uncertain),
        "row_assumption_provenance_unknown_count": len(row_assumption_provenance_unknown),
        "row_assumption_provenance_conditional_count": len(row_assumption_provenance_conditional),
        "row_assumption_provenance_conditional_without_coverage_boundary_count": len(
            row_assumption_provenance_conditional_without_coverage_boundary
        ),
        "stale_inventory": stale_inventory,
        "stale_surface": stale_surface,
        "recorded_source_coverage_mode": recorded_source_coverage_mode,
        "source_coverage_mode_mismatch": source_coverage_mode_mismatch,
        "source_artifact_current": source_artifact_current,
        "audit_kind": audit_kind,
        "audit_source_grounded": audit_source_grounded,
        "audit_is_scaffold": audit_is_scaffold,
        "prompt_version": str(audit.get("prompt_version") or "").strip(),
        "prompt_version_stale": audit_prompt_version_stale,
        "missing_source_grounded_audit": missing_source_grounded_audit,
        "coverage_source_input_error_count": len(coverage_source_input_errors),
        "coverage_source_input_errors": coverage_source_input_errors,
        "audit_metadata_missing": audit_metadata_missing,
        "defect_support_audit_required": quarantine_support_requested,
        "defect_support_audit_source": str(
            defect_support_audit.get("source") or ""
        ),
        "defect_support_prompt_version": str(
            defect_support_audit.get("prompt_version") or ""
        ),
        "defect_support_prompt_version_stale": bool(
            defect_support_audit.get("prompt_version_stale")
        ),
        "defect_support_audit_metadata_error": defect_support_audit_metadata_error,
        "coverage_metadata_missing_count": len(coverage_metadata_missing),
        "coverage_route_mismatch_count": len(coverage_route_mismatch),
        "corrected_target_coverage_error_count": len(
            corrected_target_coverage_errors
        ),
        "coverage_row_signature_error_count": len(coverage_row_signature_errors),
        "missing_coverage": missing_coverage,
        "extra_coverage": extra_coverage,
        "out_of_mode_coverage": out_of_mode_coverage,
        "conditional_boundary": conditional_boundary,
        "corrected_target_covered": corrected_target_covered,
        "support_only": support_only,
        "audited_proof_support": audited_proof_support,
        "invalid_proof_support": invalid_proof_support,
        "quarantined_defect_support": quarantined_defect_support,
        "invalid_quarantined_defect_support": invalid_quarantined_defect_support,
        "defect_support_judgment_errors": defect_support_judgment_errors,
        "quarantined_defect_direct_coverage": quarantined_defect_direct_coverage,
        "user_approved_scope_exclusions": user_approved_scope_exclusions,
        "inventory_missing_source_url": inventory_missing_source_url,
        "inventory_missing_source_provenance": inventory_missing_source_provenance,
        "inventory_unknown_source_kind": inventory_unknown_source_kind,
        "source_scope_classification_errors": source_scope_classification_errors,
        "source_presentation_classification_errors": source_presentation_classification_errors,
        "user_approved_scope_exclusion_errors": user_approved_scope_exclusion_errors,
        "source_anchor_evidence_errors": source_anchor_evidence_errors,
        "source_named_result_inventory_errors": source_named_result_inventory_errors,
        "missing_statement_digest": missing_statement_digest,
        "stale_statement": stale_statement,
        "stale_source_items": stale_source_items,
        "unverified_reused_source_items": unverified_reused_source_items,
        "semantic_reuse_source_anchor_errors": semantic_reuse_anchor_errors,
        "legacy_unpinned_items": legacy_unpinned_items,
        "invalid_row_links": invalid_row_links,
        "partial": partial,
        "missing": missing,
        "uncertain": uncertain,
        "unknown": unknown,
        "covered_without_rows": covered_without_rows,
        "covered_without_reason": covered_without_reason,
        "covered_with_seed_reason": covered_with_seed_reason,
        "covered_without_source_evidence": covered_without_source_evidence,
        "result_covered_without_proof_rows": result_covered_without_proof_rows,
        "result_covered_only_by_definition_rows": result_covered_only_by_definition_rows,
        "result_matched_only_by_definition_rows": result_matched_only_by_definition_rows,
        "semantic_contract_spec_proof_links": semantic_contract_spec_proof_links,
        "support_without_declarations": support_without_declarations,
        "support_without_reason": support_without_reason,
        "support_without_source_evidence": support_without_source_evidence,
        "support_only_named_claims": support_only_named_claims,
        "support_only_required_source_items": support_only_required_source_items,
        "required_out_of_scope": required_out_of_scope,
        "out_of_scope_without_reason": out_of_scope_without_reason,
        "out_of_scope_without_source_evidence": out_of_scope_without_source_evidence,
        "coverage_metadata_missing": coverage_metadata_missing,
        "coverage_route_mismatch": coverage_route_mismatch,
        "corrected_target_coverage_errors": corrected_target_coverage_errors,
        "coverage_row_signature_errors": coverage_row_signature_errors,
        "row_statement_match_links": row_statement_match_links,
        "row_statement_match_missing": row_statement_match_missing,
        "row_statement_match_stale": row_statement_match_stale,
        "row_statement_match_mismatch": row_statement_match_mismatch,
        "row_statement_match_uncertain": row_statement_match_uncertain,
        "row_statement_match_unknown": row_statement_match_unknown,
        "row_statement_match_conditional": row_statement_match_conditional,
        "row_statement_match_conditional_without_coverage_boundary": row_statement_match_conditional_without_coverage_boundary,
        "row_statement_match_missing_statement_digest": row_statement_match_missing_statement_digest,
        "row_statement_match_wrong_statement_digest": row_statement_match_wrong_statement_digest,
        "row_assumption_provenance_missing": row_assumption_provenance_missing,
        "row_assumption_provenance_stale": row_assumption_provenance_stale,
        "row_assumption_provenance_mismatch": row_assumption_provenance_mismatch,
        "row_assumption_provenance_uncertain": row_assumption_provenance_uncertain,
        "row_assumption_provenance_unknown": row_assumption_provenance_unknown,
        "row_assumption_provenance_conditional": row_assumption_provenance_conditional,
        "row_assumption_provenance_conditional_without_coverage_boundary": row_assumption_provenance_conditional_without_coverage_boundary,
        "source": str(audit.get("source") or "") if audit_items else "",
        "paper_statement_inventory_sha256": inventory_hash,
        "recorded_paper_statement_inventory_sha256": recorded_inventory_hash,
        "review_surface_sha256": surface_hash,
        "recorded_review_surface_sha256": recorded_surface_hash,
        "has_completed_audit": bool(audit_items),
        "needs_attention": coverage_needs_attention,
        "source_to_lean_needs_attention": source_to_lean_needs_attention,
    }


def assumption_surface_digest(items: list[ReviewItem]) -> str:
    """Return a stable digest of the paper-assumption review surface."""

    payload = [
        {
            "name": item.name,
            "kind": item.kind,
            "lean_statement": normalize_statement(item.lean_statement),
            "paper_statement": normalize_statement(item.paper_statement),
            "source_status": normalize_statement(item.source_status),
            "source_note": normalize_statement(item.source_note),
        }
        for item in sorted(items, key=lambda row: row.name)
        if item.is_assumption
    ]
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def assumption_provenance_audit_summary(folder: Path, items: list[ReviewItem]) -> dict[str, Any]:
    """Summarize whether explicit assumptions have source-assumption judgments."""

    configured_names = review_assumption_names(folder)
    assumption_items = [
        item
        for item in items
        if item.is_assumption or item.name in configured_names or is_assumption_item_name(item.name)
    ]
    item_names = {item.name for item in assumption_items}
    missing_rows = sorted(configured_names - item_names)
    unlisted_rows = sorted(
        item.name
        for item in assumption_items
        if is_assumption_item_name(item.name) and item.name not in configured_names
    )
    missing_judgment: list[str] = []
    stale_judgment: list[str] = []
    not_paper_assumption: list[str] = []
    uncertain: list[str] = []
    unknown: list[str] = []
    partial_boundary_premises: list[str] = []
    unresolved_premises: list[str] = []
    missing_source_location_premises: list[str] = []
    premise_judgment_count = 0
    paper_assumptions = 0
    paper_conditions = 0
    documented_additional_assumptions = 0
    documented_caveats = 0
    partial_boundaries = 0

    for item in assumption_items:
        judgment = str(item.llm_assumption_judgment or "").strip()
        if not judgment:
            missing_judgment.append(item.name)
            continue
        if item.llm_assumption_stale:
            stale_judgment.append(item.name)
        if judgment == "paper_assumption":
            paper_assumptions += 1
        elif judgment == "paper_condition":
            paper_conditions += 1
        elif judgment == "documented_additional_assumption":
            documented_additional_assumptions += 1
        elif judgment == "documented_caveat":
            documented_caveats += 1
        elif judgment == "partial_boundary":
            partial_boundaries += 1
        elif judgment == "not_paper_assumption":
            not_paper_assumption.append(item.name)
        elif judgment == "uncertain":
            uncertain.append(item.name)
        else:
            unknown.append(item.name)
        premise_judgments = item.llm_assumption_premise_judgments or {}
        if not isinstance(premise_judgments, dict):
            premise_judgments = {}
        for premise, raw_premise_judgment in sorted(premise_judgments.items()):
            premise_judgment = ""
            source_location = ""
            if isinstance(raw_premise_judgment, dict):
                premise_judgment = str(raw_premise_judgment.get("judgment") or "").strip()
                source_location = str(raw_premise_judgment.get("source_location") or "").strip()
            else:
                premise_judgment = _normalize_assumption_judgment(raw_premise_judgment)
            premise_judgment_count += 1
            label = f"{item.name}: {premise}"
            if premise_judgment == "partial_boundary":
                partial_boundary_premises.append(label)
                continue
            if premise_judgment not in APPROVED_ASSUMPTION_PREMISE_JUDGMENTS:
                unresolved_premises.append(f"{label} [{premise_judgment or 'missing'}]")
                continue
            if (
                premise_judgment in SOURCE_TEXT_ASSUMPTION_PREMISE_JUDGMENTS
                and not source_location
            ):
                missing_source_location_premises.append(label)

    needs_attention = bool(
        missing_rows
        or unlisted_rows
        or missing_judgment
        or stale_judgment
        or not_paper_assumption
        or uncertain
        or unknown
        or unresolved_premises
        or missing_source_location_premises
    )
    return {
        "row_count": len(assumption_items),
        "configured_count": len(configured_names),
        "paper_assumption_count": paper_assumptions,
        "paper_condition_count": paper_conditions,
        "documented_additional_assumption_count": documented_additional_assumptions,
        "documented_caveat_count": documented_caveats,
        "partial_boundary_count": partial_boundaries,
        "missing_rows_count": len(missing_rows),
        "unlisted_rows_count": len(unlisted_rows),
        "missing_judgment_count": len(missing_judgment),
        "stale_judgment_count": len(stale_judgment),
        "not_paper_assumption_count": len(not_paper_assumption),
        "uncertain_count": len(uncertain),
        "unknown_count": len(unknown),
        "premise_judgment_count": premise_judgment_count,
        "partial_boundary_premise_count": len(partial_boundary_premises),
        "unresolved_premise_count": len(unresolved_premises),
        "missing_source_location_premise_count": len(missing_source_location_premises),
        "missing_rows": missing_rows,
        "unlisted_rows": unlisted_rows,
        "missing_judgment": missing_judgment,
        "stale_judgment": stale_judgment,
        "not_paper_assumption": not_paper_assumption,
        "uncertain": uncertain,
        "unknown": unknown,
        "partial_boundary_premises": partial_boundary_premises,
        "unresolved_premises": unresolved_premises,
        "missing_source_location_premises": missing_source_location_premises,
        "has_completed_audit": bool(assumption_items) and not missing_judgment,
        "assumption_surface_sha256": assumption_surface_digest(assumption_items),
        "needs_attention": needs_attention,
        "has_warning": needs_attention,
    }


def describe_log_target(log_file: Path | None, paper: str | None = None) -> str:
    """User-visible label for where logs are persisted/read."""

    if log_file is not None:
        return str(log_file)
    if paper:
        try:
            return str(paper_review_log_file(paper))
        except ValueError:
            pass
    return "per-paper traces in each folder at <Paper>/.review_traces/paper_theorem_validations.jsonl"


def read_all_log_entries(
    paper_filter: str | None, log_file: Path | None
) -> list[dict[str, Any]]:
    """Collect review logs across selected papers or from an override log file."""

    if log_file is not None:
        entries = read_log_entries(log_file)
        if paper_filter:
            entries = [entry for entry in entries if entry.get("paper") == paper_filter]
        return entries

    entries: list[dict[str, Any]] = []
    for folder in iter_paper_folders(paper_filter):
        entries.extend(read_log_entries(paper_review_log_file(folder.name)))
    entries.sort(key=lambda row: row.get("timestamp", ""))
    return entries


def _human_review_short_name(value: object) -> str:
    return str(value or "").strip().rsplit(".", 1)[-1]


def human_review_library_prerequisites(
    folder: Path,
    claims: Iterable[Mapping[str, Any]],
    *,
    require_build: bool = True,
    semantic_targets_override: Mapping[str, Mapping[str, Any]] | None = None,
    semantic_target_errors_override: Mapping[str, str] | None = None,
    source_map_payload: Mapping[str, Any] | None = None,
    ledger_payload: Mapping[str, Any] | None = None,
    declaration_sources_override: Mapping[str, Mapping[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    """Project saved graph targets into source-connected library cards."""

    if semantic_targets_override is None:
        raise ValueError(
            "dashboard library prerequisites require saved Lean graph targets"
        )
    return _prepared_library_prerequisites(
        folder,
        claims,
        require_build=require_build,
        semantic_targets_override=semantic_targets_override,
        semantic_target_errors_override=semantic_target_errors_override,
        source_map_payload=source_map_payload,
        ledger_payload=ledger_payload,
        declaration_sources_override=declaration_sources_override,
    )


def _human_review_intake_order(folder: Path) -> dict[str, int]:
    """Load the explicit source-claim reading order for human review.

    An intake freeze remains the strongest source of a recorded DAG order.  A
    v11 interface without such a freeze may declare its claim order in
    ``review_surface.include_names``.  This is an explicit presentation/DAG
    order, not an inferred declaration-name order; the packet rejects any
    section headings that would subsequently reorder it.
    """

    payload = _dashboard_json_payload(folder / PAPER_AUDIT_DIR / "intake_freeze.json")
    raw_items = payload.get("items") if isinstance(payload, Mapping) else None
    order: dict[str, int] = {}
    if isinstance(raw_items, list):
        for raw_item in raw_items:
            if not isinstance(raw_item, Mapping):
                continue
            rank = raw_item.get("dependency_order")
            if not isinstance(rank, int) or rank < 0:
                continue
            for field in ("spec_declaration", "proof_declaration"):
                name = _human_review_short_name(raw_item.get(field))
                if name:
                    order[name] = rank
        if order:
            return order
    status = _dashboard_json_payload(folder / DEFAULT_PAPER_STATUS_FILE)
    surface = status.get("review_surface") if isinstance(status, Mapping) else None
    configured = surface.get("include_names") if isinstance(surface, Mapping) else None
    if not isinstance(configured, list):
        return {}
    for rank, raw_name in enumerate(configured, start=1):
        name = _human_review_short_name(raw_name)
        if name and name not in order:
            order[name] = rank
    return order


def human_review_claim_items(
    folder: Path,
    items: list[ReviewItem],
    *,
    semantic_reuse_authority: CurrentSemanticReuseAuthority | None = None,
) -> list[dict[str, Any]]:
    """Project raw Lean declarations to source-claim and assumption review rows.

    A transparent ``Spec`` and its paired theorem are deliberately separate
    Lean declarations: the former is the auditable paper statement and the
    latter proves it.  Showing both as independent human rows duplicates the
    same source claim.  This presentation projection keeps the raw list intact
    for evidence gates while showing the Spec once, with the proof endpoint
    named on that row.  The source-map/intake order is the claim-DAG reading
    order; unmapped legacy declarations remain visible after those claims.
    Explicit source-model assumptions retain their separate provenance
    category downstream.
    """

    item_by_full_name = {
        item.full_name: item for item in items if item.full_name
    }
    source_map = paper_statement_map_payload(folder)
    raw_map_items = source_map.get("items") if isinstance(source_map, Mapping) else None
    map_records = (
        list(raw_map_items.items()) if isinstance(raw_map_items, Mapping) else []
    )
    typed_routes = (
        EvidenceRouteSet.from_source_map(source_map)
        if isinstance(source_map, Mapping)
        and typed_route_validation_required(source_map)
        else None
    )
    route_by_source_item = (
        typed_routes.by_source_item() if typed_routes is not None else {}
    )
    proof_support_declarations = {
        str(declaration).strip()
        for _source_key, raw_record in map_records
        if isinstance(raw_record, Mapping)
        and _source_inventory_item_is_explicit_proof_support(dict(raw_record))
        for declaration in _normalize_string_list(
            raw_record.get("support_lean_declarations")
        )
        if str(declaration).strip()
    }
    intake_order = _human_review_intake_order(folder)
    selected: list[tuple[int, int, dict[str, Any]]] = []
    covered: set[str] = set()
    for source_index, (source_key, raw_record) in enumerate(map_records):
        if not isinstance(raw_record, Mapping):
            continue
        typed_route = route_by_source_item.get(str(source_key))
        if typed_route is not None:
            spec = typed_route.spec_declaration
            proof = typed_route.evidence_declaration
        else:
            contract = raw_record.get("semantic_contract")
            spec = (
                str(contract.get("spec_declaration") or "").strip()
                if isinstance(contract, Mapping)
                else ""
            )
            proof = (
                str(contract.get("evidence_declaration") or "").strip()
                if isinstance(contract, Mapping)
                else ""
            )
        if not spec:
            routes = raw_record.get("spec_lean_declarations")
            if isinstance(routes, list):
                spec = next((str(route).strip() for route in routes if str(route).strip()), "")
        item = item_by_full_name.get(spec)
        if item is None:
            continue
        record = dict(item.__dict__)
        # This is a coverage identity, not reviewer-facing prose.  It lets
        # closeout verify that every selected byte-pinned source item has its
        # own current source-to-Spec comparison; neighbouring bundle context
        # never supplies coverage for another map item.
        record["human_claim_source_key"] = str(source_key)
        record["human_claim_title"] = str(
            raw_record.get("source_item") or raw_record.get("title") or source_key
        ).strip()
        record["human_claim_proof_endpoint"] = proof
        record["human_claim_dag_order"] = intake_order.get(
            _human_review_short_name(spec), source_index + 1
        )
        selected.append((int(record["human_claim_dag_order"]), source_index, record))
        covered.add(spec)
        if proof:
            covered.add(proof)

    for fallback_index, item in enumerate(items, start=len(selected)):
        if (
            item.full_name in covered
            or item.full_name in proof_support_declarations
        ):
            continue
        record = dict(item.__dict__)
        record["human_claim_title"] = item.name
        record["human_claim_proof_endpoint"] = ""
        record["human_claim_dag_order"] = 20_000 + fallback_index
        selected.append((20_000 + fallback_index, fallback_index, record))
    records = [record for _rank, _index, record in sorted(selected, key=lambda entry: entry[:2])]
    specification_names = sorted(
        {
            str(record.get("full_name") or "").strip()
            for record in records
            if str(record.get("full_name") or "").strip().endswith("Spec")
        }
    )
    if not specification_names:
        return records
    # Rendering consumes only an authenticated retained display.  Missing
    # packet transport remains visible on the row; a dashboard request never
    # starts Lean or replays the retired native packet producer.
    try:
        from scripts.current_closeout import review_surface

        packet_cache = review_surface._current_packet_lean_cache(
            folder,
            specification_names,
            semantic_reuse_authority=semantic_reuse_authority,
        )
        raw_targets = (
            packet_cache.get("semantic_targets")
            if isinstance(packet_cache, Mapping)
            else None
        )
        if isinstance(raw_targets, Mapping) and set(raw_targets) == set(
            specification_names
        ):
            targets = raw_targets
            expansion_error = ""
        else:
            targets = {}
            expansion_error = (
                "retained Lean-expanded Spec targets are unavailable; prepare "
                "the current Lean review graph before opening this dashboard"
            )
    except Exception as exc:  # Keep malformed retained data visible on every row.
        targets = {}
        expansion_error = str(exc)
    for record in records:
        name = str(record.get("full_name") or "").strip()
        target = targets.get(name)
        if target is not None:
            record["semantic_expanded_statement"] = str(target.get("display") or "")
            record["semantic_expanded_statement_sha256"] = str(
                target.get("display_sha256") or ""
            )
            record["review_claim_manifest_sha256"] = str(
                target.get("review_claim_manifest_sha256") or ""
            )
            record["review_claim_atoms_sha256"] = str(
                target.get("review_claim_atoms_sha256") or ""
            )
            record["review_claim_atoms"] = list(
                target.get("review_claim_atoms", ())
            )
            try:
                record["source_review_target_sha256"] = statement_digest(
                    review_claim_target_text(target)
                )
            except ValueError:
                record["source_review_target_sha256"] = ""
            record["library_review_owner_declarations"] = list(
                target.get("library_declarations", ())
            )
            record["paper_semantic_prerequisite_declarations"] = list(
                target.get("prerequisite_declarations", ())
            )
            record["semantic_target_kind"] = str(
                target.get("semantic_target_kind") or "spec_proposition"
            )
            record["semantic_review_declaration"] = str(
                target.get("semantic_review_declaration") or name
            )
            record["semantic_target_protocol"] = str(
                target.get("lean_target_protocol")
                or V11_RAW_SOURCE_SPEC_LEAN_TARGET_PROTOCOL
            )
        elif name.endswith("Spec"):
            record["semantic_expansion_error"] = (
                expansion_error or "Lean did not return a complete semantic expansion"
            )
    return records


def human_review_presentation_sections(
    folder: Path,
    claim_rows: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    """Return source-claim headings without disturbing the approved DAG order.

    ``presentation_sections`` may distinguish main text from an appendix, but
    it is not a second ordering authority.  The approved source/DAG
    linearization remains fixed; headings are inserted around its contiguous
    runs.  A title can therefore recur as ``(continued)`` when a prerequisite
    from another source section must be shown first.  Explicit source-model
    assumptions are rendered in one automatic ``Source-model assumptions``
    section; they use a separate provenance lane and therefore do not belong
    to the source-claim section partition.
    """

    status = _dashboard_json_payload(folder / DEFAULT_PAPER_STATUS_FILE)
    review_surface = status.get("review_surface") if isinstance(status, Mapping) else None
    configured = (
        review_surface.get("presentation_sections")
        if isinstance(review_surface, Mapping)
        else None
    )
    configured_assumption_names = review_assumption_names(folder)

    def is_assumption_card(row: Mapping[str, Any]) -> bool:
        full_name = str(row.get("full_name") or "").strip()
        short_name = full_name.rsplit(".", 1)[-1]
        return bool(
            row.get("is_assumption")
            or full_name in configured_assumption_names
            or short_name in configured_assumption_names
        )

    source_claim_rows = [row for row in claim_rows if not is_assumption_card(row)]
    assumption_rows = [row for row in claim_rows if is_assumption_card(row)]
    ordered_names = [
        str(row.get("full_name") or "").strip() for row in source_claim_rows
    ]
    assumption_names = [
        str(row.get("full_name") or "").strip() for row in assumption_rows
    ]

    def append_assumption_section(
        sections: list[dict[str, Any]],
    ) -> list[dict[str, Any]]:
        if assumption_names:
            sections.append(
                {
                    "title": "Source-model assumptions",
                    "kind": "source_model_assumptions",
                    "names": assumption_names,
                }
            )
        return sections

    if not configured:
        sections = [{"title": "Source claims", "names": ordered_names}] if ordered_names else []
        return append_assumption_section(sections)
    if not isinstance(configured, list) or not configured:
        raise ValueError("review_surface.presentation_sections must be a nonempty list")

    lookup: dict[str, str] = {}
    for full_name in ordered_names:
        short_name = full_name.rsplit(".", 1)[-1]
        for candidate in (
            full_name,
            short_name,
            short_name[: -len("Spec")] if short_name.endswith("Spec") else "",
        ):
            if candidate:
                lookup[candidate] = full_name

    section_for_name: dict[str, str] = {}
    seen: set[str] = set()
    for raw_section in configured:
        if not isinstance(raw_section, Mapping):
            raise ValueError("each presentation section must be an object")
        title = str(raw_section.get("title") or "").strip()
        raw_names = raw_section.get("names")
        if not title or not isinstance(raw_names, list) or not raw_names:
            raise ValueError("each presentation section needs a title and nonempty names")
        for raw_name in raw_names:
            full_name = lookup.get(str(raw_name).strip())
            if not full_name:
                raise ValueError(
                    "presentation section references an unknown source card: "
                    + str(raw_name)
                )
            if full_name in seen:
                raise ValueError("presentation sections repeat source card: " + full_name)
            seen.add(full_name)
            section_for_name[full_name] = title
    if seen != set(ordered_names):
        missing = [name for name in ordered_names if name not in seen]
        raise ValueError(
            "presentation sections must cover every source card; missing "
            + ", ".join(missing)
        )
    sections: list[dict[str, Any]] = []
    used_titles: dict[str, int] = {}
    for full_name in ordered_names:
        configured_title = section_for_name[full_name]
        if (
            sections
            and str(sections[-1]["title"]).split(" (continued", 1)[0]
            == configured_title
        ):
            sections[-1]["names"].append(full_name)
            continue
        used_titles[configured_title] = used_titles.get(configured_title, 0) + 1
        occurrence = used_titles[configured_title]
        displayed_title = (
            configured_title
            if occurrence == 1
            else configured_title + " (continued" + ("" if occurrence == 2 else " " + str(occurrence - 1)) + ")"
        )
        sections.append({"title": displayed_title, "names": [full_name]})
    return append_assumption_section(sections)


def browser_review_item(item: Mapping[str, Any]) -> dict[str, Any]:
    """Return the card data needed by the browser, without Lean audit internals.

    ``lean_signature_manifest`` can contain a large recursive elaboration
    graph.  It is a server-side evidence input, not a human-review card
    field; serializing it with every card made an otherwise compact dashboard
    take tens of megabytes and delayed the page that a reviewer sees.
    """

    payload = dict(item)
    payload.pop("lean_signature_manifest", None)
    return payload


@dataclass(frozen=True)
class _CurrentSemanticReviewSurface:
    """Current claim and prerequisite evidence used by one renderer."""

    human_claims: list[dict[str, Any]]
    library_prerequisites: list[dict[str, Any]]
    library_summary: dict[str, Any]
    paper_prerequisites: list[dict[str, Any]] = dataclass_field(default_factory=list)
    paper_prerequisite_summary: dict[str, Any] = dataclass_field(default_factory=dict)


@dataclass(frozen=True)
class _PreparedDashboardSurface:
    """Typed browser projection and its nonaccepting display summaries."""

    all_claims: list[dict[str, Any]]
    selected_claims: list[dict[str, Any]]
    semantic_surface: _CurrentSemanticReviewSurface
    presentation_sections: list[dict[str, Any]]
    slices: list[dict[str, Any]]
    surface_audit: dict[str, Any]
    statement_audit: dict[str, Any]
    paper_coverage_audit: dict[str, Any]
    assumption_audit: dict[str, Any]


def _prepared_claim_semantic_state(row: Mapping[str, Any]) -> str:
    """Return the fail-closed current semantic state of one prepared card."""

    judgment = _normalize_llm_match_judgment(row.get("llm_match_judgment"))
    if judgment == APPROVED_CORRECTED_TARGET_MATCH:
        judgment = "matches"
    source_text = str(
        row.get("verbatim_source_input") or row.get("paper_statement") or ""
    )
    lean_text = str(
        row.get("semantic_expanded_statement") or row.get("lean_statement") or ""
    )
    source_digest = str(row.get("source_input_bundle_sha256") or "").strip()
    lean_digest = str(
        row.get("semantic_expanded_statement_sha256") or ""
    ).strip()
    current = bool(
        row.get("llm_match_current")
        and not row.get("llm_match_stale")
        and source_text
        and lean_text
        and SOURCE_ARTIFACT_SHA256_RE.fullmatch(source_digest)
        and SOURCE_ARTIFACT_SHA256_RE.fullmatch(lean_digest)
        and str(row.get("llm_match_lean_statement_sha256") or "").strip()
        == lean_digest
        and str(row.get("llm_match_paper_statement_sha256") or "").strip()
        == statement_digest(source_text)
    )
    if not current:
        return "stale" if judgment else "missing"
    if judgment in {"matches", "mismatch", "uncertain"}:
        return judgment
    return "unknown"


def _prepared_statement_audit_summary(
    claims: Iterable[Mapping[str, Any]],
    library_summary: Mapping[str, Any],
    paper_prerequisite_summary: Mapping[str, Any],
    *,
    authority: str,
) -> dict[str, Any]:
    """Summarize the cards on screen without replaying strict audit ledgers."""

    rows = [dict(row) for row in claims]
    buckets: dict[str, list[str]] = {
        "matches": [],
        "mismatch": [],
        "uncertain": [],
        "stale": [],
        "missing": [],
        "unknown": [],
    }
    for row in rows:
        name = str(row.get("name") or row.get("full_name") or "unnamed")
        buckets[_prepared_claim_semantic_state(row)].append(name)
    needs_attention = bool(
        buckets["mismatch"]
        or buckets["uncertain"]
        or buckets["stale"]
        or buckets["missing"]
        or buckets["unknown"]
        or library_summary.get("needs_attention")
        or paper_prerequisite_summary.get("needs_attention")
    )
    return {
        "row_count": len(rows),
        "draft_count": 0,
        "judgment_count": len(rows) - len(buckets["missing"]),
        "matches": len(buckets["matches"]),
        "mismatch_count": len(buckets["mismatch"]),
        "unresolved_mismatch_count": len(buckets["mismatch"]),
        "uncertain_count": len(buckets["uncertain"]),
        "unknown_count": len(buckets["unknown"]),
        "missing_judgment_count": len(buckets["missing"]),
        "stale_judgment_count": len(buckets["stale"]),
        "mismatch": buckets["mismatch"],
        "unresolved_mismatch": buckets["mismatch"],
        "uncertain": buckets["uncertain"],
        "unknown": buckets["unknown"],
        "missing_judgment": buckets["missing"],
        "stale_judgment": buckets["stale"],
        "has_completed_audit": bool(rows) and not needs_attention,
        "library_prerequisites": dict(library_summary),
        "paper_prerequisites": dict(paper_prerequisite_summary),
        "presentation_only": True,
        "presentation_authority": authority,
        "needs_attention": needs_attention,
    }


def _prepared_surface_audit_summary(
    claims: Iterable[Mapping[str, Any]],
    *,
    authority: str,
    accepted_graph: bool,
) -> dict[str, Any]:
    """Describe typed route selection without reloading a legacy sidecar."""

    rows = list(claims)
    row_count = len(rows)
    audit_required = row_count > REVIEW_SURFACE_LLM_AUDIT_THRESHOLD
    oversize = row_count >= REVIEW_SURFACE_WARN_THRESHOLD
    recorded = accepted_graph and audit_required
    missing_required = audit_required and not recorded
    return {
        "row_count": row_count,
        "llm_threshold": REVIEW_SURFACE_LLM_AUDIT_THRESHOLD,
        "warn_threshold": REVIEW_SURFACE_WARN_THRESHOLD,
        "audit_required": audit_required,
        "oversize": oversize,
        "missing_required": missing_required,
        "stale": False,
        "judgment": "passes" if recorded else "",
        "unknown_judgment": False,
        "reason": "",
        "source": "accepted obligation graph" if recorded else "",
        "has_completed_audit": recorded,
        "presentation_only": True,
        "presentation_authority": authority,
        "needs_attention": missing_required,
        "has_warning": missing_required or oversize,
    }


def _prepared_paper_coverage_summary(
    claims: Iterable[Mapping[str, Any]],
    paper_prerequisites: Iterable[Mapping[str, Any]],
    library_prerequisites: Iterable[Mapping[str, Any]],
    *,
    authority: str,
) -> dict[str, Any]:
    """Report exact source-card coverage without replaying strict manifests."""

    cards: list[tuple[str, str, str]] = []
    for row in claims:
        cards.append(
            (
                str(
                    row.get("source_item_key")
                    or row.get("human_claim_source_key")
                    or ""
                ).strip(),
                str(row.get("name") or row.get("full_name") or "unnamed"),
                _prepared_claim_semantic_state(row),
            )
        )
    for entry in [*paper_prerequisites, *library_prerequisites]:
        judgment = str(entry.get("semantic_judgment") or "").strip()
        if not entry.get("semantic_current"):
            state = "stale" if judgment and judgment != "not recorded" else "missing"
        elif judgment in {"matches", "mismatch", "uncertain"}:
            state = judgment
        else:
            state = "unknown"
        cards.append(
            (
                str(entry.get("source_item") or "").strip(),
                str(entry.get("lean_name") or "unnamed prerequisite"),
                state,
            )
        )

    by_source_item: dict[str, list[tuple[str, str]]] = {}
    anonymous: list[tuple[str, str]] = []
    for source_item, label, state in cards:
        if source_item:
            by_source_item.setdefault(source_item, []).append((label, state))
        else:
            anonymous.append((label, state))
    states: dict[str, str] = {}
    for source_item, rows in by_source_item.items():
        row_states = {state for _label, state in rows}
        if "mismatch" in row_states:
            states[source_item] = "mismatch"
        elif "uncertain" in row_states:
            states[source_item] = "uncertain"
        elif "stale" in row_states:
            states[source_item] = "stale"
        elif "missing" in row_states:
            states[source_item] = "missing"
        elif "unknown" in row_states:
            states[source_item] = "unknown"
        elif row_states == {"matches"}:
            states[source_item] = "matches"
        else:
            states[source_item] = "unknown"
    for index, (label, state) in enumerate(anonymous, start=1):
        states[f"[unbound {index}] {label}"] = state if state != "matches" else "missing"

    names = lambda state: sorted(
        source_item for source_item, value in states.items() if value == state
    )
    covered = names("matches")
    mismatch = names("mismatch")
    uncertain = names("uncertain")
    stale = names("stale")
    missing = names("missing")
    unknown = names("unknown")
    needs_attention = bool(mismatch or uncertain or stale or missing or unknown)
    return {
        "inventory_count": len(states),
        "coverage_item_count": len(cards),
        "covered_count": len(covered),
        "direct_covered_count": len(covered),
        "missing_count": len(missing),
        "uncertain_count": len(uncertain),
        "unknown_count": len(unknown),
        "stale_statement_count": len(stale),
        "semantic_mismatch_count": len(mismatch),
        "covered": covered,
        "missing": missing,
        "uncertain": uncertain,
        "unknown": unknown,
        "stale_statement": stale,
        "semantic_mismatch": mismatch,
        "has_completed_audit": bool(states) and not needs_attention,
        "presentation_only": True,
        "presentation_authority": authority,
        "needs_attention": needs_attention,
        "source_to_lean_needs_attention": needs_attention,
    }


def _prepared_assumption_audit_summary(
    claims: Iterable[Mapping[str, Any]],
    *,
    authority: str,
    accepted_graph: bool,
) -> dict[str, Any]:
    """Expose recorded assumption status without pretending to rerun its gate."""

    assumptions = [dict(row) for row in claims if bool(row.get("is_assumption"))]
    missing = [] if accepted_graph else [
        str(row.get("name") or row.get("full_name") or "unnamed")
        for row in assumptions
    ]
    digest_payload = [
        {
            "name": str(row.get("full_name") or row.get("name") or ""),
            "source_input_bundle_sha256": str(
                row.get("source_input_bundle_sha256") or ""
            ),
            "semantic_expanded_statement_sha256": str(
                row.get("semantic_expanded_statement_sha256") or ""
            ),
        }
        for row in assumptions
    ]
    surface_sha256 = hashlib.sha256(
        json.dumps(
            digest_payload,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()
    return {
        "row_count": len(assumptions),
        "configured_count": len(assumptions),
        # The accepted graph proves the recorded premise lane complete, but
        # this presentation projection does not reinterpret its finer
        # paper-assumption/paper-condition classification.
        "paper_assumption_count": 0,
        "missing_judgment_count": len(missing),
        "missing_judgment": missing,
        "has_completed_audit": bool(assumptions) and accepted_graph,
        "assumption_surface_sha256": surface_sha256,
        "presentation_only": True,
        "presentation_authority": authority,
        "needs_attention": bool(missing),
        "has_warning": bool(missing),
    }


def _typed_prepared_dashboard_surface(
    folder: Path,
    slice_filter: str | None,
) -> _PreparedDashboardSurface | None:
    """Project a role-typed packet surface without the base row-cache parser.

    Untyped historical papers return ``None`` and retain their parser-backed
    dashboard.  Once a source map selects the role-typed protocol, a missing
    or invalid prepared surface fails visibly instead of falling through to a
    second Python/Lean discovery path.
    """

    source_map = paper_statement_map_payload(folder)
    if not typed_route_validation_required(source_map):
        return None
    from scripts.current_closeout.review_surface import prepared_review_surface

    prepared = prepared_review_surface(folder.name)
    all_claims = attach_review_slices_to_mappings(
        folder,
        [
            {
                **dict(row),
                "line_number": int(row.get("line_number") or 0),
            }
            for row, _records, _proof in prepared.claim_rows
        ],
    )
    selected_claims = filter_mapping_rows_by_slice(
        all_claims, folder.name, slice_filter
    )
    selected_names = {
        str(row.get("full_name") or "").strip() for row in selected_claims
    }
    presentation_sections: list[dict[str, Any]] = []
    for raw_title, section_rows in prepared.claim_sections:
        names = [
            str(row.get("full_name") or "").strip()
            for row, _records, _proof in section_rows
            if str(row.get("full_name") or "").strip() in selected_names
        ]
        if not names:
            continue
        title = str(raw_title or "Source claims")
        section: dict[str, Any] = {"title": title, "names": names}
        if title == "Source-model assumptions":
            section["kind"] = "source_model_assumptions"
        presentation_sections.append(section)
    library_prerequisites = [
        dict(entry) for entry in prepared.library_prerequisites
    ]
    paper_prerequisites = [dict(entry) for entry in prepared.paper_prerequisites]
    library_summary = semantic_prerequisite_review_summary(library_prerequisites)
    paper_summary = semantic_prerequisite_review_summary(paper_prerequisites)
    semantic_surface = _CurrentSemanticReviewSurface(
        human_claims=selected_claims,
        library_prerequisites=library_prerequisites,
        library_summary=library_summary,
        paper_prerequisites=paper_prerequisites,
        paper_prerequisite_summary=paper_summary,
    )
    accepted_graph = prepared.recorded_graph_projection is not None
    return _PreparedDashboardSurface(
        all_claims=all_claims,
        selected_claims=selected_claims,
        semantic_surface=semantic_surface,
        presentation_sections=presentation_sections,
        slices=summarize_mapping_review_slices(all_claims),
        surface_audit=_prepared_surface_audit_summary(
            all_claims,
            authority=prepared.presentation_authority,
            accepted_graph=accepted_graph,
        ),
        statement_audit=_prepared_statement_audit_summary(
            all_claims,
            library_summary,
            paper_summary,
            authority=prepared.presentation_authority,
        ),
        paper_coverage_audit=_prepared_paper_coverage_summary(
            all_claims,
            paper_prerequisites,
            library_prerequisites,
            authority=prepared.presentation_authority,
        ),
        assumption_audit=_prepared_assumption_audit_summary(
            all_claims,
            authority=prepared.presentation_authority,
            accepted_graph=accepted_graph,
        ),
    )


def current_semantic_review_surface(
    folder: Path,
    claim_items: list[ReviewItem],
    all_items: list[ReviewItem],
    *,
    semantic_reuse_authority: CurrentSemanticReuseAuthority | None = None,
) -> _CurrentSemanticReviewSurface:
    """Build the non-rendering semantic surface once from authenticated rows."""

    human_claims = human_review_claim_items(
        folder,
        claim_items,
        semantic_reuse_authority=semantic_reuse_authority,
    )
    bind_current_v11_source_spec_screening(folder, human_claims)
    _project_v11_claim_rows_onto_review_items(all_items, human_claims)
    from scripts.current_closeout import review_surface

    all_specification_names = sorted(
        {
            str(item.full_name or "").strip()
            for item in all_items
            if str(item.full_name or "").strip().endswith("Spec")
        }
    )
    try:
        packet_cache = review_surface._current_packet_lean_cache(
            folder,
            all_specification_names,
            semantic_reuse_authority=semantic_reuse_authority,
        )
    except Exception:  # noqa: BLE001 - cache reuse is only a speed path.
        packet_cache = None
    cached_paper_targets = (
        review_surface.paper_semantic_review_targets_from_cache(
            packet_cache
        )
        if isinstance(packet_cache, Mapping)
        else None
    )
    cached_library_targets = (
        packet_cache.get("library_semantic_targets")
        if isinstance(packet_cache, Mapping)
        and isinstance(packet_cache.get("library_semantic_targets"), Mapping)
        else None
    )
    cached_library_target_errors = (
        packet_cache.get("library_semantic_target_errors")
        if isinstance(packet_cache, Mapping)
        and isinstance(packet_cache.get("library_semantic_target_errors"), Mapping)
        else None
    )
    # Assumptions have their own source-provenance review lane. They are
    # visible cards but do not enlarge the claim-only prerequisite surface.
    source_claim_rows = [
        item for item in human_claims if not bool(item.get("is_assumption"))
    ]
    semantic_targets = {
        str(item.get("full_name") or "").strip(): {
            "prerequisite_declarations": item.get(
                "paper_semantic_prerequisite_declarations", ()
            )
        }
        for item in source_claim_rows
        if str(item.get("full_name") or "").strip()
    }
    try:
        source_map = review_surface._read_json(
            folder / review_surface.SOURCE_MAP_NAME
        )
    except ValueError:
        source_map = {}
    recorded_library_prerequisites: list[dict[str, Any]] | None = None
    if cached_paper_targets:
        graph_selected, recorded_projection = (
            review_surface._recorded_graph_packet_projection(folder)
        )
        if graph_selected:
            if recorded_projection is None or not isinstance(packet_cache, Mapping):
                raise ValueError(
                    "recorded accepted graph is unavailable for prerequisite display"
                )
            paper_prerequisites, recorded_library_prerequisites = (
                review_surface._recorded_graph_prerequisite_cards(
                    folder,
                    source_map,
                    packet_cache,
                    recorded_projection,
                )
            )
        else:
            current_projection = (
                review_surface.load_current_v11_review_graph_projection(ROOT, folder)
            )
            if current_projection is None:
                raise ValueError(
                    "paper prerequisite cards require a saved current Lean graph"
                )
            _support, _names_by_root, support_digests = (
                current_projection.paper_prerequisite_review_support(
                    current_projection.paper_prerequisite_targets
                )
            )
            paper_prerequisites = review_surface._prepared_paper_prerequisites(
                folder,
                semantic_targets,
                source_map_payload=source_map,
                semantic_targets_by_name_override=cached_paper_targets,
                declaration_sources_override=(
                    current_projection.paper_declaration_sources
                ),
                supporting_declarations_sha256_by_name=support_digests,
            )
    else:
        paper_prerequisites = []
    library_review_inputs: list[Mapping[str, Any]] = [*source_claim_rows]
    library_review_inputs.extend(
        {
            "library_review_owner_declarations": prerequisite.get(
                "direct_library_declarations", ()
            )
        }
        for prerequisite in paper_prerequisites
    )
    explicit_library_declarations = (
        review_surface.explicit_source_semantic_declarations(
            source_map, library=True
        )
    )
    if explicit_library_declarations:
        library_review_inputs.append(
            {
                "library_review_owner_declarations": sorted(
                    explicit_library_declarations
                )
            }
        )
    library_prerequisites = (
        recorded_library_prerequisites
        if recorded_library_prerequisites is not None
        else human_review_library_prerequisites(
            folder,
            library_review_inputs,
            semantic_targets_override=cached_library_targets or {},
            semantic_target_errors_override=cached_library_target_errors or {},
        )
    )
    library_summary = library_semantic_review_summary(
        folder,
        all_items,
        entries_override=library_prerequisites,
    )
    return _CurrentSemanticReviewSurface(
        human_claims=human_claims,
        library_prerequisites=library_prerequisites,
        library_summary=library_summary,
        paper_prerequisites=paper_prerequisites,
        paper_prerequisite_summary=semantic_prerequisite_review_summary(
            paper_prerequisites
        ),
    )


def gather_paper_data(
    paper_filter: str | None = None,
    slice_filter: str | None = None,
    *,
    render_images: bool = True,
) -> list[dict[str, Any]]:
    papers = []
    for folder in iter_paper_folders(paper_filter):
        typed_surface = _typed_prepared_dashboard_surface(folder, slice_filter)
        if typed_surface is None:
            semantic_reuse_authority = current_dashboard_semantic_reuse_authority(
                folder
            )
            all_items = review_items_for_paper(
                folder,
                use_cache=True,
                render_images=render_images,
                semantic_reuse_authority=semantic_reuse_authority,
            )
            items = filter_items_by_slice(all_items, folder.name, slice_filter)
            semantic_surface = current_semantic_review_surface(
                folder,
                items,
                all_items,
                semantic_reuse_authority=semantic_reuse_authority,
            )
            human_claims = semantic_surface.human_claims
            browser_items = [browser_review_item(item.__dict__) for item in items]
            slices = summarize_review_slices(all_items)
            surface_audit = review_surface_audit_summary(folder, all_items)
            statement_summary = statement_translation_audit_summary(
                folder,
                all_items,
                library_summary_override=semantic_surface.library_summary,
            )
            paper_coverage_summary = paper_coverage_audit_summary(folder, all_items)
            assumption_summary = assumption_provenance_audit_summary(
                folder, all_items
            )
            presentation_sections = human_review_presentation_sections(
                folder, human_claims
            )
        else:
            semantic_surface = typed_surface.semantic_surface
            human_claims = typed_surface.selected_claims
            browser_items = [browser_review_item(item) for item in human_claims]
            slices = typed_surface.slices
            surface_audit = typed_surface.surface_audit
            statement_summary = typed_surface.statement_audit
            paper_coverage_summary = typed_surface.paper_coverage_audit
            assumption_summary = typed_surface.assumption_audit
            presentation_sections = typed_surface.presentation_sections
        assets = {}
        paper_pdf = find_paper_pdf(folder)
        if paper_pdf:
            assets["pdf"] = {
                "name": paper_pdf.name,
                "url": paper_asset_url(folder.name, paper_pdf),
            }
        paper_text = find_paper_text(folder)
        if paper_text:
            assets["text"] = {
                "name": paper_text.name,
                "url": paper_asset_url(folder.name, paper_text),
                "extension": paper_text.suffix.lower(),
            }
        papers.append(
            {
                "name": folder.name,
                "title": paper_title(folder),
                "items": browser_items,
                "human_claims": [browser_review_item(item) for item in human_claims],
                "presentation_sections": presentation_sections,
                "human_review_prerequisites": semantic_surface.library_prerequisites,
                "human_review_paper_prerequisites": semantic_surface.paper_prerequisites,
                "library_semantic_audit": semantic_surface.library_summary,
                "slices": slices,
                "active_slice": slice_filter or "",
                "assets": assets,
                "surface_audit": surface_audit,
                "statement_audit": statement_summary,
                "paper_coverage_audit": paper_coverage_summary,
                # This optional public-release projection supplies a frozen
                # browser denominator only.  It never changes the strict
                # source inventory used by CLI checks or closeout evidence.
                "public_source_display_surface": public_source_display_coverage_surface(
                    folder
                ),
                "assumption_audit": assumption_summary,
            }
        )
    return papers


def get_item_statements(paper: str, theorem: str) -> tuple[str, str, str, str, str]:
    """Lookup the current statements and source metadata for one theorem."""

    for paper_data in gather_paper_data(paper):
        if paper_data.get("name") != paper:
            continue
        for item in paper_data.get("items", []):
            if item.get("name") == theorem:
                return (
                    str(item.get("lean_statement") or ""),
                    str(item.get("paper_statement") or ""),
                    str(item.get("agent_statement") or ""),
                    str(item.get("source_status") or ""),
                    str(item.get("source_note") or ""),
                )
    return "", "", "", "", ""


def read_log_entries(log_file: Path, paper: str | None = None) -> list[dict[str, Any]]:
    if not log_file.exists():
        return []
    entries: list[dict[str, Any]] = []
    for raw in log_file.read_text(encoding="utf-8").splitlines():
        raw = raw.strip()
        if not raw:
            continue
        try:
            entry = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if paper and entry.get("paper") != paper:
            continue
        entries.append(entry)
    entries.sort(key=lambda row: row.get("timestamp", ""))
    return entries


def item_digest(item: dict[str, Any], key: str) -> str:
    """Get current or fall-backed digest for an item key."""

    value = str(item.get(key) or "")
    return statement_digest(value)


def review_is_stale(
    entry: dict[str, Any], item: dict[str, Any]
) -> tuple[bool, bool, bool]:
    """Return `(lean_stale, paper_stale, source_stale)` for current item snapshot."""

    if not item:
        return False, False, False

    current_lean = item_digest(item, "lean_statement")
    current_paper = item_digest(item, "paper_statement")
    current_source = source_metadata_digest(
        str(item.get("source_status") or ""),
        str(item.get("source_note") or ""),
    )
    reviewed_lean = str(entry.get("lean_statement_sha256") or statement_digest(str(entry.get("lean_statement", "")))).strip()
    reviewed_paper = str(entry.get("paper_statement_sha256") or statement_digest(str(entry.get("paper_statement", "")))).strip()
    reviewed_source = str(entry.get("source_metadata_sha256") or "").strip()

    return (
        current_lean != reviewed_lean and bool(current_lean),
        current_paper != reviewed_paper and bool(current_paper),
        current_source != reviewed_source and bool(current_source),
    )


def _review_judgment(matches: Any) -> str:
    """Normalize a saved human review decision for validator exports."""

    if matches is True:
        return "matches"
    if matches is False:
        return "mismatch"
    if matches is None:
        return ""
    text = str(matches).strip().lower()
    if text in {"matches", "match", "true", "t", "yes", "y"}:
        return "matches"
    if text in {"mismatch", "does_not_match", "does not match", "false", "f", "no", "n"}:
        return "mismatch"
    if text in {"uncertain", "unknown", "unsure", "needs_review", "needs review"}:
        return "uncertain"
    return ""


def _review_matches_value(judgment: str) -> bool | None:
    """Return the backward-compatible matches field for a normalized judgment."""

    if judgment == "matches":
        return True
    if judgment == "mismatch":
        return False
    return None


def _validator_entry(
    validator: str,
    validator_type: str,
    validated_at: str,
    judgment: str,
    comment: str,
    source: str,
    stale: bool,
) -> dict[str, Any] | None:
    """Build a compact validator ledger entry for status exports."""

    name = str(validator or "").strip()
    if not name:
        return None
    return {
        "validator": name,
        "validator_type": str(validator_type or "").strip(),
        "validated_at": str(validated_at or "").strip(),
        "judgment": str(judgment or "").strip(),
        "comment": str(comment or "").strip(),
        "source": str(source or "").strip(),
        "stale": bool(stale),
    }


def _validator_names(validators: list[dict[str, Any]]) -> str:
    """Return stable unique validator labels for compact table columns."""

    labels: list[str] = []
    seen: set[str] = set()
    for entry in validators:
        name = str(entry.get("validator") or "").strip()
        if not name:
            continue
        validator_type = str(entry.get("validator_type") or "").strip()
        label = f"{name} ({validator_type})" if validator_type else name
        if label in seen:
            continue
        seen.add(label)
        labels.append(label)
    return ", ".join(labels)


def build_review_status(papers: list[dict[str, Any]], reviews: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Build compact theorem-level review status rows."""

    by_key: dict[tuple[str, str], list[dict[str, Any]]] = {}
    for entry in reviews:
        paper = str(entry.get("paper") or "").strip()
        theorem = str(entry.get("theorem") or "").strip()
        if not paper or not theorem:
            continue
        by_key.setdefault((paper, theorem), []).append(entry)

    rows: list[dict[str, Any]] = []
    for paper in papers:
        paper_name = paper["name"]
        # The interactive surface has one row per paper source claim, plus
        # explicit source-model assumptions in their separate provenance lane.
        # A paired theorem proves its Spec but is not a second review target.
        display_items = paper.get("human_claims")
        if not isinstance(display_items, list) or not display_items:
            display_items = paper["items"]
        for item in display_items:
            theorem = item["name"]
            key = (paper_name, theorem)
            history = sorted(by_key.get(key, []), key=lambda row: row.get("timestamp", ""))
            latest = history[-1] if history else None
            stale_lean = False
            stale_paper = False
            stale_source = False
            if latest:
                stale_lean, stale_paper, stale_source = review_is_stale(latest, item)

            latest_user = latest.get("user") if latest else ""
            latest_ts = latest.get("timestamp") if latest else ""
            latest_judgment = _review_judgment(
                latest.get("judgment") if latest and "judgment" in latest else latest.get("matches") if latest else None
            )
            latest_matches = _review_matches_value(latest_judgment) if latest else None
            validators: list[dict[str, Any]] = []
            for entry in history:
                entry_stale_lean, entry_stale_paper, entry_stale_source = review_is_stale(entry, item)
                entry_judgment = _review_judgment(
                    entry.get("judgment") if "judgment" in entry else entry.get("matches")
                )
                validator_entry = _validator_entry(
                    validator=str(entry.get("user") or "").strip(),
                    validator_type="human",
                    validated_at=str(entry.get("timestamp") or "").strip(),
                    judgment=entry_judgment,
                    comment=str(entry.get("notes") or "").strip(),
                    source="paper_theorem_validations.jsonl",
                    stale=entry_stale_lean or entry_stale_paper or entry_stale_source,
                )
                if validator_entry is not None:
                    validators.append(validator_entry)
            if item.get("llm_match_judgment"):
                llm_comment = str(item.get("llm_match_reason") or "").strip()
                llm_resolution = str(item.get("llm_match_resolution") or "").strip()
                if llm_resolution:
                    resolution_bits = [f"resolution={llm_resolution}"]
                    boundary_names = _normalize_string_list(item.get("llm_match_boundary_names"))
                    conditional_premises = _normalize_string_list(
                        item.get("llm_match_conditional_premises")
                    )
                    resolution_reason = str(item.get("llm_match_resolution_reason") or "").strip()
                    if boundary_names:
                        resolution_bits.append("boundaries=" + ", ".join(boundary_names))
                    if conditional_premises:
                        resolution_bits.append(
                            "conditional_premises=" + ", ".join(conditional_premises)
                        )
                    if resolution_reason:
                        resolution_bits.append("reason=" + resolution_reason)
                    llm_comment = (
                        f"{llm_comment} [{'; '.join(resolution_bits)}]"
                        if llm_comment
                        else "; ".join(resolution_bits)
                    )
                validator_entry = _validator_entry(
                    validator=str(
                        item.get("llm_match_validator")
                        or item.get("llm_match_source")
                        or DEFAULT_LLM_STATEMENT_JUDGE_FILE
                    ).strip(),
                    validator_type=str(item.get("llm_match_validator_type") or "").strip(),
                    validated_at=str(item.get("llm_match_validated_at") or "").strip(),
                    judgment=str(item.get("llm_match_judgment") or "").strip(),
                    comment=llm_comment,
                    source=str(item.get("llm_match_source") or "").strip(),
                    stale=bool(item.get("llm_match_stale", False)),
                )
                if validator_entry is not None:
                    validators.append(validator_entry)
            if item.get("llm_assumption_judgment"):
                validator_entry = _validator_entry(
                    validator=str(
                        item.get("llm_assumption_validator")
                        or item.get("llm_assumption_source")
                        or DEFAULT_LLM_ASSUMPTION_JUDGE_FILE
                    ).strip(),
                    validator_type=str(item.get("llm_assumption_validator_type") or "").strip(),
                    validated_at=str(item.get("llm_assumption_validated_at") or "").strip(),
                    judgment=str(item.get("llm_assumption_judgment") or "").strip(),
                    comment=str(item.get("llm_assumption_reason") or "").strip(),
                    source=str(item.get("llm_assumption_source") or "").strip(),
                    stale=bool(item.get("llm_assumption_stale", False)),
                )
                if validator_entry is not None:
                    validators.append(validator_entry)
            rows.append(
                {
                    "paper": paper_name,
                    "theorem": theorem,
                    "kind": item["kind"],
                    "line_number": item.get("line_number", 0),
                    "slice_id": item.get("slice_id", "all"),
                    "slice_title": item.get("slice_title", "All statements"),
                    "has_review": latest is not None,
                    "review_count": len(history),
                    "needs_attention": latest is None
                    or stale_lean
                    or stale_paper
                    or stale_source
                    or latest_judgment in {"mismatch", "uncertain"},
                    "latest_user": latest_user,
                    "latest_timestamp": latest_ts,
                    "latest_judgment": latest_judgment,
                    "latest_matches": latest_matches,
                    "latest_notes": latest.get("notes") if latest else "",
                    "lean_stale": stale_lean,
                    "paper_stale": stale_paper,
                    "source_stale": stale_source,
                    "source_status": item.get("source_status", ""),
                    "source_note": item.get("source_note", ""),
                    "is_assumption": bool(item.get("is_assumption", False)),
                    "is_proposition_spec": bool(item.get("is_proposition_spec", False)),
                    "proposition_spec_role": item.get("proposition_spec_role", ""),
                    "proposition_spec_proof": item.get("proposition_spec_proof", ""),
                    "validators": validators,
                    "validator_names": _validator_names(validators),
                    "llm_match_judgment": item.get("llm_match_judgment", ""),
                    "llm_match_reason": item.get("llm_match_reason", ""),
                    "llm_match_stale": bool(item.get("llm_match_stale", False)),
                    "llm_match_source": item.get("llm_match_source", ""),
                    "llm_match_validator": item.get("llm_match_validator", ""),
                    "llm_match_validator_type": item.get("llm_match_validator_type", ""),
                    "llm_match_validated_at": item.get("llm_match_validated_at", ""),
                    "llm_match_resolution": item.get("llm_match_resolution", ""),
                    "llm_match_boundary_type": item.get("llm_match_boundary_type", ""),
                    "llm_match_boundary_names": _normalize_string_list(
                        item.get("llm_match_boundary_names")
                    ),
                    "llm_match_conditional_premises": _normalize_string_list(
                        item.get("llm_match_conditional_premises")
                    ),
                    "llm_match_resolution_reason": item.get("llm_match_resolution_reason", ""),
                    "llm_assumption_judgment": item.get("llm_assumption_judgment", ""),
                    "llm_assumption_reason": item.get("llm_assumption_reason", ""),
                    "llm_assumption_stale": bool(item.get("llm_assumption_stale", False)),
                    "llm_assumption_source": item.get("llm_assumption_source", ""),
                    "llm_assumption_validator": item.get("llm_assumption_validator", ""),
                    "llm_assumption_validator_type": item.get("llm_assumption_validator_type", ""),
                    "llm_assumption_validated_at": item.get("llm_assumption_validated_at", ""),
                    "llm_assumption_premise_judgments": item.get(
                        "llm_assumption_premise_judgments", {}
                    ),
                }
            )
    rows.sort(key=lambda row: (row["paper"], row["theorem"]))
    return rows


def filter_review_rows(
    rows: list[dict[str, Any]], user_filter: str | None = None, stale_only: bool = False
) -> list[dict[str, Any]]:
    if user_filter:
        user_filter = user_filter.strip()
    if not user_filter and not stale_only:
        return rows
    out: list[dict[str, Any]] = []
    for row in rows:
        if stale_only and not row.get("needs_attention"):
            continue
        if user_filter and row.get("latest_user") != user_filter:
            continue
        out.append(row)
    return out


def render_csv_summary(rows: list[dict[str, Any]]) -> str:
    header = [
        "paper",
        "slice",
        "theorem",
        "kind",
        "line_number",
        "has_review",
        "review_count",
        "needs_attention",
        "latest_user",
        "latest_timestamp",
        "latest_matches",
        "validators",
        "lean_stale",
        "paper_stale",
        "source_stale",
        "source_status",
        "source_note",
        "llm_match_judgment",
        "llm_match_resolution",
        "llm_match_stale",
    ]
    out = io.StringIO()
    writer = csv.writer(out)
    writer.writerow(header)
    for row in rows:
        writer.writerow(
            [
                row["paper"],
                row.get("slice_title", row.get("slice_id", "")),
                row["theorem"],
                row["kind"],
                str(row.get("line_number") or ""),
                "true" if row["has_review"] else "false",
                str(row["review_count"]),
                "true" if row["needs_attention"] else "false",
                row.get("latest_user", ""),
                row.get("latest_timestamp", ""),
                "true" if row.get("latest_matches") else "false",
                row.get("validator_names", ""),
                "true" if row.get("lean_stale") else "false",
                "true" if row.get("paper_stale") else "false",
                "true" if row.get("source_stale") else "false",
                row.get("source_status", ""),
                row.get("source_note", ""),
                row.get("llm_match_judgment", ""),
                row.get("llm_match_resolution", ""),
                "true" if row.get("llm_match_stale") else "false",
            ]
        )
    rendered = out.getvalue()
    out.close()
    return rendered


def _escape_md(value: Any) -> str:
    return str(value).replace("|", "\\|").replace("\n", "<br/>")


def render_markdown_summary(rows: list[dict[str, Any]]) -> str:
    lines = [
        "| Paper | Slice | Theorem | Kind | Line | Reviewed | Reviews | Needs attention | Latest | Latest timestamp | Matches | Validators | Lean stale | Paper stale | Source stale | Source status | Source note | LLM judgment | LLM resolution | LLM stale | Notes |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append(
            "| " + " | ".join(
                [
                    _escape_md(row["paper"]),
                    _escape_md(row.get("slice_title") or row.get("slice_id") or ""),
                    _escape_md(row["theorem"]),
                    _escape_md(row["kind"]),
                    str(row.get("line_number") or ""),
                    "yes" if row["has_review"] else "no",
                    str(row["review_count"]),
                    "yes" if row["needs_attention"] else "no",
                    _escape_md(row.get("latest_user") or "—"),
                    _escape_md(row.get("latest_timestamp", "")),
                    "yes" if row.get("latest_matches") else "no",
                    _escape_md(row.get("validator_names", "")),
                    "yes" if row.get("lean_stale") else "no",
                    "yes" if row.get("paper_stale") else "no",
                    "yes" if row.get("source_stale") else "no",
                    _escape_md(row.get("source_status", "")),
                    _escape_md(row.get("source_note", "")),
                    _escape_md(row.get("llm_match_judgment", "")),
                    _escape_md(row.get("llm_match_resolution", "")),
                    "yes" if row.get("llm_match_stale") else "no",
                    _escape_md(row.get("latest_notes", "")),
                ]
            )
            + " |"
        )
    return "\n".join(lines) + "\n"


def _validator_report_label(entry: dict[str, Any]) -> str:
    name = str(entry.get("validator") or "").strip()
    if not name:
        return ""
    validator_type = str(entry.get("validator_type") or "").strip()
    judgment = str(entry.get("judgment") or "").strip()
    validated_at = str(entry.get("validated_at") or "").strip()
    stale = bool(entry.get("stale"))
    details: list[str] = []
    if validator_type:
        details.append(validator_type)
    if judgment:
        details.append(judgment)
    if validated_at:
        details.append(validated_at)
    if stale:
        details.append("stale")
    if not details:
        return name
    return f"{name} ({'; '.join(details)})"


def render_validator_markdown_summary(rows: list[dict[str, Any]]) -> str:
    """Render the compact validator table intended for final validation reports."""

    lines = [
        "| Paper-facing statement | Lean declaration | Validators | Validator comments |",
        "| --- | --- | --- | --- |",
    ]
    for row in rows:
        validators = row.get("validators") if isinstance(row.get("validators"), list) else []
        labels = [_validator_report_label(entry) for entry in validators if isinstance(entry, dict)]
        labels = [label for label in labels if label]
        comments: list[str] = []
        for entry in validators:
            if not isinstance(entry, dict):
                continue
            comment = str(entry.get("comment") or "").strip()
            if not comment:
                continue
            label = _validator_report_label(entry) or str(entry.get("validator") or "").strip()
            comments.append(f"{label}: {comment}" if label else comment)
        paper_item = f"{row.get('kind', '')} {row.get('theorem', '')}".strip()
        lines.append(
            "| " + " | ".join(
                [
                    _escape_md(paper_item),
                    _escape_md(f"`{row.get('theorem', '')}`" if row.get("theorem") else ""),
                    _escape_md("<br/>".join(labels) if labels else "None recorded"),
                    _escape_md("<br/>".join(comments) if comments else "None"),
                ]
            )
            + " |"
        )
    return "\n".join(lines) + "\n"


def status_totals(rows: list[dict[str, Any]]) -> dict[str, Any]:
    total = len(rows)
    reviewed = sum(1 for row in rows if row.get("has_review"))
    stale = sum(1 for row in rows if row.get("needs_attention"))
    lean_stale = sum(1 for row in rows if row.get("lean_stale"))
    paper_stale = sum(1 for row in rows if row.get("paper_stale"))
    source_stale = sum(1 for row in rows if row.get("source_stale"))
    no_review = total - reviewed
    return {
        "total_items": total,
        "reviewed_items": reviewed,
        "unreviewed_items": no_review,
        "needs_attention_items": stale,
        "lean_stale_items": lean_stale,
        "paper_stale_items": paper_stale,
        "source_stale_items": source_stale,
    }


def surface_audit_rows(papers: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Return paper-level review-surface audit rows for API/export/precheck use."""

    rows: list[dict[str, Any]] = []
    for paper in papers:
        audit = paper.get("surface_audit") or {}
        rows.append({"paper": paper.get("name", ""), **audit})
    return rows


def statement_audit_rows(papers: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Return paper-level statement-translation audit rows for API/export/precheck."""

    rows: list[dict[str, Any]] = []
    for paper in papers:
        audit = paper.get("statement_audit") or {}
        rows.append({"paper": paper.get("name", ""), **audit})
    return rows


def _direct_audit_inputs(
    paper_filter: str | None,
    slice_filter: str | None,
) -> Iterator[
    tuple[
        Path,
        CurrentSemanticReuseAuthority | None,
        list[ReviewItem],
        list[ReviewItem],
    ]
]:
    """Yield authenticated cached rows without constructing dashboard output."""

    for folder in iter_paper_folders(paper_filter):
        authority = current_dashboard_semantic_reuse_authority(folder)
        all_items = review_items_for_paper(
            folder,
            use_cache=True,
            render_images=False,
            semantic_reuse_authority=authority,
        )
        yield (
            folder,
            authority,
            all_items,
            filter_items_by_slice(all_items, folder.name, slice_filter),
        )


def direct_statement_audit_rows(
    paper_filter: str | None,
    slice_filter: str | None = None,
) -> list[dict[str, Any]]:
    """Compute statement diagnostics from the shared non-rendering surface."""

    rows: list[dict[str, Any]] = []
    for folder, authority, all_items, selected_items in _direct_audit_inputs(
        paper_filter, slice_filter
    ):
        semantic_surface = current_semantic_review_surface(
            folder,
            selected_items,
            all_items,
            semantic_reuse_authority=authority,
        )
        rows.append(
            {
                "paper": folder.name,
                **statement_translation_audit_summary(
                    folder,
                    all_items,
                    library_summary_override=semantic_surface.library_summary,
                ),
            }
        )
    return rows


def paper_coverage_audit_rows(papers: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Return paper-level source-statement coverage audit rows."""

    rows: list[dict[str, Any]] = []
    for paper in papers:
        audit = paper.get("paper_coverage_audit") or {}
        rows.append({"paper": paper.get("name", ""), **audit})
    return rows


def direct_paper_coverage_audit_rows(
    paper_filter: str | None,
    slice_filter: str | None = None,
) -> list[dict[str, Any]]:
    """Compute the coverage CLI surface without constructing the website.

    Coverage checks need current cached review rows and their source/Spec
    judgments. They do not need rendered assets, prerequisite cards, library
    summaries, website presentation sections, or assumption summaries. The
    tracked semantic authority admits only an exact-current cache; a miss keeps
    the ordinary review-row loader fail closed.
    """

    rows: list[dict[str, Any]] = []
    for folder, authority, all_items, items in _direct_audit_inputs(
        paper_filter, slice_filter
    ):
        current_semantic_review_surface(
            folder,
            items,
            all_items,
            semantic_reuse_authority=authority,
        )
        rows.append(
            {
                "paper": folder.name,
                **paper_coverage_audit_summary(folder, items),
            }
        )
    return rows


def assumption_audit_rows(papers: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Return paper-level assumption-provenance audit rows."""

    rows: list[dict[str, Any]] = []
    for paper in papers:
        audit = paper.get("assumption_audit") or {}
        rows.append({"paper": paper.get("name", ""), **audit})
    return rows


def direct_assumption_audit_rows(
    paper_filter: str | None,
    slice_filter: str | None = None,
) -> list[dict[str, Any]]:
    """Compute the strict assumption gate from authenticated audit rows.

    Typed dashboard cards intentionally carry only presentation evidence.
    This direct path preserves the complete assumption-provenance and premise
    checks for CLI/closeout without forcing the browser to reconstruct them.
    """

    rows: list[dict[str, Any]] = []
    for folder, _authority, all_items, _selected_items in _direct_audit_inputs(
        paper_filter, slice_filter
    ):
        rows.append(
            {
                "paper": folder.name,
                **assumption_provenance_audit_summary(folder, all_items),
            }
        )
    return rows


def conditional_boundary_statement_premises(folder: Path) -> dict[str, list[str]]:
    """Return accepted visible extra Lean premises keyed by review row.

    The function name is retained for callers that consume the historical
    machine-level category. It does not accept a row with a missing source
    conclusion as a boundary.
    """

    out: dict[str, list[str]] = {}
    manifests = SIGNATURE_MANIFEST_CACHE.get(str(folder.resolve()), {})
    for name, judgment in load_llm_statement_judgments(folder, manifests).items():
        if not _is_conditional_boundary_judgment(judgment):
            continue
        premises = _normalize_string_list(judgment.get("conditional_premises"))
        if premises:
            out[name] = premises
    return out


def _default_hidden_premise_row(paper_name: str) -> dict[str, Any]:
    """Create the hidden-premise audit row shape used by CLI prechecks."""

    return {
        "paper": paper_name,
        "hidden_premise_count": 0,
        "hidden_premise_error_count": 0,
        "hidden_premise_warning_count": 0,
        "hidden_premise_samples": [],
        "accepted_conditional_premise_count": 0,
        "accepted_conditional_premise_samples": [],
        "needs_attention": False,
        "has_warning": False,
    }


FAST_SAVED_SOURCE_RECORD_IDENTITY_TIMEOUT_SECONDS = 45


def _fast_saved_source_record_identity(
    paper: str,
) -> tuple[dict[str, Any] | None, str]:
    """Read the source-record tool's narrow current-repository receipt.

    This intentionally delegates the source/configuration identity calculation
    to the source-record producer.  The producer checks the saved schema-10
    raw receipt and every Lean-owned repository source in its recorded loaded
    closure, but deliberately does not reread external ``.olean`` artifacts.
    It is therefore useful only for a responsive precheck; paper closeout
    keeps the stricter external-artifact and live-Lean validation path.
    """

    script = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
    if not script.is_file():
        return None, "source-record fast-identity helper is unavailable"
    try:
        proc = subprocess.run(
            [
                sys.executable,
                str(script),
                "--root",
                str(ROOT),
                "--paper",
                paper,
                "--fast-saved-identity",
            ],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=FAST_SAVED_SOURCE_RECORD_IDENTITY_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired:
        return None, "source-record fast-identity helper timed out"
    except OSError as exc:
        return None, "could not start source-record fast-identity helper: " + str(exc)
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError:
        excerpt = " ".join((proc.stderr or proc.stdout or "").splitlines()[-3:])
        return None, "source-record fast-identity helper returned invalid JSON" + (
            ": " + excerpt if excerpt else ""
        )
    if not isinstance(payload, dict):
        return None, "source-record fast-identity helper returned a non-object payload"
    if proc.returncode != 0 or payload.get("current") is not True:
        reason = str(payload.get("reason") or "saved source-record receipt is not current")
        return payload, reason
    return payload, ""


def _fast_source_record_closure_paths(
    payload: Mapping[str, Any],
) -> tuple[set[Path], str]:
    """Return source paths from a saved Lean-owned closure without guessing imports."""

    closure = payload.get("lean_import_closure")
    sources = closure.get("sources") if isinstance(closure, Mapping) else None
    if not isinstance(sources, list):
        return set(), "saved source-record receipt has no Lean import-closure source list"
    paths: set[Path] = set()
    for source in sources:
        if not isinstance(source, Mapping):
            return set(), "saved source-record receipt has a malformed closure source"
        raw_path = str(source.get("path") or "").strip()
        if not raw_path:
            return set(), "saved source-record receipt has an unnamed closure source"
        candidate = (ROOT / raw_path).resolve()
        try:
            candidate.relative_to(ROOT)
        except ValueError:
            return set(), "saved source-record closure source escapes the repository"
        paths.add(candidate)
    return paths, ""


def _fast_source_record_unconfigured_support_scope(
    folder: Path,
    payload: Mapping[str, Any],
    closure_paths: set[Path],
) -> tuple[list[str], list[str], str]:
    """Separate active support debt from an unimported legacy support module.

    This is a graph decision, not a declaration-name convention.  A support
    declaration reported from a separate Assumptions source cannot be an
    active premise of the current review surface when that exact source is
    absent from Lean's loaded closure and is not the status-configured
    assumption source.  It remains reported as inactive legacy inventory.
    """

    rows = [
        str(value).strip()
        for value in payload.get("unconfigured_assumption_support_rows") or []
        if str(value).strip()
    ]
    if not rows:
        return [], [], ""
    raw_source = payload.get("review_assumption_source")
    raw_path = str(raw_source.get("path") or "").strip() if isinstance(raw_source, Mapping) else ""
    if not raw_path:
        return rows, [], "source-record support inventory has no source path"
    source_path = (ROOT / raw_path).resolve()
    try:
        source_path.relative_to(ROOT)
    except ValueError:
        return rows, [], "source-record support source escapes the repository"
    try:
        configured_source = assumption_source_file(folder).resolve()
    except (OSError, ValueError):
        return rows, [], "configured assumption source is unavailable"
    if source_path not in closure_paths and source_path != configured_source:
        return [], rows, ""
    return rows, [], ""


def fast_saved_source_record_assumption_precheck(
    paper: str | None, slice_filter: str | None = None
) -> dict[str, Any] | None:
    """Return a bounded semantic premise precheck, or ``None`` when ineligible.

    The route is intentionally narrow.  It is available only where the paper
    configures no explicit Assumptions.lean declarations and the whole paper
    is selected.  It validates a source-record receipt against exact current
    repository source/configuration inputs, checks current semantic judgment
    coverage, and reads current reachability from Lean's saved loaded-module
    closure.  It does not grant strict closeout credit.
    """

    if not paper or slice_filter:
        return None
    folder = ROOT / "papers" / paper
    if not folder.is_dir() or review_assumption_names(folder):
        return None

    result: dict[str, Any] = {
        "paper": paper,
        "scope": "repository sources/configuration only; strict closeout also revalidates external artifacts and live Lean",
        "needs_attention": False,
        "reasons": [],
        "required_judgment_count": 0,
        "current_judgment_count": 0,
        "inactive_legacy_support_rows": [],
        "reachable_auxiliary_rows": [],
        "inactive_assumption_sidecar_rows": [],
        "hidden_variable_premises": [],
    }
    identity, identity_error = _fast_saved_source_record_identity(paper)
    if identity_error:
        result["needs_attention"] = True
        result["reasons"].append(identity_error)
        return result
    assert identity is not None

    try:
        from scripts import audit_evidence_integrity as evidence
        from scripts import audit_repository
    except Exception as exc:  # noqa: BLE001 - an unavailable validator fails closed.
        result["needs_attention"] = True
        result["reasons"].append("could not load semantic premise validators: " + str(exc))
        return result

    status = _dashboard_json_payload(folder / DEFAULT_PAPER_STATUS_FILE)
    if not isinstance(status, dict):
        result["needs_attention"] = True
        result["reasons"].append("paper-local status metadata is unavailable")
        return result
    audit_path, audit_path_error = evidence.source_record_review_sidecar_path(
        folder,
        status,
        config_field="source_record_audit_file",
        default_basename="source_record_audit.json",
    )
    match_path, match_path_error = evidence.source_record_review_sidecar_path(
        folder,
        status,
        config_field="source_record_judgment_file",
        default_basename="source_record_match_llm.json",
    )
    if audit_path_error or match_path_error or audit_path is None or match_path is None:
        result["needs_attention"] = True
        result["reasons"].append(
            audit_path_error or match_path_error or "source-record sidecar path is unavailable"
        )
        return result
    canonical_audit_path = folder / PAPER_AUDIT_DIR / "source_record_audit.json"
    if audit_path.resolve() != canonical_audit_path.resolve():
        result["needs_attention"] = True
        result["reasons"].append(
            "fast precheck only accepts the canonical source-record raw sidecar"
        )
        return result
    raw = _dashboard_json_payload(audit_path)
    match = _dashboard_json_payload(match_path)
    if not isinstance(raw, dict) or not isinstance(match, dict):
        result["needs_attention"] = True
        result["reasons"].append("current source-record raw or judgment sidecar is unavailable")
        return result
    if str(raw.get("source_record_audit_sha256") or "").strip() != str(
        identity.get("source_record_audit_sha256") or ""
    ).strip():
        result["needs_attention"] = True
        result["reasons"].append(
            "source-record raw sidecar changed while its fast identity was checked"
        )
        return result
    try:
        raw_file_sha256 = hashlib.sha256(audit_path.read_bytes()).hexdigest()
    except OSError:
        raw_file_sha256 = ""
    if raw_file_sha256 != str(identity.get("source_record_audit_file_sha256") or ""):
        result["needs_attention"] = True
        result["reasons"].append(
            "source-record raw bytes changed while its fast identity was checked"
        )
        return result

    (
        semantic_contract_revalidation,
        semantic_contract_revalidation_error,
    ) = evidence.source_record_semantic_contract_revalidation_context(
        folder, raw
    )
    if semantic_contract_revalidation_error:
        result["needs_attention"] = True
        result["reasons"].append(
            "semantic-contract revalidation is invalid: "
            + semantic_contract_revalidation_error
        )
        return result
    effective_semantic_errors = evidence.source_record_effective_semantic_errors(
        raw,
        semantic_contract_revalidation=semantic_contract_revalidation,
    )

    closure_paths, closure_error = _fast_source_record_closure_paths(raw)
    if closure_error:
        result["needs_attention"] = True
        result["reasons"].append(closure_error)
        return result
    active_support_rows, inactive_support_rows, support_scope_error = (
        _fast_source_record_unconfigured_support_scope(folder, raw, closure_paths)
    )
    result["inactive_legacy_support_rows"] = inactive_support_rows
    if support_scope_error:
        result["needs_attention"] = True
        result["reasons"].append(support_scope_error)
    if active_support_rows:
        result["needs_attention"] = True
        result["reasons"].append(
            f"{len(active_support_rows)} active unconfigured Assumptions support declaration(s)"
        )

    reachable_auxiliaries = [
        item
        for item in raw.get("unresolved_reachable_paper_interface_auxiliaries") or []
        if isinstance(item, Mapping)
    ]
    result["reachable_auxiliary_rows"] = reachable_auxiliaries
    if reachable_auxiliaries:
        result["needs_attention"] = True
        result["reasons"].append(
            f"{len(reachable_auxiliaries)} selected-root-reachable PaperInterface auxiliary declaration(s) lack a route or quarantine"
        )
    if raw.get("ambiguous_reachable_paper_interface_auxiliary_references"):
        result["needs_attention"] = True
        result["reasons"].append("raw source-record receipt has ambiguous reachable auxiliary references")
    for key, label in (
        ("missing_configured_review_rows", "configured review row(s) missing from raw receipt"),
        ("recursion_failures", "source-record recursion failure(s)"),
        ("semantic_model_review_configuration_errors", "semantic-model review configuration error(s)"),
        ("source_contract_association_errors", "source-contract association error(s)"),
        ("source_coverage_route_errors", "source-coverage route error(s)"),
    ):
        values = effective_semantic_errors.get(key, raw.get(key))
        if isinstance(values, list) and values:
            result["needs_attention"] = True
            result["reasons"].append(f"{len(values)} {label}")

    required = set(
        evidence.source_record_required_keys(
            raw,
            semantic_contract_revalidation=semantic_contract_revalidation,
        )
    )
    try:
        map_sha256 = evidence.current_paper_statement_map_sha256(folder)
        current = evidence._current_source_record_judgment_items(
            raw,
            match,
            expected_paper_statement_map_sha256=map_sha256,
            folder=folder,
            # The subprocess above has already checked the same exact raw
            # source/configuration identity.  This avoids redoing strict
            # external-artifact identity work in a dashboard-only precheck.
            prevalidated_source_record_identity_error="",
        )
    except Exception as exc:  # noqa: BLE001 - missing semantic validation is a failure.
        current = {}
        result["needs_attention"] = True
        result["reasons"].append("could not validate current source-record judgments: " + str(exc))
    result["required_judgment_count"] = len(required)
    result["current_judgment_count"] = len(set(current) & required)
    missing = sorted(required - set(current))
    if missing:
        result["needs_attention"] = True
        result["reasons"].append(
            f"{len(missing)} source-record semantic judgment(s) are missing or stale"
        )

    try:
        closure_files = sorted(
            path for path in closure_paths if path.is_file() and folder in path.parents
        )
        hidden = audit_repository.check_hidden_variable_premises_in_files(closure_files)
        result["hidden_variable_premises"] = [finding.message for finding in hidden]
        if hidden:
            result["needs_attention"] = True
            result["reasons"].append(f"{len(hidden)} hidden `variable` premise finding(s)")
    except Exception as exc:  # noqa: BLE001 - source scan must not silently disappear.
        result["needs_attention"] = True
        result["reasons"].append("could not scan Lean-owned closure for hidden variables: " + str(exc))

    assumption_sidecar = _dashboard_json_payload(llm_assumption_judgments_file(folder))
    sidecar_items = assumption_sidecar.get("items") if isinstance(assumption_sidecar, Mapping) else None
    if isinstance(sidecar_items, Mapping):
        # No configured assumptions means these serialized entries are outside
        # the active explicit-assumption surface.  They are reported for
        # cleanup/provenance but never grant current premise-audit credit.
        result["inactive_assumption_sidecar_rows"] = sorted(
            str(key).strip() for key in sidecar_items if str(key).strip()
        )
    return result


def print_fast_saved_source_record_assumption_precheck(result: Mapping[str, Any]) -> bool:
    """Print a clear bounded precheck result and return whether it needs attention."""

    paper = str(result.get("paper") or "unknown paper")
    scope = str(result.get("scope") or "")
    print(f"Assumption-provenance fast precheck for {paper}: {scope}.")
    inactive_support = list(result.get("inactive_legacy_support_rows") or [])
    if inactive_support:
        print(
            f" - {len(inactive_support)} unconfigured support declaration(s) are in an unimported legacy assumption source, not the current theorem surface: "
            + _format_name_sample(inactive_support)
        )
    inactive_sidecar = list(result.get("inactive_assumption_sidecar_rows") or [])
    if inactive_sidecar:
        print(
            f" - {len(inactive_sidecar)} unselected assumption-sidecar entry/entries receive no current premise-audit credit: "
            + _format_name_sample(inactive_sidecar)
        )
    reachable = list(result.get("reachable_auxiliary_rows") or [])
    if reachable:
        print(
            f" - {len(reachable)} current PaperInterface auxiliary declaration(s) are graph-reachable from selected review rows without a source route or quarantine."
        )
        for item in reachable[:3]:
            declaration = str(item.get("declaration") or "unknown declaration")
            references = item.get("transitively_referenced_from") or []
            chain = ""
            if isinstance(references, list) and references and isinstance(references[0], Mapping):
                chain = " -> ".join(
                    str(value).rsplit(".", 1)[-1]
                    for value in references[0].get("dependency_chain") or []
                    if str(value).strip()
                )
            print(f"   {declaration}" + (f" via {chain}" if chain else ""))
    if result.get("needs_attention"):
        print("Fast precheck needs attention: " + "; ".join(result.get("reasons") or ["unknown reason"]) + ".")
        print("Run strict paper closeout before claiming a formalization result.")
        return True
    print(
        "Fast precheck is current: "
        f"{int(result.get('current_judgment_count') or 0)}/{int(result.get('required_judgment_count') or 0)} "
        "semantic source-record judgments current, with no graph-visible premise defect."
    )
    print("Strict paper closeout remains required before publication.")
    return False


def hidden_premise_repository_audit_rows(paper: str | None) -> list[dict[str, Any]]:
    """Return the bounded syntax-only hidden-premise supplement for a precheck.

    ``assumption_provenance_audit_summary`` already checks the current
    elaborated review-row manifests and explicit assumption judgments.  The
    only additional lightweight check needed here is the paper-local Lean
    ``variable``-binder scan.  Calling the full machine-paper audit from this
    precheck used to reload the complete recursive source-record receipt and
    rerun unrelated closeout phases; IM05 made that one-assumption command
    take minutes and hundreds of megabytes.  Strict closeout still runs the
    complete repository audit separately.
    """

    try:
        from scripts import audit_repository
    except Exception as exc:  # pragma: no cover - defensive CLI fallback
        return [
            {
                "paper": paper or "all papers",
                "hidden_premise_audit_error": str(exc),
                "hidden_premise_count": 0,
                "hidden_premise_samples": [],
                "needs_attention": True,
                "has_warning": True,
            }
        ]

    variable_marker = "proof-boundary `variable` premise"
    rows: dict[str, dict[str, Any]] = {}
    accepted_conditional_premises: dict[str, dict[str, list[str]]] = {}

    def paper_conditional_premises(paper_name: str) -> dict[str, list[str]]:
        cached = accepted_conditional_premises.get(paper_name)
        if cached is not None:
            return cached
        folder = ROOT / "papers" / paper_name
        cached = conditional_boundary_statement_premises(folder) if folder.exists() else {}
        accepted_conditional_premises[paper_name] = cached
        return cached

    def finding_is_accepted_conditional(paper_name: str, message: str) -> bool:
        for row_name, premises in paper_conditional_premises(paper_name).items():
            if f"`{row_name}`" not in message:
                continue
            if any(premise and premise in message for premise in premises):
                return True
        return False

    if paper:
        paper_dir = ROOT / "papers" / paper
        if paper_dir.exists():
            paper_files = sorted(path for path in paper_dir.rglob("*.lean") if path.is_file())
            findings = audit_repository.check_hidden_variable_premises_in_files(paper_files)
        else:
            findings = []
    else:
        findings = audit_repository.check_hidden_variable_premises(include_active=False)
    for finding in findings:
        if variable_marker not in finding.message:
            continue
        rel_path = finding.path.relative_to(ROOT) if finding.path.is_absolute() else finding.path
        parts = rel_path.parts
        if len(parts) < 2 or parts[0] != "papers":
            continue
        paper_name = parts[1]
        if paper and paper_name != paper:
            continue
        row = rows.setdefault(paper_name, _default_hidden_premise_row(paper_name))
        if finding_is_accepted_conditional(paper_name, finding.message):
            row["accepted_conditional_premise_count"] += 1
            if len(row["accepted_conditional_premise_samples"]) < 5:
                row["accepted_conditional_premise_samples"].append(finding.message)
            continue
        row["hidden_premise_count"] += 1
        row["needs_attention"] = True
        row["has_warning"] = True
        if finding.severity == "ERROR":
            row["hidden_premise_error_count"] += 1
        elif finding.severity == "WARN":
            row["hidden_premise_warning_count"] += 1
        if len(row["hidden_premise_samples"]) < 5:
            row["hidden_premise_samples"].append(finding.message)
    return list(rows.values())


def merge_hidden_premise_audit_rows(
    rows: list[dict[str, Any]], paper: str | None
) -> list[dict[str, Any]]:
    """Merge explicit-assumption and hidden-premise audits for CLI reporting."""

    merged = {str(row.get("paper") or ""): dict(row) for row in rows}
    for hidden in hidden_premise_repository_audit_rows(paper):
        paper_name = str(hidden.get("paper") or "")
        row = merged.setdefault(paper_name, {"paper": paper_name})
        prior_needs_attention = bool(row.get("needs_attention"))
        prior_has_warning = bool(row.get("has_warning"))
        row.update(hidden)
        row["needs_attention"] = prior_needs_attention or bool(hidden.get("needs_attention"))
        row["has_warning"] = prior_has_warning or bool(hidden.get("has_warning"))
    return list(merged.values())


def stale_review_rows(rows: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    """Partition rows into stale and unreviewed buckets for launch-time diagnostics."""

    stale = [
        row
        for row in rows
        if row.get("has_review")
        and (row.get("lean_stale") or row.get("paper_stale") or row.get("source_stale"))
    ]
    unreviewed = [row for row in rows if not row.get("has_review")]
    mismatch = [
        row
        for row in rows
        if row.get("has_review")
        and not row.get("lean_stale")
        and not row.get("paper_stale")
        and not row.get("source_stale")
        and row.get("latest_matches") is False
    ]
    return {"stale": stale, "unreviewed": unreviewed, "mismatch": mismatch}


def parse_bool_flag(value: str | None) -> bool:
    if not value:
        return False
    return value.lower() in {"1", "true", "t", "yes", "y", "on"}


def append_review(log_file: Path, payload: dict[str, Any], default_user: str) -> dict[str, Any]:
    log_file.parent.mkdir(parents=True, exist_ok=True)

    paper = str(payload.get("paper") or "").strip()
    theorem = str(payload.get("theorem") or "").strip()
    user = str(payload.get("user") or default_user).strip() or default_user
    notes = str(payload.get("notes", "")).strip()
    raw_judgment = payload.get("judgment")
    if raw_judgment is None:
        raw_judgment = payload.get("matches")
    judgment = _review_judgment(raw_judgment)
    if not judgment:
        raise ValueError("missing review judgment")
    matches = _review_matches_value(judgment)
    lean_statement = str(payload.get("lean_statement") or "").strip()
    paper_statement = str(payload.get("paper_statement") or "").strip()
    agent_statement = str(payload.get("agent_statement") or "").strip()
    source_status = str(payload.get("source_status") or "").strip()
    source_note = str(payload.get("source_note") or "").strip()
    review_scope = str(payload.get("review_scope") or "source_claim").strip()
    prerequisite_key = str(payload.get("prerequisite_key") or "").strip()
    if not paper or not theorem:
        raise ValueError("missing paper/theorem")
    if review_scope not in {"source_claim", "library_prerequisite", "paper_prerequisite"}:
        raise ValueError("invalid review scope")
    if review_scope != "source_claim" and not prerequisite_key:
        raise ValueError("missing prerequisite review key")
    if not lean_statement or not paper_statement or not agent_statement or not source_status or not source_note:
        (
            current_lean_statement,
            current_paper_statement,
            current_agent_statement,
            current_source_status,
            current_source_note,
        ) = get_item_statements(
            paper, theorem
        )
        if not lean_statement:
            lean_statement = current_lean_statement
        if not paper_statement:
            paper_statement = current_paper_statement
        if not agent_statement:
            agent_statement = current_agent_statement
        if not source_status:
            source_status = current_source_status
        if not source_note:
            source_note = current_source_note

    entry = {
        "paper": paper,
        "theorem": theorem,
        "user": user,
        "paper_statement": paper_statement,
        "lean_statement": lean_statement,
        "agent_statement": agent_statement,
        "source_status": source_status,
        "source_note": source_note,
        "review_scope": review_scope,
        "prerequisite_key": prerequisite_key,
        "lean_statement_sha256": statement_digest(lean_statement),
        "paper_statement_sha256": statement_digest(paper_statement),
        "agent_statement_sha256": statement_digest(agent_statement),
        "source_metadata_sha256": source_metadata_digest(source_status, source_note),
        "judgment": judgment,
        "matches": matches,
        "notes": notes,
        "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z"),
    }
    with log_file.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(entry))
        handle.write("\n")
    return entry


def stale_review_summary(
    paper: str | None, log_file: Path | None, slice_filter: str | None = None
) -> dict[str, list[dict[str, Any]] | dict[str, Any]]:
    """Return stale/unreviewed buckets plus overall status for quick checks."""

    papers = gather_paper_data(paper, slice_filter, render_images=False)
    if log_file is not None:
        reviews = read_log_entries(log_file, paper)
    elif paper:
        reviews = read_all_log_entries(paper, None)
    else:
        reviews = read_all_log_entries(None, None)
    rows = build_review_status(papers, reviews)
    buckets = stale_review_rows(rows)
    assumption_rows = assumption_audit_rows(papers)
    # Current typed pages expose the nonaccepting status already projected by
    # ``PreparedReviewSurface``.  The launch-time browser summary must not run
    # the separate repository heuristic and splice its parser-shaped findings
    # into that display.  Explicit assumption CLI/closeout commands retain the
    # complete strict path through ``direct_assumption_audit_rows``.
    prepared_assumptions = {
        str(row.get("paper") or ""): row
        for row in assumption_rows
        if row.get("presentation_only")
    }
    legacy_assumptions = [
        row for row in assumption_rows if not row.get("presentation_only")
    ]
    displayed_assumptions = (
        merge_hidden_premise_audit_rows(legacy_assumptions, paper)
        if legacy_assumptions
        else []
    )
    if prepared_assumptions:
        displayed_assumptions = [
            row
            for row in displayed_assumptions
            if str(row.get("paper") or "") not in prepared_assumptions
        ]
        displayed_assumptions.extend(prepared_assumptions.values())
    return {
        "rows": rows,
        "totals": status_totals(rows),
        "surface_audits": surface_audit_rows(papers),
        "statement_audits": statement_audit_rows(papers),
        "paper_coverage_audits": paper_coverage_audit_rows(papers),
        "assumption_audits": displayed_assumptions,
        "stale": buckets["stale"],
        "unreviewed": buckets["unreviewed"],
        "mismatch": buckets["mismatch"],
    }


def print_statement_audit_status(paper: str | None, slice_filter: str | None = None) -> bool:
    """Print only statement-translation audit diagnostics."""

    rows = direct_statement_audit_rows(paper, slice_filter)
    label = paper or "all papers"
    if slice_filter:
        label = f"{label} slice {slice_filter}"
    has_attention = print_statement_audit_warnings(rows, label)
    if has_attention:
        return True
    total_rows = sum(int(row.get("row_count") or 0) for row in rows)
    total_drafts = sum(int(row.get("draft_count") or 0) for row in rows)
    total_judgments = sum(int(row.get("judgment_count") or 0) for row in rows)
    total_conditional_boundaries = sum(
        int(row.get("conditional_boundary_count") or 0) for row in rows
    )
    boundary_note = (
        f", {total_conditional_boundaries} strict mismatch row(s) accepted as visible-premise boundaries"
        if total_conditional_boundaries
        else ", no missing/stale/flagged items"
    )
    print(
        f"Statement-translation audits for {label} are current: "
        f"{total_rows} row(s), {total_drafts} Lean-to-TeX draft(s), "
        f"{total_judgments} statement-judge row(s){boundary_note}."
    )
    print(
        "This is only the row-local statement match lane. Before treating these "
        "rows as certified paper targets, also run "
        "`python3 scripts/review_dashboard.py --paper <paper> --assumption-precheck` "
        "or the combined `--precheck` path to verify theorem-premise provenance."
    )
    return False


def print_source_inventory_precheck_status(paper: str | None) -> bool:
    """Print source-map blockers and nonblocking coverage work separately.

    Return ``True`` only when the source-map itself blocks a manifest refresh.
    Missing or seed-scaffold semantic coverage remains visible here, but the
    strict paper-coverage/source-to-Lean checks are the fail-closed gates after
    current dashboard rows have been generated.
    """

    summaries = [
        source_inventory_precheck_summary(folder)
        for folder in iter_paper_folders(paper)
    ]
    label = paper or "all papers"
    blockers = [summary for summary in summaries if summary.get("pre_manifest_blocked")]
    pending = [
        summary for summary in summaries if summary.get("semantic_coverage_pending")
    ]
    if blockers:
        print(f"\nSource-map preflight blockers for {label}:")
        for summary in blockers:
            reasons = list(summary.get("pre_manifest_blockers") or [])
            print(f" - {summary['paper']}: {'; '.join(reasons)}.")
        print(
            "Fix these source-map blockers before refreshing Lean signature manifests. "
            "This structural gate does not replace --paper-coverage-check."
        )
    if pending:
        print(f"\nSource-to-dashboard coverage pending for {label}:")
        for summary in pending:
            reasons = list(summary.get("semantic_coverage_pending") or [])
            print(f" - {summary['paper']}: {'; '.join(reasons)}.")
        print(
            "This is expected before the first current row cache exists and does not "
            "block a paper-only --refresh-cache. After that refresh, complete the "
            "source-grounded coverage audit and run --paper-coverage-check and "
            "--source-to-lean-check; those later checks remain fail closed."
        )
    if blockers:
        return True
    if pending:
        return False

    total_inventory = sum(int(summary.get("inventory_count") or 0) for summary in summaries)
    total_coverage = sum(int(summary.get("coverage_item_count") or 0) for summary in summaries)
    print(
        f"Source-inventory precheck for {label} is current: "
        f"{total_inventory} mapped source item(s), {total_coverage} coverage item(s). "
        "Run the full paper-coverage and source-to-Lean checks after refreshing Lean rows."
    )
    return False


def print_paper_coverage_audit_status(
    paper: str | None,
    slice_filter: str | None = None,
    *,
    source_to_lean: bool = False,
) -> bool:
    """Print only paper-level source-coverage diagnostics."""

    rows = direct_paper_coverage_audit_rows(paper, slice_filter)
    label = paper or "all papers"
    if slice_filter:
        label = f"{label} slice {slice_filter}"
    has_attention = print_paper_coverage_audit_warnings(
        rows, label, source_to_lean=source_to_lean
    )
    if has_attention:
        return True
    total_inventory = sum(int(row.get("inventory_count") or 0) for row in rows)
    total_covered = sum(int(row.get("covered_count") or 0) for row in rows)
    total_corrected_targets = sum(
        int(row.get("corrected_target_covered_count") or 0) for row in rows
    )
    total_conditional = sum(int(row.get("conditional_boundary_count") or 0) for row in rows)
    total_support = sum(int(row.get("support_only_count") or 0) for row in rows)
    total_quarantined_support = sum(
        int(row.get("quarantined_defect_support_count") or 0) for row in rows
    )
    total_regular_support = max(total_support - total_quarantined_support, 0)
    total_out_of_scope = sum(int(row.get("out_of_scope_count") or 0) for row in rows)
    total_user_approved_exclusions = sum(
        int(row.get("user_approved_scope_exclusion_count") or 0) for row in rows
    )
    required = sum(1 for row in rows if row.get("audit_required"))
    print(
        f"{'Source-to-Lean' if source_to_lean else 'Paper-coverage'} audits for {label} are current: "
        f"{total_covered}/{total_inventory} source statement(s) covered directly, "
        f"{total_corrected_targets} covered as approved corrected target(s), "
        f"{total_conditional} covered with visible-premise boundaries, "
        f"{total_regular_support} covered by support declarations, "
        f"{total_quarantined_support} quarantined defect(s) supported by counterexamples/refutations (not proof coverage), "
        f"{total_out_of_scope} marked out of scope/not paper targets, "
        f"{total_user_approved_exclusions} source-visible claim(s) expressly excluded by the user, "
        f"{required} required paper audit(s), no missing/stale/flagged items."
    )
    return False


def print_assumption_audit_status(paper: str | None, slice_filter: str | None = None) -> bool:
    """Print only assumption-provenance audit diagnostics."""

    fast_precheck = fast_saved_source_record_assumption_precheck(paper, slice_filter)
    if fast_precheck is not None:
        return print_fast_saved_source_record_assumption_precheck(fast_precheck)

    rows = merge_hidden_premise_audit_rows(
        direct_assumption_audit_rows(paper, slice_filter), paper
    )
    label = paper or "all papers"
    if slice_filter:
        label = f"{label} slice {slice_filter}"
    has_attention = print_assumption_audit_warnings(rows, label)
    if has_attention:
        return True
    total_rows = sum(int(row.get("row_count") or 0) for row in rows)
    print(
        f"Assumption-provenance audits for {label} are current: "
        f"{total_rows} assumption declaration(s), no missing/stale/flagged items."
    )
    return False


def print_stale_review_warning(
    paper: str | None, log_file: Path | None, slice_filter: str | None = None
) -> bool:
    """Print a lightweight launch-time check summary and return whether stale data exists."""

    summary = stale_review_summary(paper, log_file, slice_filter)
    stale_rows = summary["stale"]
    unreviewed_rows = summary["unreviewed"]
    mismatch_rows = summary["mismatch"]
    surface_audits = summary["surface_audits"]
    statement_audits = summary["statement_audits"]
    paper_coverage_audits = summary["paper_coverage_audits"]
    assumption_audits = summary["assumption_audits"]
    totals = summary["totals"]
    label = paper or "all papers"
    if slice_filter:
        label = f"{label} slice {slice_filter}"
    total_items = int(totals.get("total_items") or 0)
    reviewed_items = int(totals.get("reviewed_items") or 0)
    needs_attention = int(totals.get("needs_attention_items") or 0)
    print(
        f"Review status for {label}: {reviewed_items}/{total_items} reviewed, "
        f"{needs_attention} need attention ({len(stale_rows)} stale, "
        f"{len(unreviewed_rows)} unreviewed, {len(mismatch_rows)} mismatch)."
    )
    surface_needs_attention = print_surface_audit_warnings(surface_audits, label)
    statement_needs_attention = print_statement_audit_warnings(statement_audits, label)
    paper_coverage_needs_attention = print_paper_coverage_audit_warnings(
        paper_coverage_audits,
        label,
    )
    assumption_needs_attention = print_assumption_audit_warnings(assumption_audits, label)

    if not stale_rows:
        if not unreviewed_rows and not mismatch_rows:
            print(f"Review checks for {label} are currently up to date.")
            return (
                surface_needs_attention
                or statement_needs_attention
                or paper_coverage_needs_attention
                or assumption_needs_attention
            )
        else:
            print(
                f"Review checks for {label}: no stale checks, but "
                f"{len(unreviewed_rows)} item(s) have no review entry yet and "
                f"{len(mismatch_rows)} item(s) are marked as not matching."
            )
            return True

    print(f"\nReview check: found {len(stale_rows)} stale check(s) in {label}.")
    print("The dashboard loads current Lean/Paper statements on launch, but these")
    print("previously logged entries were checked against an earlier interface snapshot:")
    for row in stale_rows[:12]:
        reasons = []
        if row.get("lean_stale"):
            reasons.append("Lean signature changed")
        if row.get("paper_stale"):
            reasons.append("paper-facing text changed")
        print(
            f" - {row['paper']}.{row['theorem']} "
            f"({' / '.join(reasons) if reasons else 'statement changed'})"
        )
    if len(stale_rows) > 12:
        print(f" - ... {len(stale_rows) - 12} more")
    if unreviewed_rows:
        print(f"{len(unreviewed_rows)} additional item(s) currently need an initial review.")
    if mismatch_rows:
        print(f"{len(mismatch_rows)} additional reviewed item(s) are marked as not matching.")
    print("Open the dashboard and resave checks for these items to refresh the trace.")
    print("The agent Lean drafts are regenerated from the current declarations automatically.")
    return True


class ReusableThreadingHTTPServer(ThreadingHTTPServer):
    allow_reuse_address = True


class ReviewHTTPHandler(BaseHTTPRequestHandler):
    papers: list[dict[str, Any]] = []
    log_file: Path | None = None
    default_user: str = getpass.getuser()
    paper_filter: str | None = None
    slice_filter: str | None = None

    def log_message(self, *_args: Any) -> None:  # silence noisy HTTP logs
        return

    def _json_response(self, status: int, payload: dict[str, Any]) -> None:
        data = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def _collect_path(self) -> tuple[str, dict[str, str]]:
        parsed = urllib.parse.urlsplit(self.path)
        query = urllib.parse.parse_qs(parsed.query)
        clean_query = {k: v[0] for k, v in query.items()}
        return parsed.path, clean_query

    def _send_file(self, path: Path) -> None:
        """Serve a single local file."""

        data = path.read_bytes()
        content_type, _ = mimetypes.guess_type(str(path))
        if path.suffix.lower() == ".txt":
            content_type = "text/plain; charset=utf-8"
        self.send_response(200)
        self.send_header("Content-Type", content_type or "application/octet-stream")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Content-Disposition", "inline")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.end_headers()
        self.wfile.write(data)

    def _send_asset(self, paper: str, filename: str) -> None:
        """Serve a validated paper asset if it belongs to the selected paper."""

        target_paper_dir = None
        for folder in iter_paper_folders(self.paper_filter):
            if folder.name == paper:
                target_paper_dir = folder
                break
        if target_paper_dir is None:
            self.send_error(404, "paper not found")
            return
        if not filename or "/" in filename or "\\" in filename or ".." in filename:
            self.send_error(404, "invalid asset")
            return
        if not filename.lower().endswith(tuple(PAPER_ASSET_EXTENSIONS)):
            self.send_error(404, "unsupported paper asset")
            return
        candidate = target_paper_dir / filename
        if not candidate.exists() or not candidate.is_file():
            self.send_error(404, "asset not found")
            return
        self._send_file(candidate)

    def _send_rendered_statement(self, paper: str, filename: str) -> None:
        """Serve a generated statement-render PNG if it belongs to the paper cache."""

        target_paper_dir = None
        for folder in iter_paper_folders(self.paper_filter):
            if folder.name == paper:
                target_paper_dir = folder
                break
        if target_paper_dir is None:
            self.send_error(404, "paper not found")
            return
        if not filename or "/" in filename or "\\" in filename or ".." in filename:
            self.send_error(404, "invalid rendered statement")
            return
        if not filename.lower().endswith(tuple(PAPER_RENDERED_IMAGE_EXTENSIONS)):
            self.send_error(404, "unsupported rendered statement")
            return
        candidate = target_paper_dir / ".review_traces" / PAPER_RENDERED_STATEMENT_DIR / filename
        if not candidate.exists() or not candidate.is_file():
            self.send_error(404, "rendered statement not found")
            return
        self._send_file(candidate)

    def do_GET(self) -> None:
        path, query = self._collect_path()
        if path == "/":
            papers = gather_paper_data(self.paper_filter, self.slice_filter)
            html = render_static_html(
                papers,
                self.default_user,
                describe_log_target(self.log_file, self.paper_filter),
            )
            body = html.encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        if path.startswith("/paper-assets/"):
            pieces = [segment for segment in path.split("/") if segment]
            if len(pieces) != 3:
                self.send_error(404, "invalid asset request")
                return
            paper = urllib.parse.unquote(pieces[1])
            filename = urllib.parse.unquote(pieces[2])
            self._send_asset(paper, filename)
            return
        if path.startswith("/rendered-statements/"):
            pieces = [segment for segment in path.split("/") if segment]
            if len(pieces) != 3:
                self.send_error(404, "invalid rendered statement request")
                return
            paper = urllib.parse.unquote(pieces[1])
            filename = urllib.parse.unquote(pieces[2])
            self._send_rendered_statement(paper, filename)
            return
        if path == "/api/papers":
            papers = gather_paper_data(self.paper_filter, self.slice_filter)
            self._json_response(200, {"papers": papers})
            return
        if path == "/api/reviews":
            paper = query.get("paper")
            if paper and self.log_file is None:
                try:
                    reviews = read_log_entries(paper_review_log_file(paper))
                except ValueError:
                    reviews = []
            elif paper:
                reviews = read_log_entries(self.log_file, paper)
            else:
                reviews = read_all_log_entries(self.paper_filter, self.log_file)
            self._json_response(200, {"reviews": reviews})
            return
        if path == "/api/library-reviews":
            paper = query.get("paper")
            if paper:
                try:
                    reviews = read_log_entries(paper_library_prerequisite_log_file(paper))
                except ValueError:
                    reviews = []
            else:
                reviews = []
                for folder in iter_paper_folders(self.paper_filter):
                    reviews.extend(
                        read_log_entries(paper_library_prerequisite_log_file(folder.name))
                    )
                reviews.sort(key=lambda entry: str(entry.get("timestamp") or ""))
            self._json_response(200, {"reviews": reviews})
            return
        if path == "/api/status":
            requested_paper = query.get("paper")
            user_filter = query.get("user")
            stale_only = parse_bool_flag(query.get("stale_only"))
            papers = gather_paper_data(
                requested_paper or self.paper_filter,
                self.slice_filter,
                render_images=False,
            )
            if self.log_file is not None:
                if requested_paper:
                    reviews = read_log_entries(self.log_file, requested_paper)
                else:
                    reviews = read_log_entries(self.log_file)
            elif requested_paper:
                try:
                    reviews = read_log_entries(paper_review_log_file(requested_paper))
                except ValueError:
                    reviews = []
            else:
                reviews = read_all_log_entries(self.paper_filter, None)
            rows = build_review_status(papers, reviews)
            rows = filter_review_rows(rows, user_filter=user_filter, stale_only=stale_only)
            self._json_response(
                200,
                {
                    "status": rows,
                    "totals": status_totals(rows),
                    "surface_audits": surface_audit_rows(papers),
                    "statement_audits": statement_audit_rows(papers),
                    "paper_coverage_audits": paper_coverage_audit_rows(papers),
                    "assumption_audits": merge_hidden_premise_audit_rows(
                        assumption_audit_rows(papers),
                        requested_paper or self.paper_filter,
                    ),
                },
            )
            return
        self.send_error(404, "not found")

    def do_POST(self) -> None:
        path, _ = self._collect_path()
        if path not in {"/api/reviews", "/api/library-reviews"}:
            self.send_error(404, "not found")
            return
        length = int(self.headers.get("Content-Length", "0"))
        raw = self.rfile.read(length).decode("utf-8")
        try:
            payload = json.loads(raw or "{}")
        except json.JSONDecodeError:
            self._json_response(400, {"error": "invalid json body"})
            return
        try:
            paper_name = str(payload.get("paper") or "").strip()
            review_scope = str(payload.get("review_scope") or "source_claim").strip()
            if path == "/api/library-reviews":
                if review_scope not in {"library_prerequisite", "paper_prerequisite"}:
                    raise ValueError("library review endpoint needs a prerequisite scope")
                log_file = paper_library_prerequisite_log_file(paper_name)
            elif self.log_file is None:
                log_file = paper_review_log_file(paper_name)
            else:
                log_file = self.log_file
            entry = append_review(log_file, payload, self.default_user)
        except Exception as exc:  # noqa: BLE001 - user input surface
            self._json_response(400, {"error": str(exc)})
            return
        self._json_response(200, {"entry": entry})


def main() -> None:
    parser = argparse.ArgumentParser(description="Review dashboard for paper interface statements.")
    parser.add_argument("--paper", help="Optional paper folder name to limit the dashboard.")
    parser.add_argument(
        "--slice",
        dest="slice_filter",
        default="",
        help="Optional review slice id, or PAPER::slice id, to limit dashboard rows.",
    )
    parser.add_argument(
        "--log-file",
        default="",
        help="Optional single JSONL trace path that overrides per-paper storage.",
    )
    parser.add_argument(
        "--user",
        default="",
        help="Reviewer handle (fallback used in saved entries).",
    )
    parser.add_argument(
        "--user-var",
        action="append",
        dest="user_vars",
        help="Environment variable(s) to check for default username (default GitHub variables).",
    )
    parser.add_argument(
        "--export-format",
        choices=("json", "csv", "md", "validators-md"),
        help="Generate a review status export instead of static HTML when not in server mode.",
    )
    parser.add_argument("--export-file", default="", help="Optional path for exported report output.")
    parser.add_argument("--status-user", default="", help="Filter status rows by reviewer handle.")
    parser.add_argument(
        "--stale-only",
        action="store_true",
        help="Filter status export to rows that need attention.",
    )
    parser.add_argument(
        "--precheck",
        action="store_true",
        help="Print stale review diagnostics for the selected paper and exit.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Like --precheck, but return non-zero if any item needs review or is stale.",
    )
    parser.add_argument(
        "--statement-precheck",
        action="store_true",
        help="Print only Lean-to-TeX and statement-judge audit diagnostics, then exit.",
    )
    parser.add_argument(
        "--statement-check",
        action="store_true",
        help="Like --statement-precheck, but return non-zero for missing/stale/flagged statement-audit rows.",
    )
    parser.add_argument(
        "--paper-coverage-precheck",
        action="store_true",
        help="Print only source-paper statement coverage diagnostics, then exit.",
    )
    parser.add_argument(
        "--paper-coverage-check",
        action="store_true",
        help="Like --paper-coverage-precheck, but return non-zero for missing/stale/flagged coverage rows.",
    )
    parser.add_argument(
        "--source-inventory-precheck",
        action="store_true",
        help=(
            "Check source-map structural readiness without parsing Lean rows; report "
            "coverage work separately before an expensive cache refresh."
        ),
    )
    parser.add_argument(
        "--source-inventory-check",
        action="store_true",
        help=(
            "Like --source-inventory-precheck, but return non-zero only for "
            "source-map blockers. Semantic coverage remains enforced later by "
            "--paper-coverage-check and --source-to-lean-check."
        ),
    )
    parser.add_argument(
        "--source-to-lean-precheck",
        action="store_true",
        help="Print source-paper-to-Lean row correctness diagnostics, then exit.",
    )
    parser.add_argument(
        "--source-to-lean-check",
        action="store_true",
        help=(
            "Like --source-to-lean-precheck, but return non-zero when source coverage "
            "lacks current row-local LLM correctness judgments."
        ),
    )
    parser.add_argument(
        "--assumption-precheck",
        action="store_true",
        help="Print only paper-assumption provenance audit diagnostics, then exit.",
    )
    parser.add_argument(
        "--assumption-check",
        action="store_true",
        help="Like --assumption-precheck, but return non-zero for missing/stale/flagged assumption-audit rows.",
    )
    parser.add_argument(
        "--refresh-cache",
        action="store_true",
        help="Regenerate cached paper-interface rows and exit.",
    )
    parser.add_argument("--serve", action="store_true", help="Start a local review web server.")
    parser.add_argument("--host", default="127.0.0.1", help="Server host when --serve is set.")
    parser.add_argument("--port", type=int, default=8765, help="Server port when --serve is set.")
    args = parser.parse_args()

    if args.user_vars is None:
        args.user_vars = DEFAULT_USER_ENV_VARS.copy()
    user = detect_reviewer_username(args.user, args.user_vars)

    log_file = Path(args.log_file) if args.log_file else None

    if args.precheck or args.check:
        has_attention = print_stale_review_warning(args.paper, log_file, args.slice_filter)
        if args.check and has_attention:
            sys.exit(1)
        return

    if args.statement_precheck or args.statement_check:
        has_attention = print_statement_audit_status(args.paper, args.slice_filter)
        if args.statement_check and has_attention:
            sys.exit(1)
        return

    if args.source_inventory_precheck or args.source_inventory_check:
        has_attention = print_source_inventory_precheck_status(args.paper)
        if args.source_inventory_check and has_attention:
            sys.exit(1)
        return

    if args.paper_coverage_precheck or args.paper_coverage_check:
        has_attention = print_paper_coverage_audit_status(args.paper, args.slice_filter)
        if args.paper_coverage_check and has_attention:
            sys.exit(1)
        return

    if args.source_to_lean_precheck or args.source_to_lean_check:
        has_attention = print_paper_coverage_audit_status(
            args.paper, args.slice_filter, source_to_lean=True
        )
        if args.source_to_lean_check and has_attention:
            sys.exit(1)
        return

    if args.assumption_precheck or args.assumption_check:
        has_attention = print_assumption_audit_status(args.paper, args.slice_filter)
        if args.assumption_check and has_attention:
            sys.exit(1)
        return

    if args.refresh_cache:
        papers = iter_paper_folders(args.paper)
        if not papers:
            if args.paper:
                raise SystemExit(
                    f"no canonical human-review PaperInterface.lean found for paper '{args.paper}'"
                )
            raise SystemExit("no papers with canonical human-review PaperInterface.lean found")
        for folder in papers:
            refresh_cached_review_rows(folder)
            print(f"refreshed dashboard cache for {folder.name}")
        return

    if args.serve:
        handler = ReviewHTTPHandler
        handler.papers = gather_paper_data(args.paper, args.slice_filter)
        handler.log_file = log_file
        handler.default_user = user
        handler.paper_filter = args.paper
        handler.slice_filter = args.slice_filter
        try:
            server = ReusableThreadingHTTPServer((args.host, args.port), handler)
        except OSError as exc:
            print(
                f"Failed to start dashboard server on {args.host}:{args.port}: {exc}"
            )
            if args.host == "0.0.0.0":
                print(
                    "Hint: in WSL2, you may retry with --host 127.0.0.1 or use "
                    "localhost in Windows."
                )
            else:
                print(
                    "Hint: check if another process is already using this port, "
                    "or try a different --port value."
                )
            sys.exit(1)
        print(f"Review dashboard: http://{args.host}:{args.port}/")
        print(f"Log target: {describe_log_target(log_file, args.paper)}")
        print("Run with --precheck or --check for the full launch-time status summary.")
        print("Press Ctrl-C to stop.")
        server.serve_forever()

    if args.export_format:
        papers = gather_paper_data(args.paper, args.slice_filter, render_images=False)
        if log_file is not None:
            if args.paper:
                reviews = read_log_entries(log_file, args.paper)
            else:
                reviews = read_log_entries(log_file)
        elif args.paper:
            reviews = read_all_log_entries(args.paper, None)
        else:
            reviews = read_all_log_entries(None, None)
        rows = build_review_status(papers, reviews)
        rows = filter_review_rows(rows, user_filter=(args.status_user or "").strip() or None, stale_only=args.stale_only)
        if args.export_format == "json":
            payload = json.dumps(
                {
                    "status": rows,
                    "totals": status_totals(rows),
                    "surface_audits": surface_audit_rows(papers),
                    "statement_audits": statement_audit_rows(papers),
                    "paper_coverage_audits": paper_coverage_audit_rows(papers),
                    "assumption_audits": merge_hidden_premise_audit_rows(
                        assumption_audit_rows(papers),
                        args.paper,
                    ),
                },
                indent=2,
            )
        elif args.export_format == "csv":
            payload = render_csv_summary(rows)
        elif args.export_format == "validators-md":
            payload = render_validator_markdown_summary(rows)
        else:
            payload = render_markdown_summary(rows)
        if args.export_file:
            out = Path(args.export_file)
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(payload, encoding="utf-8")
            print(f"Wrote report to {out}")
        else:
            if args.export_format == "json":
                print(payload)
            else:
                sys.stdout.write(payload)
        return

    else:
        papers = gather_paper_data(args.paper, args.slice_filter)
        html = render_static_html(papers, user, describe_log_target(log_file, args.paper))
        if log_file is not None:
            out = log_file.parent / "review_dashboard.html"
        elif args.paper:
            out = paper_review_log_file(args.paper).parent / "review_dashboard.html"
        else:
            out = ROOT / ".review_traces" / "review_dashboard.html"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(html, encoding="utf-8")
        print(f"Wrote dashboard HTML to {out}")
        print("Run with --serve to allow interactive saving to the local review log.")


if __name__ == "__main__":
    main()
