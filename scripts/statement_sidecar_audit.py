#!/usr/bin/env python3
"""Pure interpretation of statement-sidecar audit summaries.

The dashboard owns extraction and freshness validation for the underlying
review evidence.  This module owns only the deterministic conversion from
those already-computed summaries to repository-audit issues.  Keeping that
boundary free of filesystem, Lean, and dashboard imports makes it directly
testable and keeps the repository audit executor focused on orchestration.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping, Sequence


@dataclass(frozen=True)
class StatementSidecarIssue:
    """One repository-audit issue emitted from current sidecar summaries."""

    artifact: str
    message: str


def _counted_parts(
    summary: Mapping[str, object],
    labels: Sequence[tuple[str, str]],
    *,
    boolean_fields: bool = False,
) -> list[str]:
    parts: list[str] = []
    for key, label in labels:
        value = summary.get(key)
        if boolean_fields and isinstance(value, bool):
            if value:
                parts.append(label)
        elif isinstance(value, int) and value:
            parts.append(f"{value} {label}(s)")
    return parts


def statement_sidecar_summary_issues(
    paper_id: str,
    status: object,
    *,
    surface: Mapping[str, object],
    statements: Mapping[str, object],
    paper_coverage: Mapping[str, object],
    assumptions: Mapping[str, object],
    bridge_lanes: Mapping[str, bool],
    v11_required: bool,
    v11_screening_errors: Sequence[str],
    v11_coverage_errors: Sequence[str],
) -> tuple[StatementSidecarIssue, ...]:
    """Convert validated dashboard summaries to stable audit diagnostics."""

    issues: list[StatementSidecarIssue] = []
    if v11_required:
        if v11_screening_errors:
            issues.append(
                StatementSidecarIssue(
                    "audit/v11_raw_source_spec_screening.json",
                    f"`{paper_id}` v11 raw-source-to-expanded-Spec screening needs attention: "
                    + ", ".join(v11_screening_errors[:8])
                    + ("; ..." if len(v11_screening_errors) > 8 else ""),
                )
            )
        if v11_coverage_errors:
            issues.append(
                StatementSidecarIssue(
                    "audit/paper_statement_map.json",
                    f"`{paper_id}` v11 source inventory is not fully covered by "
                    "current raw-source-to-Spec rows: "
                    + ", ".join(v11_coverage_errors[:8])
                    + ("; ..." if len(v11_coverage_errors) > 8 else ""),
                )
            )

    strict_evidence_required = status in {
        "formalized",
        "formalized with caveat",
        "partially formalized",
        "conditional",
    }
    surface_needs_attention = bool(
        surface.get("needs_attention")
        or (strict_evidence_required and not surface.get("has_completed_audit"))
    )
    if surface_needs_attention and not bridge_lanes["review_surface"]:
        reasons: list[str] = []
        if strict_evidence_required and not surface.get("has_completed_audit"):
            reasons.append("missing explicit review-surface LLM pass")
        if surface.get("missing_required"):
            reasons.append("missing review-surface LLM audit")
        if surface.get("stale"):
            reasons.append("stale review-surface LLM audit")
        if surface.get("metadata_missing"):
            reasons.append(
                "review-surface audit missing validator/timestamp success metadata"
            )
        if surface.get("judgment") in {"needs_curation", "uncertain"}:
            reasons.append(f"review-surface judgment `{surface.get('judgment')}`")
        if surface.get("unknown_judgment"):
            reasons.append(
                "unrecognized review-surface judgment "
                f"`{surface.get('judgment') or 'missing'}`"
            )
        issues.append(
            StatementSidecarIssue(
                "audit/review_surface_llm.json",
                f"`{paper_id}` review-surface audit needs attention: "
                + (", ".join(reasons) if reasons else "unknown issue"),
            )
        )

    if paper_coverage.get("needs_attention") and not bridge_lanes["coverage"]:
        parts = _counted_parts(
            paper_coverage,
            (
                ("missing_inventory", "missing required source-statement inventory"),
                ("unresolved_statement_map", "unresolved audit/paper_statement_map.json"),
                ("missing_required", "missing paper-level coverage audit"),
                (
                    "inventory_unknown_source_kind_count",
                    "source statement with unknown source_kind",
                ),
                ("missing_coverage_count", "source statement without coverage judgment"),
                ("partial_count", "partially covered source statement"),
                ("missing_count", "missing source statement"),
                ("uncertain_count", "uncertain source-coverage judgment"),
                ("unknown_count", "unknown source-coverage judgment"),
                ("stale_statement_count", "stale source-statement digest"),
                ("extra_coverage_count", "stale extra coverage item"),
                (
                    "coverage_metadata_missing_count",
                    "coverage item missing validator/timestamp metadata",
                ),
                ("invalid_row_link_count", "invalid linked dashboard row"),
                (
                    "coverage_row_signature_error_count",
                    "coverage judgment without a current elaborated Lean-row signature pin",
                ),
                (
                    "coverage_source_input_error_count",
                    "coverage judgment without the required byte-pinned raw source-input protocol",
                ),
                ("covered_without_rows_count", "covered source statement without linked row"),
                (
                    "covered_without_reason_count",
                    "covered source statement without semantic coverage reason",
                ),
                (
                    "covered_with_seed_reason_count",
                    "covered source statement justified only by dashboard/source-key name matching",
                ),
                (
                    "covered_without_source_evidence_count",
                    "covered source statement without source evidence",
                ),
                (
                    "result_covered_without_proof_row_count",
                    "paper-facing result covered without a theorem/lemma row",
                ),
                (
                    "result_matched_only_by_definition_row_count",
                    "paper-facing result whose positive match evidence is only def/abbrev rows",
                ),
                (
                    "support_without_declarations_count",
                    "support-covered source statement without support declarations",
                ),
                (
                    "support_without_reason_count",
                    "support-covered source statement without semantic coverage reason",
                ),
                (
                    "support_without_source_evidence_count",
                    "support-covered source statement without source evidence",
                ),
                (
                    "invalid_quarantined_defect_support_count",
                    "quarantined source defect without exact-hash semantic support",
                ),
                (
                    "defect_support_judgment_error_count",
                    "missing/stale/malformed defect-support semantic judgment",
                ),
                (
                    "quarantined_defect_direct_coverage_count",
                    "quarantined source defect incorrectly counted as direct proof coverage",
                ),
                (
                    "out_of_scope_without_reason_count",
                    "out-of-scope source statement without semantic reason",
                ),
                (
                    "out_of_scope_without_source_evidence_count",
                    "out-of-scope source statement without source evidence",
                ),
                (
                    "required_out_of_scope_count",
                    "required source-visible review target marked out of scope/not a paper target",
                ),
            ),
            boolean_fields=True,
        )
        if paper_coverage.get("stale_inventory"):
            parts.append("stale source-inventory digest")
        if paper_coverage.get("stale_surface"):
            parts.append("stale review-surface digest")
        if paper_coverage.get("audit_metadata_missing"):
            parts.append(
                "paper-coverage audit missing validator/timestamp success metadata"
            )
        issues.append(
            StatementSidecarIssue(
                "audit/paper_coverage_llm.json",
                f"`{paper_id}` paper-coverage audit needs attention: "
                + (", ".join(parts) if parts else "unknown issue"),
            )
        )

    if paper_coverage.get("source_to_lean_needs_attention") and not bridge_lanes[
        "coverage"
    ]:
        parts = _counted_parts(
            paper_coverage,
            (
                (
                    "support_only_named_claim_count",
                    "theorem-like source statement only support-covered",
                ),
                (
                    "support_only_required_source_item_count",
                    "required source-visible review target only support-covered",
                ),
                (
                    "invalid_quarantined_defect_support_count",
                    "quarantined source defect without exact-hash semantic support",
                ),
                (
                    "defect_support_judgment_error_count",
                    "missing/stale/malformed defect-support semantic judgment",
                ),
                (
                    "quarantined_defect_direct_coverage_count",
                    "quarantined source defect incorrectly counted as direct proof coverage",
                ),
                (
                    "required_out_of_scope_count",
                    "required source-visible review target marked out of scope/not a paper target",
                ),
                (
                    "coverage_row_signature_error_count",
                    "source-to-row link without a current elaborated Lean-row signature pin",
                ),
                (
                    "row_statement_match_missing_count",
                    "source-to-row link without row-local statement judgment",
                ),
                (
                    "row_statement_match_stale_count",
                    "source-to-row link with stale row-local statement judgment",
                ),
                (
                    "row_statement_match_mismatch_count",
                    "source-to-row link with mismatched row-local statement judgment",
                ),
                (
                    "row_statement_match_uncertain_count",
                    "source-to-row link with uncertain row-local statement judgment",
                ),
                (
                    "row_statement_match_unknown_count",
                    "source-to-row link with unknown row-local statement judgment",
                ),
                (
                    "row_statement_match_conditional_without_coverage_boundary_count",
                    "direct source coverage link whose row is only conditionally matched",
                ),
                (
                    "row_statement_match_missing_statement_digest_count",
                    "source-to-row link without row-local statement digest",
                ),
                (
                    "row_statement_match_wrong_statement_digest_count",
                    "source-to-row link with wrong row-local statement digest",
                ),
                (
                    "row_assumption_provenance_missing_count",
                    "source-to-assumption link without provenance judgment",
                ),
                (
                    "row_assumption_provenance_stale_count",
                    "source-to-assumption link with stale provenance judgment",
                ),
                (
                    "row_assumption_provenance_mismatch_count",
                    "source-to-assumption link with provenance mismatch",
                ),
                (
                    "row_assumption_provenance_uncertain_count",
                    "source-to-assumption link with uncertain provenance",
                ),
                (
                    "row_assumption_provenance_unknown_count",
                    "source-to-assumption link with unknown provenance",
                ),
                (
                    "row_assumption_provenance_conditional_without_coverage_boundary_count",
                    "direct source coverage link whose assumption is only a partial boundary",
                ),
            ),
        )
        if parts:
            issues.append(
                StatementSidecarIssue(
                    "audit/paper_coverage_llm.json",
                    f"`{paper_id}` source-to-Lean audit needs attention: "
                    + ", ".join(parts),
                )
            )

    if statements.get("needs_attention") and not bridge_lanes["statement"]:
        parts = _counted_parts(
            statements,
            (
                ("missing_draft_count", "missing Lean-to-TeX draft"),
                ("stale_draft_count", "stale Lean-to-TeX draft"),
                ("missing_judgment_count", "missing statement-judge row"),
                ("stale_judgment_count", "stale statement-judge row"),
                (
                    "missing_obligation_ledger_count",
                    "statement row without a complete semantic obligation ledger",
                ),
                ("mismatch_count", "statement mismatch"),
                ("uncertain_count", "uncertain statement judgment"),
                ("unknown_count", "unknown statement judgment"),
            ),
        )
        issues.append(
            StatementSidecarIssue(
                "audit/statement_match_llm.json",
                f"`{paper_id}` statement-translation audit needs attention: "
                + (", ".join(parts) if parts else "unknown issue"),
            )
        )

    if assumptions.get("needs_attention"):
        parts = _counted_parts(
            assumptions,
            (
                (
                    "missing_rows_count",
                    "configured assumption declaration missing from review surface",
                ),
                ("unlisted_rows_count", "assumption-like declaration not listed in status.json"),
                ("missing_judgment_count", "missing assumption-provenance judgment"),
                ("stale_judgment_count", "stale assumption-provenance judgment"),
                ("not_paper_assumption_count", "assumption judged not paper/source backed"),
                ("uncertain_count", "uncertain assumption-provenance judgment"),
                ("unknown_count", "unknown assumption-provenance judgment"),
                ("unresolved_premise_count", "unresolved premise-level provenance judgment"),
                (
                    "missing_source_location_premise_count",
                    "source-text premise judgment without source location",
                ),
            ),
        )
        issues.append(
            StatementSidecarIssue(
                "audit/assumption_match_llm.json",
                f"`{paper_id}` assumption-provenance audit needs attention: "
                + (", ".join(parts) if parts else "unknown issue"),
            )
        )
    return tuple(issues)
