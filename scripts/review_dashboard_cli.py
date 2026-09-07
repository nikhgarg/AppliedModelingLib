#!/usr/bin/env python3
"""Pure terminal formatting for review-dashboard audit summaries."""

from __future__ import annotations

from typing import Any


def _format_name_sample(names: list[str], limit: int = 8) -> str:
    """Format a compact sample of dashboard row names."""

    if not names:
        return ""
    shown = ", ".join(f"`{name}`" for name in names[:limit])
    if len(names) > limit:
        shown += f", ... {len(names) - limit} more"
    return shown


def print_surface_audit_warnings(rows: list[dict[str, Any]], label: str) -> bool:
    """Print paper-level review-surface warnings and return whether any need attention."""

    warnings = [row for row in rows if row.get("has_warning") or row.get("needs_attention")]
    if not warnings:
        return False
    needs_attention = any(row.get("needs_attention") for row in warnings)
    print(f"\nReview-surface audit warnings for {label}:")
    for row in warnings:
        paper = row.get("paper") or "unknown paper"
        count = int(row.get("row_count") or 0)
        reasons: list[str] = []
        if row.get("oversize"):
            reasons.append(
                f"{count} rows is at or above the {row.get('warn_threshold')} row warning threshold"
            )
        if row.get("missing_required"):
            reasons.append(
                f"{count} rows is above {row.get('llm_threshold')} and needs review_surface_llm.json"
            )
        if row.get("stale"):
            reasons.append("the saved review_surface_llm.json audit is stale")
        if row.get("prompt_version_stale"):
            reasons.append(
                "the saved review_surface_llm.json prompt version is stale "
                f"({row.get('prompt_version') or 'missing'})"
            )
        if row.get("metadata_missing"):
            reasons.append("review_surface_llm.json is missing validator or validated_at success metadata")
        if row.get("judgment") == "needs_curation":
            reasons.append("the LLM audit says the surface needs curation")
        if row.get("judgment") == "uncertain":
            reasons.append("the LLM audit is uncertain")
        if row.get("unknown_judgment"):
            reasons.append(
                f"the LLM audit judgment `{row.get('judgment') or 'missing'}` is not recognized"
            )
        if not reasons:
            reasons.append("the review surface needs attention")
        print(f" - {paper}: {'; '.join(reasons)}.")
        if row.get("reason"):
            print(f"   audit note: {row['reason']}")
    print(
        "For papers above 30 dashboard rows, run a no-paper-context LLM pass that "
        "checks whether every row is genuinely paper-facing, then save "
        "review_surface_llm.json."
    )
    return needs_attention


def print_statement_audit_warnings(rows: list[dict[str, Any]], label: str) -> bool:
    """Print paper-level statement-translation audit warnings."""

    warnings = [row for row in rows if row.get("needs_attention")]
    if not warnings:
        return False
    print(f"\nStatement-translation audit warnings for {label}:")
    for row in warnings:
        paper = row.get("paper") or "unknown paper"
        reasons: list[str] = []
        if row.get("missing_draft_count"):
            reasons.append(f"{row['missing_draft_count']} missing Lean-to-TeX draft(s)")
        if row.get("stale_draft_count"):
            reasons.append(f"{row['stale_draft_count']} stale Lean-to-TeX draft(s)")
        if row.get("missing_judgment_count"):
            reasons.append(f"{row['missing_judgment_count']} missing statement-judge row(s)")
        if row.get("stale_judgment_count"):
            reasons.append(f"{row['stale_judgment_count']} stale statement-judge row(s)")
        if row.get("missing_obligation_ledger_count"):
            reasons.append(
                f"{row['missing_obligation_ledger_count']} incomplete semantic obligation ledger(s)"
            )
        if row.get("unresolved_mismatch_count"):
            reasons.append(f"{row['unresolved_mismatch_count']} unresolved mismatch judgment(s)")
        if row.get("conditional_boundary_count"):
            reasons.append(
                f"{row['conditional_boundary_count']} visible-premise boundary judgment(s)"
            )
        if row.get("uncertain_count"):
            reasons.append(f"{row['uncertain_count']} uncertain judgment(s)")
        if row.get("unknown_count"):
            reasons.append(f"{row['unknown_count']} unknown judgment value(s)")
        library = row.get("library_prerequisites") or {}
        if library.get("pending_count"):
            reasons.append(
                f"{library['pending_count']} material library definition(s) lack a source connection or semantic judgment"
            )
        if library.get("stale_count"):
            reasons.append(
                f"{library['stale_count']} stale material library semantic judgment(s)"
            )
        if library.get("mismatch_count"):
            reasons.append(
                f"{library['mismatch_count']} material library mismatch judgment(s)"
            )
        if library.get("uncertain_count"):
            reasons.append(
                f"{library['uncertain_count']} uncertain material library judgment(s)"
            )
        if row.get("all_uncertain"):
            reasons.append("all rows are uncertain, suggesting a source-statement extraction or parser issue")
        if not reasons:
            reasons.append("statement audit needs attention")
        print(f" - {paper}: {'; '.join(str(reason) for reason in reasons)}.")
        if row.get("all_uncertain"):
            print(
                "   fix the extracted source statements or parser first; do not "
                "leave a paper-wide parser failure as row-by-row uncertainty."
            )
        samples: list[str] = []
        for key, label_text in [
            ("unresolved_mismatch", "unresolved mismatch"),
            ("conditional_boundary", "visible-premise boundary"),
            ("uncertain", "uncertain"),
            ("stale_judgment", "stale judgment"),
            ("missing_obligation_ledger", "missing obligation ledger"),
            ("stale_draft", "stale draft"),
            ("missing_judgment", "missing judgment"),
            ("missing_draft", "missing draft"),
            ("unknown", "unknown"),
            ("library_pending", "library pending"),
            ("library_stale", "library stale"),
            ("library_mismatch", "library mismatch"),
            ("library_uncertain", "library uncertain"),
        ]:
            if key.startswith("library_"):
                sample = _format_name_sample(
                    list((row.get("library_prerequisites") or {}).get(key.removeprefix("library_") or "") or [])
                )
            else:
                sample = _format_name_sample(list(row.get(key) or []))
            if sample:
                samples.append(f"{label_text}: {sample}")
        for sample in samples[:3]:
            print(f"   {sample}")
    print(
        "At statement-review boundaries, regenerate lean_to_tex_llm.json from the "
        "Lean statements alone, preserving every visible binder, hypothesis, "
        "domain condition, named predicate/wrapper application, "
        "equivalence/implication direction, conclusion, and input premise. "
        "Then regenerate statement_match_llm.json from the complete original "
        "paper theorem/definition/formula text and that translation. The judge "
        "should scrutinize every input semantically against the paper source "
        "model, expanding named predicates/wrappers when needed. It must not "
        "approve by theorem label, phrase overlap, or source-looking Lean name. "
        "Mark mismatch or uncertain for omitted subparts, extra non-source "
        "conditions, hidden strengthening inside named predicates, broad "
        "aggregate rows, source-row/certificate/replay/process/bridge packages, or "
        "weakened/strengthened statements. A matches judgment must enumerate "
        "source and Lean parameter/assumption/conclusion atoms, reference every "
        "machine-generated Lean signature atom exactly once, and align every "
        "source conclusion and Lean input by semantic "
        "equivalence or a stated implication; names are routing only. If all rows are uncertain, treat that "
        "as a likely source extraction problem and fix the source map before "
        "accepting row-level judgments. A clean statement audit is still row-local; "
        "run `python3 scripts/review_dashboard.py --paper <paper> "
        "--assumption-precheck` or the combined `--precheck` path before treating "
        "theorem premises as certified."
    )
    return True


def print_paper_coverage_audit_warnings(
    rows: list[dict[str, Any]], label: str, *, source_to_lean: bool = False
) -> bool:
    """Print paper-level source-statement coverage audit warnings."""

    warnings = [
        row
        for row in rows
        if row.get("needs_attention")
        or (source_to_lean and row.get("source_to_lean_needs_attention"))
    ]
    if not warnings:
        return False
    if source_to_lean:
        print(f"\nSource-to-Lean audit warnings for {label}:")
    else:
        print(f"\nPaper-coverage audit warnings for {label}:")
    for row in warnings:
        paper = row.get("paper") or "unknown paper"
        reasons: list[str] = []
        if row.get("missing_inventory"):
            reasons.append("source-statement inventory is required but empty")
        if row.get("unresolved_statement_map"):
            reasons.append(
                "audit/paper_statement_map.json exists but has no resolvable tracked source statements"
            )
        if row.get("inventory_is_scaffold"):
            reasons.append(
                "audit/paper_statement_map.json is still dashboard-seeded or not marked source-curated"
            )
        if row.get("missing_required"):
            reasons.append("missing paper_coverage_llm.json coverage audit")
        if row.get("missing_source_grounded_audit"):
            reasons.append(
                "paper_coverage_llm.json is not a source-grounded source-to-dashboard LLM audit"
            )
        if row.get("prompt_version_stale"):
            reasons.append(
                "the saved paper_coverage_llm.json prompt version is stale "
                f"({row.get('prompt_version') or 'missing'})"
            )
        if row.get("audit_metadata_missing"):
            reasons.append("paper_coverage_llm.json is missing validator or validated_at success metadata")
        if row.get("coverage_metadata_missing_count"):
            reasons.append(
                f"{row['coverage_metadata_missing_count']} coverage item(s) lack validator/timestamp metadata"
            )
        if row.get("inventory_missing_source_url_count"):
            reasons.append(
                f"{row['inventory_missing_source_url_count']} source-inventory statement(s) lack source URL"
            )
        if row.get("inventory_missing_source_provenance_count"):
            reasons.append(
                f"{row['inventory_missing_source_provenance_count']} source-inventory statement(s) lack source location/status"
            )
        if row.get("inventory_unknown_source_kind_count"):
            reasons.append(
                f"{row['inventory_unknown_source_kind_count']} source-inventory statement(s) use unknown source_kind values"
            )
        if row.get("missing_coverage_count"):
            reasons.append(f"{row['missing_coverage_count']} source statement(s) missing coverage row")
        if row.get("missing_statement_digest_count"):
            reasons.append(
                f"{row['missing_statement_digest_count']} coverage item(s) lack source-statement digest"
            )
        if row.get("partial_count"):
            reasons.append(f"{row['partial_count']} partially covered source statement(s)")
        if row.get("missing_count"):
            reasons.append(f"{row['missing_count']} source statement(s) judged missing")
        if row.get("uncertain_count"):
            reasons.append(f"{row['uncertain_count']} uncertain source-coverage judgment(s)")
        if row.get("unknown_count"):
            reasons.append(f"{row['unknown_count']} unknown coverage judgment value(s)")
        if row.get("stale_inventory"):
            reasons.append("the saved paper_coverage_llm.json source-inventory digest is stale")
        if row.get("stale_surface"):
            reasons.append("the saved paper_coverage_llm.json review-surface digest is stale")
        if row.get("stale_statement_count"):
            reasons.append(f"{row['stale_statement_count']} stale source-statement digest(s)")
        if row.get("invalid_row_link_count"):
            reasons.append(f"{row['invalid_row_link_count']} linked dashboard row(s) no longer exist")
        if row.get("coverage_row_signature_error_count"):
            reasons.append(
                f"{row['coverage_row_signature_error_count']} coverage link(s) lack a current elaborated Lean signature pin"
            )
        if row.get("covered_without_rows_count"):
            reasons.append(f"{row['covered_without_rows_count']} covered source statement(s) lack linked dashboard rows")
        if row.get("covered_without_reason_count"):
            reasons.append(f"{row['covered_without_reason_count']} covered source statement(s) lack match reasons")
        if row.get("covered_with_seed_reason_count"):
            reasons.append(f"{row['covered_with_seed_reason_count']} covered source statement(s) only have exact-key scaffold reasons")
        if row.get("covered_without_source_evidence_count"):
            reasons.append(f"{row['covered_without_source_evidence_count']} covered source statement(s) lack source evidence")
        if row.get("coverage_route_mismatch_count"):
            reasons.append(
                f"{row['coverage_route_mismatch_count']} coverage link(s) are not pinned to the row's exact semantic source route"
            )
        if row.get("result_covered_without_proof_row_count"):
            reasons.append(
                f"{row['result_covered_without_proof_row_count']} paper-facing result(s) are directly covered without a theorem/lemma row"
            )
        if row.get("result_matched_only_by_definition_row_count"):
            reasons.append(
                f"{row['result_matched_only_by_definition_row_count']} paper-facing result(s) have positive match evidence only from def/abbrev rows"
            )
        if row.get("support_without_declarations_count"):
            reasons.append(
                f"{row['support_without_declarations_count']} support-covered source statement(s) lack support declarations"
            )
        if row.get("support_without_reason_count"):
            reasons.append(
                f"{row['support_without_reason_count']} support-covered source statement(s) lack reasons"
            )
        if row.get("support_without_source_evidence_count"):
            reasons.append(
                f"{row['support_without_source_evidence_count']} support-covered source statement(s) lack source evidence"
            )
        if row.get("invalid_proof_support_count"):
            reasons.append(
                f"{row['invalid_proof_support_count']} proof-support source item(s) lack an exact transparent, proof-routed Spec route"
            )
        if row.get("invalid_quarantined_defect_support_count"):
            reasons.append(
                f"{row['invalid_quarantined_defect_support_count']} quarantined source defect(s) lack exact-hash semantic counterexample/refutation support"
            )
        if row.get("defect_support_judgment_error_count"):
            reasons.append(
                f"{row['defect_support_judgment_error_count']} defect-support semantic judgment(s) are missing, stale, malformed, or tautological"
            )
        if row.get("quarantined_defect_direct_coverage_count"):
            reasons.append(
                f"{row['quarantined_defect_direct_coverage_count']} quarantined source defect(s) are incorrectly counted as direct proof coverage"
            )
        if row.get("user_approved_scope_exclusion_error_count"):
            reasons.append(
                f"{row['user_approved_scope_exclusion_error_count']} user-approved scope exclusion(s) lack complete approval or pinned source evidence"
            )
        if row.get("required_out_of_scope_count"):
            reasons.append(
                f"{row['required_out_of_scope_count']} required source-visible review target(s) are marked out of scope/not paper targets"
            )
        if source_to_lean and row.get("support_only_named_claim_count"):
            reasons.append(
                f"{row['support_only_named_claim_count']} theorem-like source statement(s) are only support-covered, without review-row statement-match audit"
            )
        if source_to_lean and row.get("support_only_required_source_item_count"):
            reasons.append(
                f"{row['support_only_required_source_item_count']} required source-visible review target(s) are only support-covered, without review-row statement-match audit"
            )
        if source_to_lean and row.get("row_statement_match_missing_count"):
            reasons.append(
                f"{row['row_statement_match_missing_count']} source-to-row link(s) lack row-local LLM correctness judgments"
            )
        if source_to_lean and row.get("row_statement_match_stale_count"):
            reasons.append(
                f"{row['row_statement_match_stale_count']} source-to-row link(s) use stale row-local LLM correctness judgments"
            )
        if source_to_lean and row.get("row_statement_match_mismatch_count"):
            reasons.append(
                f"{row['row_statement_match_mismatch_count']} source-to-row link(s) point to row-local LLM correctness mismatches"
            )
        if source_to_lean and row.get("row_statement_match_uncertain_count"):
            reasons.append(
                f"{row['row_statement_match_uncertain_count']} source-to-row link(s) point to uncertain row-local LLM correctness judgments"
            )
        if source_to_lean and row.get("row_statement_match_unknown_count"):
            reasons.append(
                f"{row['row_statement_match_unknown_count']} source-to-row link(s) point to unknown row-local LLM correctness judgments"
            )
        if source_to_lean and row.get("row_statement_match_conditional_without_coverage_boundary_count"):
            reasons.append(
                f"{row['row_statement_match_conditional_without_coverage_boundary_count']} source-to-row link(s) rely on conditional row-local mismatches while source coverage is marked direct"
            )
        if source_to_lean and row.get("row_statement_match_missing_statement_digest_count"):
            reasons.append(
                f"{row['row_statement_match_missing_statement_digest_count']} source-to-row link(s) have row-local statement judgments without saved paper-statement digests"
            )
        if source_to_lean and row.get("row_statement_match_wrong_statement_digest_count"):
            reasons.append(
                f"{row['row_statement_match_wrong_statement_digest_count']} source-to-row link(s) have row-local statement judgments for a different current row statement"
            )
        if source_to_lean and row.get("row_assumption_provenance_missing_count"):
            reasons.append(
                f"{row['row_assumption_provenance_missing_count']} assumption-linked source-to-row link(s) lack assumption-provenance judgments"
            )
        if source_to_lean and row.get("row_assumption_provenance_stale_count"):
            reasons.append(
                f"{row['row_assumption_provenance_stale_count']} assumption-linked source-to-row link(s) use stale assumption-provenance judgments"
            )
        if source_to_lean and row.get("row_assumption_provenance_mismatch_count"):
            reasons.append(
                f"{row['row_assumption_provenance_mismatch_count']} assumption-linked source-to-row link(s) are judged not to be source assumptions"
            )
        if source_to_lean and row.get("row_assumption_provenance_uncertain_count"):
            reasons.append(
                f"{row['row_assumption_provenance_uncertain_count']} assumption-linked source-to-row link(s) have uncertain assumption-provenance judgments"
            )
        if source_to_lean and row.get("row_assumption_provenance_unknown_count"):
            reasons.append(
                f"{row['row_assumption_provenance_unknown_count']} assumption-linked source-to-row link(s) have unknown assumption-provenance judgments"
            )
        if source_to_lean and row.get("row_assumption_provenance_conditional_without_coverage_boundary_count"):
            reasons.append(
                f"{row['row_assumption_provenance_conditional_without_coverage_boundary_count']} assumption-linked source-to-row link(s) are partial boundaries while source coverage is marked direct"
            )
        if row.get("out_of_scope_without_reason_count"):
            reasons.append(
                f"{row['out_of_scope_without_reason_count']} out-of-scope source statement(s) lack reasons"
            )
        if row.get("out_of_scope_without_source_evidence_count"):
            reasons.append(
                f"{row['out_of_scope_without_source_evidence_count']} out-of-scope source statement(s) lack source evidence"
            )
        if row.get("extra_coverage_count"):
            reasons.append(f"{row['extra_coverage_count']} stale extra coverage item(s)")
        if not reasons:
            reasons.append("paper-coverage audit needs attention")
        print(f" - {paper}: {'; '.join(str(reason) for reason in reasons)}.")
        samples: list[str] = []
        sample_specs = [
            ("missing_coverage", "missing coverage"),
            ("inventory_missing_source_url", "missing source URL"),
            ("inventory_missing_source_provenance", "missing source provenance"),
            ("inventory_unknown_source_kind", "unknown source_kind"),
            ("missing_statement_digest", "missing digest"),
            ("missing", "judged missing"),
            ("partial", "partial"),
            ("uncertain", "uncertain"),
            ("stale_statement", "stale statement"),
            ("invalid_row_links", "invalid row link"),
            ("coverage_row_signature_errors", "row-signature pin"),
            ("covered_without_rows", "covered without row"),
            ("covered_without_reason", "covered without reason"),
            ("covered_with_seed_reason", "exact-key scaffold reason"),
            ("covered_without_source_evidence", "missing source evidence"),
            ("coverage_route_mismatch", "coverage route mismatch"),
            ("result_covered_without_proof_rows", "result without proof row"),
            (
                "result_matched_only_by_definition_rows",
                "result matched only by def/abbrev",
            ),
            ("coverage_metadata_missing", "missing audit metadata"),
            ("support_without_declarations", "support missing declarations"),
            ("support_without_reason", "support without reason"),
            ("support_without_source_evidence", "support missing source evidence"),
            (
                "invalid_quarantined_defect_support",
                "invalid quarantined-defect support",
            ),
            (
                "defect_support_judgment_errors",
                "invalid defect-support semantic judgment",
            ),
            (
                "quarantined_defect_direct_coverage",
                "quarantined defect counted as proved",
            ),
            (
                "user_approved_scope_exclusion_errors",
                "invalid user-approved scope exclusion",
            ),
            ("required_out_of_scope", "required source target scoped out"),
            ("out_of_scope_without_reason", "out-of-scope without reason"),
            ("out_of_scope_without_source_evidence", "out-of-scope missing source evidence"),
            ("extra_coverage", "extra stale item"),
            ("unknown", "unknown"),
        ]
        if source_to_lean:
            sample_specs.extend(
                [
                    ("support_only_named_claims", "support-only named claim"),
                    ("support_only_required_source_items", "support-only required source target"),
                    ("row_statement_match_missing", "missing row correctness"),
                    ("row_statement_match_stale", "stale row correctness"),
                    ("row_statement_match_mismatch", "mismatched row correctness"),
                    ("row_statement_match_uncertain", "uncertain row correctness"),
                    ("row_statement_match_unknown", "unknown row correctness"),
                    (
                        "row_statement_match_conditional_without_coverage_boundary",
                        "conditional row but direct coverage",
                    ),
                    ("row_statement_match_missing_statement_digest", "missing row-statement digest"),
                    ("row_statement_match_wrong_statement_digest", "wrong row-statement digest"),
                    ("row_assumption_provenance_missing", "missing assumption provenance"),
                    ("row_assumption_provenance_stale", "stale assumption provenance"),
                    ("row_assumption_provenance_mismatch", "assumption provenance mismatch"),
                    ("row_assumption_provenance_uncertain", "uncertain assumption provenance"),
                    ("row_assumption_provenance_unknown", "unknown assumption provenance"),
                    (
                        "row_assumption_provenance_conditional_without_coverage_boundary",
                        "partial assumption but direct coverage",
                    ),
                ]
            )
        for key, label_text in sample_specs:
            sample = _format_name_sample(list(row.get(key) or []))
            if sample:
                samples.append(f"{label_text}: {sample}")
        for sample in samples[:4]:
            print(f"   {sample}")
    print(
        "This is the paper-level coverage lane: build a source-statement inventory "
        "from the source PDF/TeX/text, not from Lean row names, then have an "
        "independent LLM judge whether each paper statement is covered by one or "
        "more dashboard rows. Save that semantic source-to-dashboard judgment in "
        "paper_coverage_llm.json with audit_kind=source_to_dashboard_llm, "
        "source_grounded=true, source evidence, linked dashboard rows, an exact "
        "review_row_signature_sha256 pin for every linked row, and a "
        "nontrivial match reason. Exact-key seeding is only a scaffold. Do not "
        "mark source-visible definitions, examples, remarks, propositions, "
        "theorems, corollaries, or main-text lemmas as out of scope merely to keep "
        "the review surface compact; expose dashboard rows so the LLM-as-judge "
        "can inspect them. Appendix lemmas are a judgment call, but appendix "
        "theorems and corollaries should be covered. The "
        "source result lane requires an actual reviewed theorem/lemma declaration; "
        "a matching def/abbrev is specification vocabulary and cannot supply proof "
        "credit. A quarantined_source_defect item remains unproved and may use "
        "support_only only with a current defect_support_match_llm.json judgment "
        "that exact-hash pins the validated source defect, Lean statement, and "
        "elaborated signature and semantically aligns every theorem atom. Trivial "
        "or reflexive tautologies cannot provide defect support. The "
        "stricter source-to-Lean lane requires linked non-assumption rows to have "
        "current row-local LLM correctness judgments in statement_match_llm.json "
        "for the same current dashboard paper statement. Explicit Assumptions.lean "
        "rows instead require current assumption_match_llm.json provenance evidence; "
        "they are source model conditions, not duplicate theorem conclusions."
    )
    return True


def print_assumption_audit_warnings(rows: list[dict[str, Any]], label: str) -> bool:
    """Print paper-level assumption-provenance warnings."""

    warnings = [row for row in rows if row.get("has_warning") or row.get("needs_attention")]
    if not warnings:
        return False
    print(f"\nAssumption-provenance audit warnings for {label}:")
    for row in warnings:
        paper = row.get("paper") or "unknown paper"
        reasons: list[str] = []
        if row.get("missing_rows_count"):
            reasons.append(f"{row['missing_rows_count']} configured assumption declaration(s) missing")
        if row.get("unlisted_rows_count"):
            reasons.append(f"{row['unlisted_rows_count']} assumption-like declaration(s) not listed in status.json")
        if row.get("missing_judgment_count"):
            reasons.append(f"{row['missing_judgment_count']} missing assumption-judge declaration(s)")
        if row.get("stale_judgment_count"):
            reasons.append(f"{row['stale_judgment_count']} stale assumption-judge declaration(s)")
        if row.get("not_paper_assumption_count"):
            reasons.append(f"{row['not_paper_assumption_count']} declaration(s) judged not to be paper assumptions")
        if row.get("uncertain_count"):
            reasons.append(f"{row['uncertain_count']} uncertain assumption-judge declaration(s)")
        if row.get("unknown_count"):
            reasons.append(f"{row['unknown_count']} unknown assumption-judge value(s)")
        if row.get("partial_boundary_count"):
            reasons.append(f"{row['partial_boundary_count']} partial-boundary declaration(s)")
        if row.get("partial_boundary_premise_count"):
            reasons.append(
                f"{row['partial_boundary_premise_count']} premise-level partial boundary finding(s)"
            )
        if row.get("unresolved_premise_count"):
            reasons.append(
                f"{row['unresolved_premise_count']} unresolved premise-level judgment(s)"
            )
        if row.get("missing_source_location_premise_count"):
            reasons.append(
                f"{row['missing_source_location_premise_count']} source-text premise judgment(s) missing source_location"
            )
        if row.get("hidden_premise_count"):
            hidden_bits: list[str] = [f"{row['hidden_premise_count']} hidden premise finding(s)"]
            if row.get("hidden_premise_error_count"):
                hidden_bits.append(f"{row['hidden_premise_error_count']} error")
            if row.get("hidden_premise_warning_count"):
                hidden_bits.append(f"{row['hidden_premise_warning_count']} warning")
            reasons.append(", ".join(hidden_bits))
        if row.get("accepted_conditional_premise_count"):
            reasons.append(
                f"{row['accepted_conditional_premise_count']} accepted visible-premise finding(s)"
            )
        if row.get("hidden_premise_audit_error"):
            reasons.append(f"could not run hidden-premise audit: {row['hidden_premise_audit_error']}")
        if not reasons:
            reasons.append("assumption provenance needs attention")
        print(f" - {paper}: {'; '.join(str(reason) for reason in reasons)}.")
        samples: list[str] = []
        for key, label_text in [
            ("missing_rows", "missing declaration"),
            ("unlisted_rows", "unlisted declaration"),
            ("not_paper_assumption", "not paper assumption"),
            ("uncertain", "uncertain"),
            ("stale_judgment", "stale judgment"),
            ("missing_judgment", "missing judgment"),
            ("unknown", "unknown"),
            ("partial_boundary_premises", "partial premise"),
            ("unresolved_premises", "unresolved premise"),
            ("missing_source_location_premises", "missing premise source"),
        ]:
            sample = _format_name_sample(list(row.get(key) or []))
            if sample:
                samples.append(f"{label_text}: {sample}")
        for sample in samples[:4]:
            print(f"   {sample}")
        for sample in list(row.get("hidden_premise_samples") or [])[:3]:
            print(f"   hidden premise: {sample}")
        for sample in list(row.get("accepted_conditional_premise_samples") or [])[:3]:
            print(f"   accepted visible premise: {sample}")
    print(
        "Every paper-facing theorem premise that is not derived in Lean must be "
        "declared in Assumptions.lean, listed in "
        "status.json review_surface.assumption_names, and judged in "
        "assumption_match_llm.json as a true paper/source model assumption, "
        "unless it is an explicitly accepted statement-level visible-premise "
        "boundary recorded in statement_match_llm.json. The judge must inspect "
        "premise semantics rather than names: certificate, replay, process, "
        "bridge, source-row, or broad package premises need a constructor from "
        "paper primitives or they remain partial/conditional."
    )
    return True
