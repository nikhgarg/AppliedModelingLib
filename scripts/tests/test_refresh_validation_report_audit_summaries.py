#!/usr/bin/env python3
"""Regression tests for compatible validation-report summary refreshes."""

from __future__ import annotations

from collections import Counter
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import refresh_validation_report_audit_summaries as REFRESH  # noqa: E402


SUMMARY = {
    "coverage": "source coverage has 1 covered",
    "statement": "statement LLM-as-judge has 1 matches",
    "tex": "Lean-to-TeX has 1 row translation",
    "assumption": "assumption provenance has 1 paper_condition",
    "record_match": "source-record classification has 1 proved_from_primitives",
    "record_audit": "source-record audit reports 1 review row",
    "review": "review-surface audit passes over 1 review row",
}


class LegacyAuditSummaryCompatibilityTests(unittest.TestCase):
    def test_current_report_selects_inputs_before_any_legacy_acquisition(self) -> None:
        cases = (
            ({"require_source_spec_correspondence": True}, {}),
            ({"require_v11_raw_source_spec_screening": True}, {}),
            ({"llm_statement_review": {"required_prompt_version": "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-claim-atoms-v3"}}, {}),
            ({}, {"source_spec_correspondence_schema": 1}),
        )
        for surface, source_map in cases:
            with self.subTest(surface=surface, source_map=source_map):
                with tempfile.TemporaryDirectory() as temp_dir:
                    folder = Path(temp_dir) / "Fixture"
                    audit = folder / "audit"
                    audit.mkdir(parents=True)
                    report = folder / REFRESH.REPORT
                    # Even a complete old layout must remain authored text.
                    original = "# Report\n\n" + "\n".join(
                        f"## {section}. Preserved author section\n\nAuthor prose.\n"
                        for section in (12, 13, 14, 15, 20, 21)
                    )
                    report.write_text(original, encoding="utf-8")
                    (folder / "status.json").write_text(
                        json.dumps({"review_surface": surface}), encoding="utf-8"
                    )
                    map_path = audit / "paper_statement_map.json"
                    map_path.write_text(json.dumps(source_map), encoding="utf-8")
                    retired_names = (
                        set(REFRESH.CANONICAL_SIDECAR_NAMES.values())
                        | set(REFRESH.SUMMARY_SIDECAR_NAMES.values())
                    ) - {"paper_statement_map.json"}
                    retired_paths = {
                        parent / name
                        for parent in (folder, audit)
                        for name in retired_names
                    }
                    retired_paths.add(folder / "paper_statement_map.json")
                    retired_paths.add(
                        folder / ".review_traces" / "paper_interface_cache.json"
                    )
                    raw_record = audit / "source_record_audit.json"
                    raw_record.write_text("{" + " " * (2 * 1024 * 1024), encoding="utf-8")
                    real_read_bytes = Path.read_bytes

                    def reject_retired_read(path: Path) -> bytes:
                        if path in retired_paths:
                            raise PermissionError("retired input must not be acquired")
                        return real_read_bytes(path)

                    with (
                        mock.patch.object(Path, "read_bytes", reject_retired_read),
                        mock.patch.object(
                            REFRESH, "saved_report_reuse_authorization",
                            side_effect=AssertionError("current report requested legacy reuse"),
                        ),
                        mock.patch.object(
                            REFRESH, "saved_sidecar_reuse_authorization",
                            side_effect=AssertionError("current report revalidated legacy reuse"),
                        ),
                    ):
                        prepared = REFRESH.prepare_report(report)
                        self.assertEqual(prepared.rendered, original)
                        self.assertFalse(retired_paths.intersection(prepared.snapshot.input_paths))
                        raw_record.write_text("changed retired bytes", encoding="utf-8")
                        REFRESH.validate_prepared_report(prepared, closure_provider=object())
                        map_path.write_text(json.dumps({**source_map, "changed": True}), encoding="utf-8")
                        with self.assertRaisesRegex(ValueError, "inputs changed"):
                            REFRESH.validate_prepared_report(prepared, closure_provider=object())

    def test_historical_report_still_rejects_malformed_legacy_input(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            report = folder / REFRESH.REPORT
            report.write_text("# Historical report\n", encoding="utf-8")
            (folder / "status.json").write_text("{}", encoding="utf-8")
            (audit / "source_record_audit.json").write_text("not JSON", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "valid JSON"):
                REFRESH.load_report_input_snapshot(report)

    def test_direct_source_spec_reports_are_not_rewritten_by_legacy_refresher(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "EX24Example"
            folder.mkdir()
            report = folder / "FINAL_VALIDATION_REPORT.md"
            original = "# Closeout\n\nSource-first review links stay intact.\n"
            report.write_text(original, encoding="utf-8")
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "llm_statement_review": {
                                "required_prompt_version": (
                                    "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-claim-atoms-supporting-declarations-v4"
                                )
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            prepared = REFRESH.prepare_report(report)

        self.assertEqual(prepared.rendered, original)

    def test_report_input_digest_tracks_present_missing_and_changed_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            present = Path(temp_dir) / "present.json"
            missing = Path(temp_dir) / "missing.json"
            present.write_text("{}\n", encoding="utf-8")
            paths = (missing, present)

            initial = REFRESH.report_input_digest(paths)
            present.write_text('{"changed": true}\n', encoding="utf-8")
            changed = REFRESH.report_input_digest(paths)
            missing.write_text("{}\n", encoding="utf-8")
            created = REFRESH.report_input_digest(paths)

        self.assertNotEqual(initial, changed)
        self.assertNotEqual(changed, created)

    def test_machine_enums_render_as_human_labels_and_blank_values_are_ignored(
        self,
    ) -> None:
        counts = Counter(
            {
                "validated_source_assumption": 3,
                "container_recursively_audited": 2,
                "nonpropositional_witness_data": 1,
            }
        )

        self.assertEqual(
            REFRESH.ordered_counts(counts, REFRESH.SOURCE_RECORD_ORDER),
            "3 source condition, 2 recursively audited support, "
            "1 non-propositional witness data",
        )
        self.assertEqual(
            REFRESH.count_field(
                {"items": [{"resolution": ""}, {"resolution": "  "}]},
                "resolution",
            ),
            Counter(),
        )
        self.assertEqual(
            REFRESH.ordered_counts(Counter({"future_machine_label": 2}), []),
            "2 result needing review",
        )

    def test_generated_block_only_report_does_not_require_legacy_summary_line(
        self,
    ) -> None:
        report = "# Report\n\n<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->\nold\n<!-- END GENERATED LLM-AS-JUDGE RESULTS -->\n"

        self.assertEqual(
            REFRESH.replace_audit_summary(
                report,
                SUMMARY,
                ROOT / "papers" / "Fixture" / "FINAL_VALIDATION_REPORT.md",
            ),
            report,
        )

    def test_legacy_summary_line_is_still_replaced(self) -> None:
        report = "# Report\n\n- Audit summary: stale.\n"

        self.assertEqual(
            REFRESH.replace_audit_summary(
                report,
                SUMMARY,
                ROOT / "papers" / "Fixture" / "FINAL_VALIDATION_REPORT.md",
            ),
            "# Report\n\n" + REFRESH.audit_summary_line(SUMMARY) + "\n",
        )

    def test_source_record_detail_distinguishes_discovery_from_resolution(self) -> None:
        detail = REFRESH.source_record_audit_detail(
            {
                "review_row_count": 34,
                "configured_review_row_count": 49,
                "boundary_input_count": 209,
                "conclusion_dependency_count": 20,
                "recursive_field_count": 18,
                "semantic_model_item_count": 34,
                "unresolved_conclusion_dependency_count": 0,
                "recursion_failure_count": 0,
            }
        )

        self.assertEqual(
            detail,
            "34 source-record review rows (from 49 configured review-surface rows), "
            "209 boundary inputs, 20 conclusion dependencies, 18 recursive fields, "
            "34 semantic-model records, 0 source-record-only unresolved conclusion dependencies, "
            "0 recursion failures",
        )

    def test_write_mode_final_authorizes_changed_report_only_once(self) -> None:
        def prepared(name: str, *, changed: bool) -> REFRESH.PreparedReport:
            path = ROOT / "papers" / name / REFRESH.REPORT
            snapshot = REFRESH.ReportInputSnapshot(
                path=path,
                text="old\n",
                status={},
                evidence={},
                sidecar_paths={},
                record_match=None,
                record_audit=None,
                cache_rows=(),
                input_paths=(path,),
                input_sha256="a" * 64,
            )
            return REFRESH.PreparedReport(
                snapshot=snapshot,
                reuse=REFRESH.SavedSidecarReuseAuthorization(False),
                rendered="new\n" if changed else "old\n",
            )

        changed = prepared("ChangedFixture", changed=True)
        unchanged = prepared("UnchangedFixture", changed=False)
        with (
            mock.patch.object(
                REFRESH,
                "parse_args",
                return_value=REFRESH.argparse.Namespace(check=False, paper=None),
            ),
            mock.patch.object(
                REFRESH,
                "public_report_paths",
                return_value=[changed.snapshot.path, unchanged.snapshot.path],
            ),
            mock.patch.object(
                REFRESH,
                "prepare_report",
                side_effect=[changed, unchanged],
            ),
            mock.patch.object(
                REFRESH,
                "validate_prepared_report",
            ) as validate,
            mock.patch.object(
                REFRESH,
                "write_prepared_report",
            ) as write,
        ):
            result = REFRESH.main()

        self.assertEqual(result, 0)
        self.assertEqual(
            [call.args[0] for call in validate.call_args_list], [unchanged]
        )
        self.assertEqual([call.args[0] for call in write.call_args_list], [changed])


class HumanFacingLedgerGenerationTests(unittest.TestCase):
    @staticmethod
    def legacy_report_template() -> str:
        """Small report declaring the legacy generated-ledger layout."""

        return "\n".join(
            [
                "# Legacy report",
                "",
                "## 12. Validation Checks",
                "",
                "## 13. Paper Assumption Provenance",
                "",
                "## 14. Displayed Formula Provenance",
                "",
                "## 15. Supporting Detail",
                "",
                "## 20. Paper-Facing Statement Validator Ledger",
                "",
                "## 21. Source-Coverage Audit Ledger",
                "",
            ]
        )

    def test_reason_text_preserves_complete_human_review_comment(self) -> None:
        reason = "Reviewed source condition. " * 20
        resolution = "The Lean statement preserves the complete condition. " * 10

        rendered = REFRESH.reason_text(
            {"reason": reason, "resolution_reason": resolution}
        )

        self.assertEqual(
            rendered,
            REFRESH.human_text(f"{reason} {resolution}"),
        )
        self.assertGreater(len(rendered), 360)
        self.assertNotIn("...", rendered)

    def test_generated_ledgers_share_one_semantic_surface_projection(self) -> None:
        folder = Path("papers/Fixture")
        status = {"id": "Fixture"}
        evidence = {
            "assumption": None,
            "coverage": None,
            "source_map": None,
            "statement": None,
            "tex": None,
            "review": None,
        }
        surface = {
            "rows": [],
            "orphan_statement_keys": [],
            "orphan_assumption_keys": [],
            "orphan_tex_keys": [],
        }
        reuse = mock.sentinel.reuse
        with (
            mock.patch.object(REFRESH, "status_payload", return_value=status),
            mock.patch.object(REFRESH, "canonical_sidecars", return_value=evidence),
            mock.patch.object(
                REFRESH,
                "saved_report_reuse_authorization",
                return_value=reuse,
            ),
            mock.patch.object(
                REFRESH,
                "semantic_review_surface",
                return_value=surface,
            ) as project,
            mock.patch.object(REFRESH, "assumption_ledger", return_value="13") as a,
            mock.patch.object(REFRESH, "formula_ledger", return_value="14") as f,
            mock.patch.object(REFRESH, "statement_ledger", return_value="20") as s,
            mock.patch.object(
                REFRESH,
                "source_coverage_ledger",
                return_value="21",
            ) as c,
        ):
            blocks = REFRESH.generated_section_blocks(folder)

        self.assertEqual(blocks, {13: "13", 14: "14", 20: "20", 21: "21"})
        project.assert_called_once()
        for ledger in (a, f, s, c):
            self.assertIs(ledger.call_args.kwargs["semantic_surface"], surface)

    def make_fixture(self, root: Path) -> Path:
        folder = root / "EX24Example"
        audit = folder / "audit"
        audit.mkdir(parents=True)
        traces = folder / ".review_traces"
        traces.mkdir()
        paper_statements = {
            "opaque_formula_declaration": "The displayed identity is x = y.",
            "paper_theorem": (
                "Theorem 1. The paper theorem reaches its stated conclusion."
            ),
            "unchecked_theorem": "Theorem 2 has not yet been checked.",
            "source_domain": "The source parameter is positive.",
        }
        lean_statements = {
            "opaque_formula_declaration": "theorem opaque_formula_declaration : x = y",
            "paper_theorem": "theorem paper_theorem : P",
            "unchecked_theorem": "theorem unchecked_theorem : Q",
            "source_domain": "abbrev source_domain : Prop := 0 < x",
        }
        translated_statements = {
            "opaque_formula_declaration": "x=y",
            "paper_theorem": "P",
            "unchecked_theorem": "Q",
            "source_domain": "0 < x",
        }
        signatures = {
            "opaque_formula_declaration": "1" * 64,
            "paper_theorem": "2" * 64,
            "unchecked_theorem": "3" * 64,
            "source_domain": "4" * 64,
        }
        (folder / "status.json").write_text(
            json.dumps(
                {
                    "review_surface": {
                        "include_names": [
                            "opaque_formula_declaration",
                            "paper_theorem",
                            "unchecked_theorem",
                        ],
                        "assumption_names": ["source_domain"],
                    },
                    "human_review": {"reviewed_rows": 0, "total_rows": 3},
                }
            ),
            encoding="utf-8",
        )
        (audit / "paper_statement_map.json").write_text(
            json.dumps(
                {
                    "source_artifact_path": "source.txt",
                    "source_coverage_mode": "deep_paper_with_all_prose_claims",
                    "items": {
                        "source_domain": {
                            "source_kind": "assumption",
                            "source_location": "source.txt:10-12",
                            "statement": "The source parameter is positive.",
                            "lean_declarations": ["source_domain"],
                        },
                        "displayed_identity": {
                            "source_kind": "formula",
                            "source_location": "source.txt:20-21",
                            "statement": "The displayed identity is x = y.",
                            "lean_declarations": ["opaque_formula_declaration"],
                        },
                        "main_result": {
                            "source_kind": "theorem",
                            "source_location": "source.txt:30-35",
                            "statement": "Theorem 1. The paper theorem reaches its stated conclusion.",
                            "source_anchor_evidence": [
                                {
                                    "path": "source.txt",
                                    "line_start": 30,
                                    "line_end": 35,
                                    "quoted_text": "Theorem 1. The paper theorem reaches its stated conclusion.",
                                    "quoted_text_sha256": "0" * 64,
                                }
                            ],
                            "lean_declarations": ["paper_theorem"],
                        },
                    },
                }
            ),
            encoding="utf-8",
        )
        (audit / "assumption_match_llm.json").write_text(
            json.dumps(
                {
                    "validator": "Semantic reviewer",
                    "validator_type": "agent_semantic_source_review",
                    "validated_at": "2026-07-31T12:00:00Z",
                    "items": {
                        "source_domain": {
                            "judgment": "paper_condition",
                            "lean_statement_sha256": REFRESH.statement_digest(
                                lean_statements["source_domain"]
                            ),
                            "paper_statement_sha256": REFRESH.statement_digest(
                                paper_statements["source_domain"]
                            ),
                            "reason": "This premise is stated in the source.",
                            "premise_judgments": {
                                "h : 0 < x": {"judgment": "paper_condition"}
                            },
                        }
                    },
                }
            ),
            encoding="utf-8",
        )
        (audit / "paper_coverage_llm.json").write_text(
            json.dumps(
                {
                    "validator": "Coverage reviewer",
                    "validator_type": "model",
                    "validated_at": "2026-07-31T12:00:00Z",
                    "items": {
                        "displayed_identity": {
                            "coverage": "covered",
                            "review_rows": ["opaque_formula_declaration"],
                            "reason": "Checked from /tmp/private-worktree/source.txt and [memo](../private/memo.md).",
                        },
                        "main_result": {
                            "coverage": "conditional_boundary",
                            "review_rows": ["paper_theorem"],
                            "reason": "The visible premise is recorded.",
                        },
                    },
                }
            ),
            encoding="utf-8",
        )
        (audit / "statement_match_llm.json").write_text(
            json.dumps(
                {
                    "validator": "Statement reviewer",
                    "validator_type": "agent",
                    "validated_at": "2026-07-31T12:00:00Z",
                    "items": {
                        "opaque_formula_declaration": {
                            "judgment": "matches",
                            "lean_signature_sha256": signatures[
                                "opaque_formula_declaration"
                            ],
                            "lean_statement_sha256": REFRESH.statement_digest(
                                lean_statements["opaque_formula_declaration"]
                            ),
                            "paper_statement_sha256": REFRESH.statement_digest(
                                paper_statements["opaque_formula_declaration"]
                            ),
                            "tex_statement_sha256": REFRESH.statement_digest(
                                translated_statements["opaque_formula_declaration"]
                            ),
                            "reason": "The formula is exact.",
                        },
                        "paper_theorem": {
                            "judgment": "mismatch",
                            "lean_signature_sha256": signatures["paper_theorem"],
                            "lean_statement_sha256": REFRESH.statement_digest(
                                lean_statements["paper_theorem"]
                            ),
                            "paper_statement_sha256": REFRESH.statement_digest(
                                paper_statements["paper_theorem"]
                            ),
                            "tex_statement_sha256": REFRESH.statement_digest(
                                translated_statements["paper_theorem"]
                            ),
                            "resolution": "conditional_boundary",
                            "reason": "A visible premise remains.",
                        },
                    },
                }
            ),
            encoding="utf-8",
        )
        (audit / "lean_to_tex_llm.json").write_text(
            json.dumps(
                {
                    "translator": "Translation reviewer",
                    "translator_type": "model",
                    "translated_at": "2026-07-31T12:00:00Z",
                    "items": {
                        "opaque_formula_declaration": {
                            "lean_statement_sha256": REFRESH.statement_digest(
                                lean_statements["opaque_formula_declaration"]
                            ),
                            "tex_statement": "x=y",
                        },
                        "paper_theorem": {
                            "lean_statement_sha256": REFRESH.statement_digest(
                                lean_statements["paper_theorem"]
                            ),
                            "tex_statement": "P",
                        },
                    },
                }
            ),
            encoding="utf-8",
        )
        (audit / "review_surface_llm.json").write_text(
            json.dumps(
                {
                    "judgment": "passes",
                    "review_rows": 3,
                    "validator": "Surface reviewer",
                    "validator_type": "agent",
                    "validated_at": "2026-07-31T12:00:00Z",
                }
            ),
            encoding="utf-8",
        )
        (traces / "paper_interface_cache.json").write_text(
            json.dumps(
                {
                    "rows": [
                        {
                            "name": name,
                            "lean_signature_sha256": signatures[name],
                            "lean_statement": lean_statements[name],
                            "interface_source": lean_statements[name],
                            "paper_statement": paper_statements[name],
                            "agent_statement": translated_statements[name],
                        }
                        for name in (
                            "opaque_formula_declaration",
                            "paper_theorem",
                            "unchecked_theorem",
                            "source_domain",
                        )
                    ]
                }
            ),
            encoding="utf-8",
        )
        return folder

    def saved_authorization(
        self,
        source_row: dict[str, object],
        *,
        coverage_total: int = 1,
        canonical_digest: str = "b" * 64,
    ) -> REFRESH.SavedSidecarReuseAuthorization:
        return REFRESH.SavedSidecarReuseAuthorization(
            True,
            statement_counts={
                "total": 3,
                "matches": 2,
                "mismatch": 0,
                "formalization_boundary": 1,
                "uncertain": 0,
                "unknown": 0,
                "source_condition_rows": 1,
            },
            coverage_counts={
                "total": coverage_total,
                "covered": 0,
                "corrected_target_covered": 0,
                "conditional_boundary": coverage_total,
                "support_only": 0,
                "out_of_scope": 0,
                "scope_exclusion": 0,
            },
            coverage_source_bindings=(
                {
                    "source_map_item_semantic_sha256": (
                        REFRESH.source_item_coverage_sha256(
                            source_row,
                            "named_theoretical_statements",
                        )
                    ),
                    "source_item_semantic_sha256": canonical_digest,
                },
            ),
            canonical_source_state="structural_checkout_immutable_attestation",
            receipt_schema=3,
            receipt_sha256="a" * 64,
        )

    def test_row_ledgers_use_semantic_metadata_and_do_not_infer_human_review(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            blocks = REFRESH.generated_section_blocks(folder)
            summary = REFRESH.sidecar_summary(folder)
            combined = "\n".join(blocks.values())

            self.assertIn("source condition", blocks[13])
            self.assertNotIn("paper_condition", combined)
            self.assertIn("The displayed identity is x = y.", blocks[14])
            self.assertIn("`opaque_formula_declaration`", blocks[14])
            self.assertIn("exact match", blocks[14])
            self.assertIn("does not match; formalization boundary", blocks[20])
            self.assertIn("No completed statement check recorded", blocks[20])
            self.assertIn("0/3 rows", blocks[20])
            self.assertIn("No human row-level approval is inferred", blocks[20])
            self.assertNotIn("Human review by", combined)
            self.assertNotIn("/tmp/private-worktree", combined)
            self.assertNotIn("](../private", combined)
            self.assertNotIn("conditional_boundary", combined)
            self.assertNotIn("agent_semantic_source_review", combined)
            self.assertIn(
                "independent freshness is not established by this report generator",
                summary["tex"],
            )
            self.assertIn(
                "independent freshness is not established by this report generator",
                summary["review"],
            )
            self.assertIn(
                "recorded translation metadata, whose independent freshness is "
                "not established by this report generator",
                blocks[20],
            )

    def test_named_theory_reports_exclude_unnamed_prose_and_formula_rows(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            source_map = folder / "audit" / "paper_statement_map.json"
            payload = json.loads(source_map.read_text(encoding="utf-8"))
            payload["source_coverage_mode"] = "named_theoretical_statements"
            payload["items"]["prose_observation"] = {
                "source_kind": "claim",
                "statement": "An unnumbered empirical observation.",
            }
            source_map.write_text(json.dumps(payload), encoding="utf-8")

            blocks = REFRESH.generated_section_blocks(folder)

            self.assertNotIn("The displayed identity is x = y.", blocks[14])
            self.assertNotIn("An unnumbered empirical observation.", blocks[21])
            self.assertIn(
                "The paper theorem reaches its stated conclusion.", blocks[21]
            )
            self.assertIn("named theoretical statements", blocks[21])
            self.assertNotIn("named_theoretical_statements", blocks[21])

    def test_formula_ledger_retains_explicit_supplemental_formula_without_promoting_coverage(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            source_map = folder / "audit" / "paper_statement_map.json"
            payload = json.loads(source_map.read_text(encoding="utf-8"))
            payload["source_coverage_mode"] = "named_theoretical_statements"
            payload["items"]["displayed_identity"].update(
                {
                    "claim_bearing": True,
                    "semantic_contract": {
                        "spec_declaration": "Fixture.opaque_formula_declarationSpec",
                        "evidence_declaration": "Fixture.opaque_formula_declaration",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                }
            )
            payload["items"]["ordinary_formula_context"] = {
                "source_kind": "formula",
                "statement": "A merely displayed supporting identity.",
                "claim_bearing": False,
            }
            source_map.write_text(json.dumps(payload), encoding="utf-8")

            blocks = REFRESH.generated_section_blocks(folder)

            self.assertIn("The displayed identity is x = y.", blocks[14])
            self.assertIn("selected supplemental formula/equation target", blocks[14])
            self.assertIn("Complete source-map `Spec`/evidence contract", blocks[14])
            self.assertNotIn("A merely displayed supporting identity.", blocks[14])
            self.assertNotIn("The displayed identity is x = y.", blocks[21])

    def test_formula_ledger_supplement_does_not_require_normal_coverage_reuse_binding(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            source_map = folder / "audit" / "paper_statement_map.json"
            payload = json.loads(source_map.read_text(encoding="utf-8"))
            payload["source_coverage_mode"] = "named_theoretical_statements"
            payload["items"]["displayed_identity"].update(
                {
                    "claim_bearing": True,
                    "semantic_contract": {
                        "spec_declaration": "Fixture.opaque_formula_declarationSpec",
                        "evidence_declaration": "Fixture.opaque_formula_declaration",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                }
            )
            source_map.write_text(json.dumps(payload), encoding="utf-8")

            evidence = REFRESH.canonical_sidecars(folder)
            statement_rows = REFRESH.keyed_items(evidence["statement"])
            surface = {
                "rows": [
                    {
                        "name": "opaque_formula_declaration",
                        "kind": "statement",
                        "cache_row": {},
                        "statement_row": statement_rows[
                            "opaque_formula_declaration"
                        ],
                    }
                ]
            }
            reuse = self.saved_authorization(payload["items"]["main_result"])

            block = REFRESH.formula_ledger(
                folder,
                {},
                evidence,
                reuse=reuse,
                semantic_surface=surface,
            )

            self.assertIn("The displayed identity is x = y.", block)
            self.assertIn("selected supplemental formula/equation target", block)

    def test_duplicate_semantic_receipts_fail_closed_without_name_fallback(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            statement_path = folder / "audit" / "statement_match_llm.json"
            payload = json.loads(statement_path.read_text(encoding="utf-8"))
            original = payload["items"].pop("opaque_formula_declaration")
            payload["items"]["prior_storage_name"] = original
            payload["items"]["duplicate_storage_name"] = dict(original)
            statement_path.write_text(json.dumps(payload), encoding="utf-8")

            block = REFRESH.generated_section_blocks(folder)[20]

            self.assertIn("No completed statement check recorded", block)
            self.assertNotIn("The formula is exact.", block)
            self.assertIn(
                "2 unconfigured, stale, or ambiguous statement-sidecar rows",
                block,
            )

    def test_receipt_bound_prose_ignores_forged_obligation_digest(self) -> None:
        approved = "The source theorem reaches its stated conclusion."
        approved_digest = REFRESH.statement_digest(approved)
        forged = "The source proves a much stronger conclusion."
        row = {
            "paper_statement_sha256": approved_digest,
            "source_obligations": [
                {
                    "statement": forged,
                    "source_statement_sha256": approved_digest,
                }
            ],
        }

        recovered = REFRESH.receipt_bound_paper_statement(
            row,
            {"source_map": None},
        )

        self.assertEqual(recovered, "")
        self.assertNotEqual(REFRESH.statement_digest(forged), approved_digest)

    def test_current_statement_binding_recovers_stale_cache_source_prose(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            cache_path = folder / ".review_traces" / "paper_interface_cache.json"
            cache = json.loads(cache_path.read_text(encoding="utf-8"))
            for row in cache["rows"]:
                if row["name"] == "paper_theorem":
                    row["paper_statement"] = "Stale cache prose."
            cache_path.write_text(json.dumps(cache), encoding="utf-8")

            surface = REFRESH.semantic_review_surface(
                folder,
                REFRESH.status_payload(folder),
                REFRESH.canonical_sidecars(folder),
            )
            selected = next(
                row for row in surface["rows"] if row["name"] == "paper_theorem"
            )

            self.assertIsNotNone(selected["statement_row"])
            self.assertEqual(
                selected["cache_row"]["paper_statement"],
                "Theorem 1. The paper theorem reaches its stated conclusion.",
            )

    def test_current_statement_binding_overlays_stale_cache_translation(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            cache_path = folder / ".review_traces" / "paper_interface_cache.json"
            cache = json.loads(cache_path.read_text(encoding="utf-8"))
            for row in cache["rows"]:
                if row["name"] == "paper_theorem":
                    row["agent_statement"] = "stale translation"
            cache_path.write_text(json.dumps(cache), encoding="utf-8")

            surface = REFRESH.semantic_review_surface(
                folder,
                REFRESH.status_payload(folder),
                REFRESH.canonical_sidecars(folder),
            )
            selected = next(
                row for row in surface["rows"] if row["name"] == "paper_theorem"
            )

            self.assertIsNotNone(selected["statement_row"])
            self.assertEqual(selected["cache_row"]["agent_statement"], "P")

    def test_formula_ledger_links_content_pinned_statement_when_tex_is_stale(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            source_map_path = folder / "audit" / "paper_statement_map.json"
            source_map = json.loads(source_map_path.read_text(encoding="utf-8"))
            source_map["source_coverage_mode"] = "named_theoretical_statements"
            source_map["items"]["displayed_identity"].update(
                {
                    "claim_bearing": True,
                    "semantic_contract": {
                        "spec_declaration": "Fixture.opaque_formula_declarationSpec",
                        "evidence_declaration": "Fixture.opaque_formula_declaration",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                }
            )
            source_map_path.write_text(json.dumps(source_map), encoding="utf-8")

            statement_path = folder / "audit" / "statement_match_llm.json"
            statement = json.loads(statement_path.read_text(encoding="utf-8"))
            statement["items"]["semantic_current_formula_receipt"] = statement[
                "items"
            ].pop("opaque_formula_declaration")
            statement_path.write_text(json.dumps(statement), encoding="utf-8")

            tex_path = folder / "audit" / "lean_to_tex_llm.json"
            tex = json.loads(tex_path.read_text(encoding="utf-8"))
            tex["items"]["opaque_formula_declaration"][
                "lean_statement_sha256"
            ] = REFRESH.statement_digest("stale Lean expression")
            tex_path.write_text(json.dumps(tex), encoding="utf-8")

            evidence = REFRESH.canonical_sidecars(folder)
            surface = REFRESH.semantic_review_surface(
                folder,
                REFRESH.status_payload(folder),
                evidence,
            )
            selected = next(
                row
                for row in surface["rows"]
                if row["name"] == "opaque_formula_declaration"
            )

            self.assertEqual(selected["statement_row"]["judgment"], "matches")
            self.assertIsNone(selected["tex_row"])
            ledger = REFRESH.formula_ledger(
                folder,
                REFRESH.status_payload(folder),
                evidence,
                reuse=REFRESH.SavedSidecarReuseAuthorization(False),
                semantic_surface=surface,
            )
            self.assertIn("The displayed identity is x = y.", ledger)
            self.assertIn("`opaque_formula_declaration`: exact match", ledger)
            self.assertNotIn(
                "`opaque_formula_declaration`: no completed statement check",
                ledger,
            )

    def test_statement_receipt_fallback_requires_current_cache_translation(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            tex_path = folder / "audit" / "lean_to_tex_llm.json"
            tex = json.loads(tex_path.read_text(encoding="utf-8"))
            tex["items"]["opaque_formula_declaration"][
                "lean_statement_sha256"
            ] = REFRESH.statement_digest("stale Lean expression")
            tex_path.write_text(json.dumps(tex), encoding="utf-8")

            cache_path = folder / ".review_traces" / "paper_interface_cache.json"
            cache = json.loads(cache_path.read_text(encoding="utf-8"))
            for row in cache["rows"]:
                if row["name"] == "opaque_formula_declaration":
                    row["agent_statement"] = "stale translation"
            cache_path.write_text(json.dumps(cache), encoding="utf-8")

            surface = REFRESH.semantic_review_surface(
                folder,
                REFRESH.status_payload(folder),
                REFRESH.canonical_sidecars(folder),
            )
            selected = next(
                row
                for row in surface["rows"]
                if row["name"] == "opaque_formula_declaration"
            )

            self.assertIsNone(selected["cache_row"])
            self.assertIsNone(selected["statement_row"])

    def test_empty_source_receipt_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            statement_path = folder / "audit" / "statement_match_llm.json"
            statement = json.loads(statement_path.read_text(encoding="utf-8"))
            statement["items"]["paper_theorem"]["paper_statement_sha256"] = (
                REFRESH.statement_digest("")
            )
            statement_path.write_text(json.dumps(statement), encoding="utf-8")
            cache_path = folder / ".review_traces" / "paper_interface_cache.json"
            cache = json.loads(cache_path.read_text(encoding="utf-8"))
            for row in cache["rows"]:
                if row["name"] == "paper_theorem":
                    row["paper_statement"] = ""
            cache_path.write_text(json.dumps(cache), encoding="utf-8")

            surface = REFRESH.semantic_review_surface(
                folder,
                REFRESH.status_payload(folder),
                REFRESH.canonical_sidecars(folder),
            )
            selected = next(
                row for row in surface["rows"] if row["name"] == "paper_theorem"
            )

            self.assertIsNone(selected["cache_row"])
            self.assertIsNone(selected["statement_row"])

    def test_duplicate_current_translation_receipts_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            tex_path = folder / "audit" / "lean_to_tex_llm.json"
            tex = json.loads(tex_path.read_text(encoding="utf-8"))
            tex["items"]["duplicate_translation_storage_key"] = dict(
                tex["items"]["paper_theorem"]
            )
            tex_path.write_text(json.dumps(tex), encoding="utf-8")

            surface = REFRESH.semantic_review_surface(
                folder,
                REFRESH.status_payload(folder),
                REFRESH.canonical_sidecars(folder),
            )
            selected = next(
                row for row in surface["rows"] if row["name"] == "paper_theorem"
            )

            self.assertIsNone(selected["cache_row"])
            self.assertIsNone(selected["statement_row"])
            self.assertIn(
                "duplicate_translation_storage_key", surface["orphan_tex_keys"]
            )

    def test_receipt_bound_prose_never_uses_generated_source_identifier(self) -> None:
        source_key = "blank_source_item"
        row = {
            "paper_statement_sha256": REFRESH.statement_digest(
                REFRESH.humanize_identifier(source_key)
            )
        }

        recovered = REFRESH.receipt_bound_paper_statement(
            row,
            {"source_map": {"items": {source_key: {}}}},
        )

        self.assertEqual(recovered, "")

    def test_configured_30_row_surface_excludes_65_statement_sidecar_orphans(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "PRPKGStyle"
            audit = folder / "audit"
            traces = folder / ".review_traces"
            audit.mkdir(parents=True)
            traces.mkdir()
            statement_names = [f"paper_row_{index}" for index in range(30)]
            condition_names = [f"source_condition_{index}" for index in range(19)]
            cache_rows: list[dict[str, str]] = []
            statement_items: dict[str, dict[str, str]] = {}
            assumption_items: dict[str, dict[str, str]] = {}
            tex_items: dict[str, dict[str, str]] = {}

            for index, name in enumerate(statement_names):
                lean_statement = f"theorem {name} : P{index}"
                paper_statement = f"Paper statement {index}."
                translated_statement = f"P_{{{index}}}"
                signature = REFRESH.statement_digest(f"signature:{name}")
                cache_rows.append(
                    {
                        "name": name,
                        "lean_signature_sha256": signature,
                        "lean_statement": lean_statement,
                        "interface_source": lean_statement,
                        "paper_statement": paper_statement,
                        "agent_statement": translated_statement,
                    }
                )
                statement_items[f"renamed-active-receipt-{index}"] = {
                    "judgment": "matches",
                    "lean_signature_sha256": signature,
                    "lean_statement_sha256": REFRESH.statement_digest(lean_statement),
                    "paper_statement_sha256": REFRESH.statement_digest(paper_statement),
                    "tex_statement_sha256": REFRESH.statement_digest(
                        translated_statement
                    ),
                }
                tex_items[f"renamed-translation-{index}"] = {
                    "lean_statement_sha256": REFRESH.statement_digest(lean_statement),
                    "tex_statement": translated_statement,
                }

            for index, name in enumerate(condition_names):
                lean_statement = f"abbrev {name} : Prop := C{index}"
                paper_statement = f"Source condition {index}."
                cache_rows.append(
                    {
                        "name": name,
                        "lean_signature_sha256": REFRESH.statement_digest(
                            f"signature:{name}"
                        ),
                        "lean_statement": lean_statement,
                        "interface_source": lean_statement,
                        "paper_statement": paper_statement,
                        "agent_statement": f"C_{{{index}}}",
                    }
                )
                assumption_items[f"renamed-condition-receipt-{index}"] = {
                    "judgment": "paper_condition",
                    "lean_statement_sha256": REFRESH.statement_digest(lean_statement),
                    "paper_statement_sha256": REFRESH.statement_digest(paper_statement),
                }

            for index in range(65):
                statement_items[f"orphan-stale-row-{index}"] = {
                    "judgment": "matches",
                    "lean_signature_sha256": REFRESH.statement_digest(
                        f"orphan-signature:{index}"
                    ),
                    "lean_statement_sha256": REFRESH.statement_digest(
                        f"orphan Lean statement {index}"
                    ),
                    "paper_statement_sha256": REFRESH.statement_digest(
                        f"orphan paper statement {index}"
                    ),
                    "tex_statement_sha256": REFRESH.statement_digest(
                        f"orphan translated statement {index}"
                    ),
                }

            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": statement_names,
                            "assumption_names": condition_names,
                        },
                        "human_review": {"reviewed_rows": 0, "total_rows": 49},
                    }
                ),
                encoding="utf-8",
            )
            (traces / "paper_interface_cache.json").write_text(
                json.dumps({"rows": cache_rows}),
                encoding="utf-8",
            )
            for filename, payload in (
                (
                    "statement_match_llm.json",
                    {"validator": "statement reviewer", "items": statement_items},
                ),
                (
                    "assumption_match_llm.json",
                    {"validator": "condition reviewer", "items": assumption_items},
                ),
                (
                    "lean_to_tex_llm.json",
                    {"translator": "translation reviewer", "items": tex_items},
                ),
            ):
                (audit / filename).write_text(json.dumps(payload), encoding="utf-8")

            summary = REFRESH.sidecar_summary(folder)
            block = REFRESH.generated_section_blocks(folder)[20]

            self.assertIn("30 exact match", summary["statement"])
            self.assertIn("19 source condition", summary["statement"])
            self.assertIn(
                "65 orphan/stale statement-sidecar rows excluded",
                summary["statement"],
            )
            self.assertNotIn("95 exact match", summary["statement"])
            self.assertIn("`paper_row_0`", block)
            self.assertIn("`source_condition_18`", block)
            self.assertNotIn("orphan-stale-row-0", block)
            self.assertNotIn("renamed-active-receipt-0", block)

    def test_assumption_ledger_excludes_unconfigured_semantic_receipts(self) -> None:
        cases = (
            ("LBG24Style", True, 4, 4),
            ("MSVVStyle", True, 4, 4),
            ("LG21Style", False, 6, 7),
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            for paper, keeps_condition, added_rows, expected_orphans in cases:
                with self.subTest(paper=paper):
                    folder = self.make_fixture(root / paper)
                    status_path = folder / "status.json"
                    status = json.loads(status_path.read_text(encoding="utf-8"))
                    if not keeps_condition:
                        status["review_surface"]["assumption_names"] = []
                        status_path.write_text(json.dumps(status), encoding="utf-8")

                    assumption_path = folder / "audit" / "assumption_match_llm.json"
                    assumption = json.loads(assumption_path.read_text(encoding="utf-8"))
                    for index in range(added_rows):
                        assumption["items"][f"diagnostic_only_{index}"] = {
                            "judgment": "paper_condition",
                            "lean_statement_sha256": REFRESH.statement_digest(
                                f"stale Lean condition {paper} {index}"
                            ),
                            "paper_statement_sha256": REFRESH.statement_digest(
                                f"stale paper condition {paper} {index}"
                            ),
                            "reason": "UNCONFIGURED PROVENANCE SENTINEL",
                        }
                    assumption_path.write_text(
                        json.dumps(assumption),
                        encoding="utf-8",
                    )

                    block = REFRESH.generated_section_blocks(folder)[13]
                    summary = REFRESH.sidecar_summary(folder)["assumption"]

                    self.assertNotIn("UNCONFIGURED PROVENANCE SENTINEL", block)
                    self.assertIn(
                        f"{expected_orphans} unconfigured, stale, or ambiguous "
                        "source-condition sidecar rows",
                        block,
                    )
                    if keeps_condition:
                        self.assertIn("The source parameter is positive.", block)
                        self.assertIn(
                            "assumption provenance has 1 source condition", summary
                        )
                        self.assertNotIn("5 source condition", summary)
                    else:
                        self.assertNotIn("`source_domain`", block)
                        self.assertIn(
                            "no configured source-condition rows",
                            summary,
                        )

    def test_legacy_source_scope_renders_full_inventory_with_migration_diagnostic(
        self,
    ) -> None:
        cases = (
            ("DGD65Style", 65),
            ("EOS24Style", 24),
            ("GS6219Style", 19),
            ("Roth34Style", 34),
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            for paper, row_count in cases:
                with self.subTest(paper=paper):
                    folder = self.make_fixture(root / paper)
                    source_map_path = folder / "audit" / "paper_statement_map.json"
                    coverage_path = folder / "audit" / "paper_coverage_llm.json"
                    source_map = json.loads(source_map_path.read_text(encoding="utf-8"))
                    source_map.pop("source_coverage_mode")
                    source_map["items"] = {
                        f"legacy_claim_{index}": {
                            "source_kind": "claim",
                            "statement": f"Every legacy item satisfies property {index}.",
                        }
                        for index in range(row_count)
                    }
                    coverage = {
                        "validator": "Coverage reviewer",
                        "validator_type": "model",
                        "items": {
                            item_id: {"coverage": "covered", "review_rows": []}
                            for item_id in source_map["items"]
                        },
                    }
                    source_map_path.write_text(
                        json.dumps(source_map),
                        encoding="utf-8",
                    )
                    coverage_path.write_text(
                        json.dumps(coverage),
                        encoding="utf-8",
                    )

                    block = REFRESH.generated_section_blocks(folder)[21]
                    summary = REFRESH.sidecar_summary(folder)["coverage"]

                    self.assertIn(
                        f"Source inventory: {row_count} source statements",
                        block,
                    )
                    self.assertIn(f"Coverage result: {row_count} covered", block)
                    self.assertIn("full inventory shown because scope metadata", block)
                    self.assertIn(f"source coverage has {row_count} covered", summary)
                    self.assertNotIn("Source inventory: 0 source statements", block)

    def test_immutable_saved_receipt_authorizes_legacy_named_scope_aggregates(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            source_map_path = folder / "audit" / "paper_statement_map.json"
            source_map = json.loads(source_map_path.read_text(encoding="utf-8"))
            source_map.pop("source_coverage_mode")
            source_map_path.write_text(json.dumps(source_map), encoding="utf-8")
            statement_path = folder / "audit" / "statement_match_llm.json"
            statement = json.loads(statement_path.read_text(encoding="utf-8"))
            statement["items"]["unchecked_theorem"] = {
                "judgment": "matches",
                "lean_signature_sha256": "3" * 64,
                "lean_statement_sha256": REFRESH.statement_digest(
                    "theorem unchecked_theorem : Q"
                ),
                "paper_statement_sha256": REFRESH.statement_digest(
                    "Theorem 2 has not yet been checked."
                ),
                "tex_statement_sha256": REFRESH.statement_digest("Q"),
                "reason": "The theorem statement is exact.",
            }
            statement_path.write_text(json.dumps(statement), encoding="utf-8")
            (folder / ".review_traces" / "paper_interface_cache.json").unlink()
            raw_source_digest = REFRESH.source_item_coverage_sha256(
                source_map["items"]["main_result"],
                "named_theoretical_statements",
            )
            receipt_sha256 = "a" * 64
            authorization = REFRESH.SavedSidecarReuseAuthorization(
                True,
                statement_counts={
                    "total": 3,
                    "matches": 2,
                    "mismatch": 0,
                    "formalization_boundary": 1,
                    "uncertain": 0,
                    "unknown": 0,
                    "source_condition_rows": 1,
                },
                coverage_counts={
                    "total": 1,
                    "covered": 0,
                    "corrected_target_covered": 0,
                    "conditional_boundary": 1,
                    "support_only": 0,
                    "out_of_scope": 0,
                    "scope_exclusion": 0,
                },
                coverage_source_bindings=(
                    {
                        "source_map_item_semantic_sha256": raw_source_digest,
                        "source_item_semantic_sha256": "b" * 64,
                    },
                ),
                canonical_source_state=("structural_checkout_immutable_attestation"),
                receipt_schema=3,
                receipt_sha256=receipt_sha256,
            )

            with mock.patch.object(
                REFRESH,
                "saved_report_reuse_authorization",
                return_value=authorization,
            ):
                summary = REFRESH.sidecar_summary(folder)
                blocks = REFRESH.generated_section_blocks(folder)

            self.assertIn("2 exact matches", summary["statement"])
            self.assertIn("1 formalization boundary", summary["statement"])
            self.assertIn("1 configured source condition", summary["statement"])
            self.assertIn("1 conditional boundary", summary["coverage"])
            self.assertIn(
                "independent freshness is not established by the saved semantic receipt",
                summary["review"],
            )
            self.assertIn(
                "independent freshness is not established",
                summary["tex"],
            )
            for rendered in (
                summary["statement"],
                summary["coverage"],
                blocks[20],
                blocks[21],
            ):
                self.assertIn("saved semantic receipt schema 3", rendered)
                self.assertIn(receipt_sha256, rendered)
                self.assertIn("immutable private issuance attestation", rendered)
            self.assertIn(
                "does not relabel a legacy row as a newly executed check",
                blocks[20],
            )
            self.assertIn(
                "does not relabel a legacy row as a newly executed check",
                blocks[21],
            )
            self.assertNotIn("full inventory shown because scope metadata", blocks[21])
            self.assertIn("Source inventory: 1 source statement", blocks[21])
            self.assertIn(
                "The paper theorem reaches its stated conclusion.",
                blocks[21],
            )
            self.assertIn(
                "The paper theorem reaches its stated conclusion.",
                blocks[20],
            )
            self.assertIn(
                "does not match; formalization boundary",
                blocks[20],
            )
            self.assertIn(
                "recorded translation metadata, whose independent freshness is "
                "not established by the saved semantic receipt",
                blocks[20],
            )
            self.assertNotIn("The displayed identity is x = y.", blocks[21])

    def test_saved_statement_navigation_rekey_is_semantically_authorized(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            source_map_path = folder / "audit" / "paper_statement_map.json"
            source_map = json.loads(source_map_path.read_text(encoding="utf-8"))
            source_map["source_coverage_mode"] = "named_theoretical_statements"
            source_map_path.write_text(json.dumps(source_map), encoding="utf-8")
            status_path = folder / "status.json"
            status = json.loads(status_path.read_text(encoding="utf-8"))
            include_names = status["review_surface"]["include_names"]
            include_names[include_names.index("paper_theorem")] = "renamed_navigation"
            status_path.write_text(json.dumps(status), encoding="utf-8")
            statement_path = folder / "audit" / "statement_match_llm.json"
            statement = json.loads(statement_path.read_text(encoding="utf-8"))
            statement["items"]["renamed_navigation"] = statement["items"].pop(
                "paper_theorem"
            )
            statement["items"]["unchecked_theorem"] = {
                "judgment": "matches",
                "lean_signature_sha256": "3" * 64,
                "lean_statement_sha256": REFRESH.statement_digest(
                    "theorem unchecked_theorem : Q"
                ),
                "paper_statement_sha256": REFRESH.statement_digest(
                    "Theorem 2 has not yet been checked."
                ),
                "tex_statement_sha256": REFRESH.statement_digest("Q"),
                "reason": "The theorem statement is exact.",
            }
            statement_path.write_text(json.dumps(statement), encoding="utf-8")
            coverage_path = folder / "audit" / "paper_coverage_llm.json"
            coverage = json.loads(coverage_path.read_text(encoding="utf-8"))
            coverage["items"]["main_result"]["review_rows"] = ["renamed_navigation"]
            coverage_path.write_text(json.dumps(coverage), encoding="utf-8")
            (folder / ".review_traces" / "paper_interface_cache.json").unlink()
            authorization = self.saved_authorization(source_map["items"]["main_result"])

            with mock.patch.object(
                REFRESH,
                "saved_report_reuse_authorization",
                return_value=authorization,
            ):
                block = REFRESH.generated_section_blocks(folder)[20]

            self.assertIn(
                "The paper theorem reaches its stated conclusion.",
                block,
            )
            self.assertIn("does not match; formalization boundary", block)
            self.assertIn("`renamed_navigation`", block)

    def test_saved_coverage_row_rekey_is_resolved_by_semantic_digest(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            source_map_path = folder / "audit" / "paper_statement_map.json"
            source_map = json.loads(source_map_path.read_text(encoding="utf-8"))
            source_map["source_coverage_mode"] = "named_theoretical_statements"
            source_row = source_map["items"].pop("main_result")
            source_map["items"]["renamed_source_navigation"] = source_row
            source_map_path.write_text(json.dumps(source_map), encoding="utf-8")

            canonical_digest = "c" * 64
            coverage_path = folder / "audit" / "paper_coverage_llm.json"
            coverage = json.loads(coverage_path.read_text(encoding="utf-8"))
            coverage["items"]["main_result"].update(
                {
                    "source_item_coverage_digest_schema": (
                        REFRESH.SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
                    ),
                    "source_item_coverage_sha256": canonical_digest,
                }
            )
            coverage_path.write_text(json.dumps(coverage), encoding="utf-8")
            authorization = self.saved_authorization(
                source_row,
                canonical_digest=canonical_digest,
            )

            with mock.patch.object(
                REFRESH,
                "saved_report_reuse_authorization",
                return_value=authorization,
            ):
                block = REFRESH.generated_section_blocks(folder)[21]

            self.assertIn(
                "The paper theorem reaches its stated conclusion.",
                block,
            )
            self.assertNotIn("No completed coverage check recorded", block)

    def test_saved_receipt_rejects_source_table_count_divergence(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            source_map_path = folder / "audit" / "paper_statement_map.json"
            source_map = json.loads(source_map_path.read_text(encoding="utf-8"))
            source_map["source_coverage_mode"] = "named_theoretical_statements"
            source_map_path.write_text(json.dumps(source_map), encoding="utf-8")
            authorization = self.saved_authorization(
                source_map["items"]["main_result"],
                coverage_total=2,
            )

            with (
                mock.patch.object(
                    REFRESH,
                    "saved_report_reuse_authorization",
                    return_value=authorization,
                ),
                self.assertRaisesRegex(
                    ValueError,
                    "binding count disagrees with coverage total",
                ),
            ):
                REFRESH.generated_section_blocks(folder)

    def test_saved_receipt_does_not_publish_contradictory_human_counts(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            status_path = folder / "status.json"
            status = json.loads(status_path.read_text(encoding="utf-8"))
            status["human_review"] = {"reviewed_rows": 99, "total_rows": 99}
            status_path.write_text(json.dumps(status), encoding="utf-8")
            source_map = json.loads(
                (folder / "audit" / "paper_statement_map.json").read_text(
                    encoding="utf-8"
                )
            )
            source_map["source_coverage_mode"] = "named_theoretical_statements"
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps(source_map),
                encoding="utf-8",
            )
            authorization = self.saved_authorization(source_map["items"]["main_result"])

            with mock.patch.object(
                REFRESH,
                "saved_report_reuse_authorization",
                return_value=authorization,
            ):
                block = REFRESH.generated_section_blocks(folder)[20]

            self.assertIn(
                "human dashboard review counts are invalid",
                block,
            )
            self.assertIn("no human approval is inferred", block)
            self.assertNotIn("99/99", block)

    def test_named_scope_includes_byte_pinned_source_index_additions(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            source_map_path = folder / "audit" / "paper_statement_map.json"
            source_map = json.loads(source_map_path.read_text(encoding="utf-8"))
            source_map["source_coverage_mode"] = "named_theoretical_statements"
            source_map_path.write_text(json.dumps(source_map), encoding="utf-8")

            with mock.patch.object(
                REFRESH,
                "source_index_byte_pinned_anchor_item_ids",
                return_value={"displayed_identity"},
            ):
                blocks = REFRESH.generated_section_blocks(folder)

            self.assertIn("Source inventory: 2 source statements", blocks[21])
            self.assertIn("The displayed identity is x = y.", blocks[21])
            self.assertIn("The displayed identity is x = y.", blocks[14])

    def test_source_coverage_links_only_configured_semantic_rows(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            statement_path = folder / "audit" / "statement_match_llm.json"
            statement = json.loads(statement_path.read_text(encoding="utf-8"))
            statement["items"]["raw_auxiliary_link"] = {
                "judgment": "matches",
                "lean_signature_sha256": REFRESH.statement_digest("aux signature"),
                "lean_statement_sha256": REFRESH.statement_digest("aux Lean"),
                "paper_statement_sha256": REFRESH.statement_digest("aux paper"),
                "tex_statement_sha256": REFRESH.statement_digest("aux tex"),
            }
            statement_path.write_text(json.dumps(statement), encoding="utf-8")
            coverage_path = folder / "audit" / "paper_coverage_llm.json"
            coverage = json.loads(coverage_path.read_text(encoding="utf-8"))
            coverage["items"]["main_result"]["review_rows"].append("raw_auxiliary_link")
            coverage_path.write_text(json.dumps(coverage), encoding="utf-8")

            block = REFRESH.generated_section_blocks(folder)[21]

            self.assertNotIn("raw_auxiliary_link", block)
            self.assertIn(
                "1 recorded declaration reference was outside the configured "
                "paper-facing surface",
                block,
            )

    def test_section_replacement_preserves_prose_removes_legacy_table_and_is_idempotent(
        self,
    ) -> None:
        report = (
            "## 13. Paper Assumption Provenance\n\n"
            "Researcher interpretation remains.\n\n"
            "| Old | Table |\n| --- | --- |\n| stale | row |\n\n"
            "## 14. Displayed Formula Provenance\n"
        )
        path = ROOT / "papers" / "EX24Example" / "FINAL_VALIDATION_REPORT.md"
        updated = REFRESH.replace_section_ledger(report, 13, "new table", path)
        repeated = REFRESH.replace_section_ledger(updated, 13, "new table", path)

        self.assertEqual(updated, repeated)
        self.assertIn("Researcher interpretation remains.", updated)
        self.assertNotIn("| Old | Table |", updated)
        self.assertEqual(updated.count(REFRESH.SECTION_BLOCKS[13][1]), 1)

    def test_render_report_is_pure(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            report = folder / REFRESH.REPORT
            report.write_text(self.legacy_report_template(), encoding="utf-8")
            before = report.read_text(encoding="utf-8")

            rendered = REFRESH.render_report(report)

            self.assertEqual(report.read_text(encoding="utf-8"), before)
            self.assertNotEqual(rendered, before)
            self.assertIn(REFRESH.SECTION_BLOCKS[21][1], rendered)

    def test_prepared_report_rejects_input_mutation_before_write(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            report = folder / REFRESH.REPORT
            report.write_text(
                self.legacy_report_template(),
                encoding="utf-8",
            )
            prepared = REFRESH.prepare_report(report)
            coverage_path = folder / "audit" / "paper_coverage_llm.json"
            coverage = json.loads(coverage_path.read_text(encoding="utf-8"))
            coverage["unreviewed_mutation"] = True
            coverage_path.write_text(json.dumps(coverage), encoding="utf-8")

            with self.assertRaisesRegex(ValueError, "inputs changed during rendering"):
                REFRESH.validate_prepared_report(
                    prepared,
                    closure_provider=object(),
                )

    def test_prepared_report_reauthorizes_with_supplied_fresh_provider(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            report = folder / REFRESH.REPORT
            report.write_text(
                self.legacy_report_template(),
                encoding="utf-8",
            )
            source_map_path = folder / "audit" / "paper_statement_map.json"
            source_map = json.loads(source_map_path.read_text(encoding="utf-8"))
            source_map["source_coverage_mode"] = "named_theoretical_statements"
            source_map_path.write_text(json.dumps(source_map), encoding="utf-8")
            authorization = self.saved_authorization(source_map["items"]["main_result"])
            changed_authorization = REFRESH.SavedSidecarReuseAuthorization(
                **{
                    **authorization.__dict__,
                    "receipt_sha256": "d" * 64,
                }
            )

            with mock.patch.object(
                REFRESH,
                "saved_report_reuse_authorization",
                return_value=authorization,
            ):
                prepared = REFRESH.prepare_report(report)
            fresh_provider = object()
            with (
                mock.patch.object(
                    REFRESH,
                    "saved_sidecar_reuse_authorization",
                    return_value=changed_authorization,
                ) as reauthorize,
                self.assertRaisesRegex(
                    ValueError,
                    "saved semantic authority changed during rendering",
                ),
            ):
                REFRESH.validate_prepared_report(
                    prepared,
                    closure_provider=fresh_provider,
                )

            self.assertIs(
                reauthorize.call_args.kwargs["closure_provider"],
                fresh_provider,
            )

    def test_prepared_report_rejects_sidecar_mutation_during_reauthorization(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = self.make_fixture(Path(temp_dir))
            report = folder / REFRESH.REPORT
            report.write_text(
                self.legacy_report_template(),
                encoding="utf-8",
            )
            prepared = REFRESH.prepare_report(report)
            coverage_path = folder / "audit" / "paper_coverage_llm.json"

            def mutate_and_reauthorize(*_args: object, **_kwargs: object):
                coverage = json.loads(coverage_path.read_text(encoding="utf-8"))
                coverage["items"]["main_result"]["reason"] = (
                    "Reason text mutated during authorization."
                )
                coverage_path.write_text(json.dumps(coverage), encoding="utf-8")
                return prepared.reuse

            with (
                mock.patch.object(
                    REFRESH,
                    "saved_sidecar_reuse_authorization",
                    side_effect=mutate_and_reauthorize,
                ),
                self.assertRaisesRegex(
                    ValueError,
                    "inputs changed during final authorization",
                ),
            ):
                REFRESH.validate_prepared_report(
                    prepared,
                    closure_provider=object(),
                )


if __name__ == "__main__":
    unittest.main()
