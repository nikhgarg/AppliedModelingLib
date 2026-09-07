"""Reader coverage must fail closed without becoming mathematical evidence."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.final_validation_report_sections import section_four_result_table
from scripts.report_memo_coverage import (
    COVERAGE_PATH,
    _automatic_printed_label,
    _heading_anchor,
    _portable_source_inventory_errors,
    _required_result_explanation_keys,
    coverage_template,
    memo_content_sha256,
    report_content_sha256,
    report_memo_coverage_errors,
)
from scripts.source_named_result_index import (
    named_result_presentations_sha256,
    reviewed_source_presentation_inventory,
)


class ReportMemoCoverageTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.folder = Path(self.temp.name) / "Fixture"
        (self.folder / "docs").mkdir(parents=True)
        (self.folder / "audit").mkdir()
        self.report = self.folder / "FINAL_VALIDATION_REPORT.md"
        self.report.write_text(
            "## 4. Result Comparison\n\n"
            "| Result | Comparison with source |\n"
            "| --- | --- |\n"
            "| Model clarification | Positive-mass endpoint. "
            "[Explanation](./docs/SOURCE_CLARIFICATIONS.md#positive-mass). |\n\n"
            "## 10. Source Clarifications\nThe endpoint uses positive mass.\n\n"
            "[Explanation](./docs/SOURCE_CLARIFICATIONS.md#positive-mass)\n\n"
            "## 11. Paper Issues or Caveats\nNone.\n"
        )
        self.memo = self.folder / "docs/SOURCE_CLARIFICATIONS.md"
        self.memo.write_text(
            "# Source clarifications\n\n## Positive mass\n"
            "The conditional expectation in Lemma 1 concerns a positive-mass event.\n"
        )
        self.fidelity = self.folder / "audit/source_proof_fidelity.json"
        self.fidelity.write_text(json.dumps({
            "defects": [{"id": "mass", "source_claim": "The conditional mean exists."}],
            "model_conventions": [{"id": "encoding", "formal_meaning": "Order is represented by ranks."}],
        }))
        self.assessment = coverage_template(self.folder)
        self.assessment["all_selected_semantic_review_sha256"] = "a" * 64
        self.assessment["report_inventory_complete"] = True
        self.assessment["items"] = {
            "defect/mass": {"disposition": "memo", "memo": "docs/SOURCE_CLARIFICATIONS.md", "memo_heading": "Positive mass", "memo_anchor": "positive-mass", "memo_sha256": memo_content_sha256(self.memo)},
            "convention/encoding": {"disposition": "not_material", "reason": "The rank encoding preserves the source order and adds no premise."},
        }
        self.assessment["result_table"]["complete"] = True
        for row in self.assessment["result_table"]["rows"].values():
            row["explanation_keys"] = ["defect/mass"]
            row["supplemental_reason"] = "This row records a model-level clarification."
        self.save()

    def save(self) -> None:
        (self.folder / COVERAGE_PATH).write_text(json.dumps(self.assessment))

    @staticmethod
    def anchor(path: str, line: int, quote: str) -> dict:
        return {
            "path": path,
            "line_start": line,
            "line_end": line,
            "quoted_text": quote,
            "quoted_text_sha256": hashlib.sha256(quote.encode()).hexdigest(),
        }

    def install_text_source_results(self) -> None:
        source_text = (
            "Theorem 1. A stable allocation exists.\n"
            "Lemma 2. The stable allocation is unique.\n"
        )
        source = self.folder / "source.txt"
        source.write_text(source_text)
        presentations = reviewed_source_presentation_inventory(
            source_text, source_path="source.txt", source_format="text"
        ).classified
        source_sha256 = hashlib.sha256(source_text.encode()).hexdigest()
        source_map = {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_sha256,
            "source_coverage_mode": "named_theoretical_statements",
            "source_named_result_inventory_review": {
                "complete": True,
                "source_artifact_sha256": source_sha256,
                "discovered_named_result_sha256": named_result_presentations_sha256(
                    presentations
                ),
            },
            "items": {
                "theorem1": {
                    "source_kind": "theorem",
                    "source_defect_ids": ["mass"],
                    "source_anchor_evidence": [
                        self.anchor("source.txt", 1, source_text.splitlines()[0])
                    ],
                },
                "lemma2": {
                    "source_kind": "lemma",
                    "source_anchor_evidence": [
                        self.anchor("source.txt", 2, source_text.splitlines()[1])
                    ],
                },
            },
        }
        (self.folder / "audit/paper_statement_map.json").write_text(
            json.dumps(source_map)
        )
        self.report.write_text(
            "## 4. Result Comparison\n\n"
            "| Result | Comparison with source |\n"
            "| --- | --- |\n"
            "| Theorems 1–2 | The conclusions are checked. "
            "[Explanation](docs/SOURCE_CLARIFICATIONS.md#positive-mass). |\n\n"
            "## 10. Source Clarifications\nThe endpoint uses positive mass.\n\n"
            "[Explanation](docs/SOURCE_CLARIFICATIONS.md#positive-mass)\n\n"
            "## 11. Paper Issues or Caveats\nNone.\n"
        )
        self.assessment = coverage_template(self.folder)
        self.assessment["all_selected_semantic_review_sha256"] = "a" * 64
        self.assessment["report_inventory_complete"] = True
        self.assessment["items"] = {
            "defect/mass": {
                "disposition": "memo",
                "memo": "docs/SOURCE_CLARIFICATIONS.md",
                "memo_heading": "Positive mass",
                "memo_anchor": "positive-mass",
                "memo_sha256": memo_content_sha256(self.memo),
            },
            "convention/encoding": {
                "disposition": "not_material",
                "reason": "The encoding changes no premise.",
            },
        }
        table = self.assessment["result_table"]
        table["complete"] = True
        row_id = next(iter(table["rows"]))
        table["rows"][row_id]["explanation_keys"] = ["defect/mass"]
        for result in table["results"].values():
            result["row_mappings"] = [
                {"report_label": "Theorems 1–2", "row_sha256": row_id}
            ]
            result["grouping_reason"] = "The row groups the theorem and its supporting lemma."
        self.save()

    def test_reviewed_linked_explanation_passes_without_writes(self) -> None:
        before = {p: p.read_bytes() for p in self.folder.rglob("*") if p.is_file()}
        self.assertEqual(report_memo_coverage_errors(self.folder), ())
        self.assertEqual(before, {p: p.read_bytes() for p in before})

    def test_terminal_semantic_basis_stales_without_reclassifying_reader_prose(self) -> None:
        self.assertEqual(report_memo_coverage_errors(self.folder), ())
        self.assertEqual(
            report_memo_coverage_errors(
                self.folder,
                expected_all_selected_semantic_review_sha256="a" * 64,
            ),
            (),
        )
        errors = report_memo_coverage_errors(
            self.folder,
            expected_all_selected_semantic_review_sha256="b" * 64,
        )
        self.assertTrue(any("current all-selected semantic review" in e for e in errors))
        missing = report_memo_coverage_errors(
            self.folder,
            expected_all_selected_semantic_review_sha256="",
        )
        self.assertTrue(any("was not supplied by the terminal" in e for e in missing))

    def test_prose_repair_keeps_the_same_current_semantic_basis(self) -> None:
        self.report.write_text(
            self.report.read_text().replace(
                "The endpoint uses positive mass.",
                "The endpoint uses the source positive-mass reading.",
            )
        )
        self.assessment["report_sha256"] = report_content_sha256(
            self.report.read_text()
        )
        self.save()
        self.assertEqual(
            report_memo_coverage_errors(
                self.folder,
                expected_all_selected_semantic_review_sha256="a" * 64,
            ),
            (),
        )

    def test_template_has_no_semantic_authority(self) -> None:
        template = coverage_template(self.folder)
        self.assertEqual(template["all_selected_semantic_review_sha256"], "")

    def test_template_is_not_acceptance(self) -> None:
        self.assessment = coverage_template(self.folder)
        self.assessment["all_selected_semantic_review_sha256"] = "a" * 64
        self.save()
        errors = report_memo_coverage_errors(self.folder)
        self.assertTrue(any("not been reviewed" in e for e in errors))
        self.assertTrue(any("needs a reviewed memo" in e for e in errors))

    def test_missing_or_malformed_assessment_fails(self) -> None:
        path = self.folder / COVERAGE_PATH
        path.unlink()
        self.assertTrue(report_memo_coverage_errors(self.folder))
        path.write_text("[]")
        self.assertIn("expected a JSON object", report_memo_coverage_errors(self.folder)[0])

    def test_duplicate_json_fields_cannot_replace_an_unreviewed_disposition(self) -> None:
        path = self.folder / COVERAGE_PATH
        text = path.read_text().replace(
            '"report_inventory_complete": true',
            '"report_inventory_complete": false, "report_inventory_complete": true',
        )
        path.write_text(text)
        self.assertIn("duplicate JSON field", report_memo_coverage_errors(self.folder)[0])

    def test_uncovered_and_unknown_records_fail(self) -> None:
        del self.assessment["items"]["defect/mass"]
        self.assessment["items"]["defect/unknown"] = {"disposition": "not_material", "reason": "Unknown."}
        self.save()
        errors = report_memo_coverage_errors(self.folder)
        self.assertTrue(any("no coverage assessment: defect/mass" in e for e in errors))
        self.assertTrue(any("unknown source clarification" in e for e in errors))

    def test_nonmaterial_disposition_requires_reason(self) -> None:
        self.assessment["items"]["convention/encoding"].pop("reason")
        self.save()
        self.assertTrue(any("mathematical reason" in e for e in report_memo_coverage_errors(self.folder)))

    def test_misspelled_assessment_fields_do_not_silently_disable_checks(self) -> None:
        row = self.assessment["items"]["defect/mass"]
        row["memo_headding"] = row.pop("memo_heading")
        self.assessment["report_inventory_completee"] = True
        self.save()
        errors = report_memo_coverage_errors(self.folder)
        self.assertTrue(any("assessment fields" in e for e in errors))
        self.assertTrue(any("coverage item fields" in e for e in errors))

    def test_new_source_finding_requires_assessment(self) -> None:
        data = json.loads(self.fidelity.read_text())
        data["defects"].append({"id": "strictness", "source_claim": "The inequality is strict."})
        self.fidelity.write_text(json.dumps(data))
        errors = report_memo_coverage_errors(self.folder)
        self.assertTrue(any("defect/strictness" in e for e in errors))
        self.assertTrue(any("current source records" in e for e in errors))

    def test_changed_source_meaning_requires_document_reassessment(self) -> None:
        data = json.loads(self.fidelity.read_text())
        data["defects"][0]["source_claim"] = "A pointwise conditional mean exists on null events."
        self.fidelity.write_text(json.dumps(data))
        self.assertTrue(any("current source records" in e for e in report_memo_coverage_errors(self.folder)))

    def test_reader_change_stales_coverage_but_hidden_metadata_does_not(self) -> None:
        original = self.report.read_text()
        self.report.write_text(original + "<!-- generated date changed -->\n## 12. Validation\nnew technical log\n")
        self.assertEqual(report_content_sha256(original), report_content_sha256(self.report.read_text()))
        self.assertEqual(report_memo_coverage_errors(self.folder), ())
        self.report.write_text(original.replace("positive mass", "positive atomless mass"))
        self.assertTrue(any("reader-facing report" in e for e in report_memo_coverage_errors(self.folder)))

    def test_hidden_metadata_lines_preserve_report_and_memo_identities(self) -> None:
        original_report = self.report.read_text()
        original_memo_digest = memo_content_sha256(self.memo)
        self.report.write_text(original_report.replace(
            "The endpoint", "<!-- presentation digest -->\nThe endpoint"
        ))
        self.memo.write_text(self.memo.read_text().replace(
            "The conditional", "<!-- first metadata -->\n<!-- second metadata -->\nThe conditional"
        ))
        self.assertEqual(report_content_sha256(original_report), report_content_sha256(self.report.read_text()))
        self.assertEqual(original_memo_digest, memo_content_sha256(self.memo))
        self.assertEqual(report_memo_coverage_errors(self.folder), ())

    def test_inline_comment_does_not_hide_intervening_reader_prose(self) -> None:
        original = "## 10. Notes\nAn <!-- invisible --> assumption.\nAnother claim.\n<!-- metadata -->\n"
        visible = "## 10. Notes\nAn  assumption.\nAnother claim.\n"
        self.assertEqual(report_content_sha256(original), report_content_sha256(visible))
        self.assertNotEqual(report_content_sha256(original), report_content_sha256("## 10. Notes\n"))

    def test_missing_unlinked_or_dangling_heading_fails(self) -> None:
        self.memo.unlink()
        self.assertTrue(any("missing or unreadable" in e for e in report_memo_coverage_errors(self.folder)))
        self.memo.write_text("# Another explanation\nThe condition is stated here.\n")
        self.assertTrue(any("heading does not resolve" in e for e in report_memo_coverage_errors(self.folder)))
        self.report.write_text(self.report.read_text().replace("[Explanation](./docs/SOURCE_CLARIFICATIONS.md#positive-mass)", ""))
        self.assertTrue(any("does not link" in e for e in report_memo_coverage_errors(self.folder)))

    def test_internal_target_and_path_escape_fail(self) -> None:
        for path in ("audit/APPROVAL.md", "../elsewhere.md", "/tmp/note.md"):
            with self.subTest(path=path):
                self.assessment["items"]["defect/mass"]["memo"] = path
                self.save()
                self.assertTrue(any("paper-local" in e for e in report_memo_coverage_errors(self.folder)))

    def test_symlink_escape_fails(self) -> None:
        outside = Path(self.temp.name) / "outside.md"
        outside.write_text("# Private note\n")
        self.memo.unlink()
        self.memo.symlink_to(outside)
        self.assertTrue(any("escapes" in e for e in report_memo_coverage_errors(self.folder)))

    def test_symlinked_docs_directory_cannot_import_external_memos(self) -> None:
        docs = self.folder / "docs"
        outside = Path(self.temp.name) / "external-docs"
        docs.rename(outside)
        docs.symlink_to(outside, target_is_directory=True)
        self.assertTrue(any("escapes" in e for e in report_memo_coverage_errors(self.folder)))

    def test_symlink_cycle_is_a_document_finding(self) -> None:
        self.memo.unlink()
        self.memo.symlink_to(self.memo.name)
        self.assertTrue(any("escapes" in e for e in report_memo_coverage_errors(self.folder)))

    def test_changed_explanation_requires_reassessment(self) -> None:
        self.memo.write_text(self.memo.read_text().replace("positive-mass", "arbitrary"))
        self.assertTrue(any("changed since" in e for e in report_memo_coverage_errors(self.folder)))

    def test_internal_document_under_docs_cannot_count_as_memo(self) -> None:
        self.assessment["items"]["defect/mass"]["memo"] = "docs/SOURCE_CORRECTION_AUTHORITY.md"
        self.save()
        self.assertTrue(any("internal approval or working document" in e for e in report_memo_coverage_errors(self.folder)))

    def test_reader_labels_and_private_approval_records_fail(self) -> None:
        for text, expected in (
            ("Codex draft for review", "draft label"),
            (">>> START OF GENERATED CONTENT >>>", "generated boundary"),
            ("Repository user approved this in docs/APPROVED_TARGET.md", "internal approval"),
        ):
            with self.subTest(text=text):
                self.memo.write_text("# Source clarifications\n## Positive mass\n" + text)
                self.assertTrue(any(expected in e for e in report_memo_coverage_errors(self.folder)))

    def test_hidden_generator_markers_keep_substantive_memo(self) -> None:
        text = self.memo.read_text()
        self.memo.write_text("<!-- BEGIN GENERATED CONTEXT -->\n" + text + "<!-- END GENERATED CONTEXT -->\n")
        self.assertEqual(report_memo_coverage_errors(self.folder), ())

    def test_approval_labels_are_rejected_in_reports_and_memos(self) -> None:
        original_report = self.report.read_text()
        original_memo = self.memo.read_text()
        for phrase in ("author-approved correction", "formalizer-approved target",
                       "owner approved the model", "Approved additional assumptions"):
            for target, original in ((self.report, original_report), (self.memo, original_memo)):
                with self.subTest(phrase=phrase, target=target.name):
                    target.write_text(original + "\n" + phrase + "\n")
                    self.assertTrue(any("approval label" in e for e in report_memo_coverage_errors(self.folder)))
                    target.write_text(original)

    def test_mathematical_approval_and_evidence_identifiers_are_not_endorsements(self) -> None:
        self.report.write_text(self.report.read_text() +
            "\n## 12. Evidence\nK-approval voting counts approved candidates.\n"
            "`matches_approved_corrected_target` names an evidence disposition.\n"
            "<!-- author-approved target: historical metadata -->\n")
        self.assertEqual(report_memo_coverage_errors(self.folder), ())

    def test_assumption_explanation_needs_a_link_at_the_discussion(self) -> None:
        original = self.report.read_text()
        section = "## 6. Additional Assumptions Beyond Paper\nPositive mass is required.\n\n"
        self.report.write_text(section + original)
        self.assertTrue(any("Section 6" in e for e in report_memo_coverage_errors(self.folder)))
        self.report.write_text(section.replace("required.",
            "required; see [why](docs/SOURCE_CLARIFICATIONS.md#positive-mass).") + original)
        self.assertFalse(any("Section 6" in e for e in report_memo_coverage_errors(self.folder)))
        self.report.write_text("## 6. Additional Assumptions Beyond Paper\nNone.\n\n" + original)
        self.assertFalse(any("Section 6" in e for e in report_memo_coverage_errors(self.folder)))

    def test_visible_boundaries_in_later_report_sections_are_rejected(self) -> None:
        self.report.write_text(self.report.read_text() + "\n## 12. Validation\n>>> START OF GENERATED CONTENT >>>\n")
        self.assertTrue(any("visible generated boundary" in e for e in report_memo_coverage_errors(self.folder)))

    def test_historical_reviewer_identifier_is_not_a_reader_draft_label(self) -> None:
        self.report.write_text(self.report.read_text() + "\n## 12. Review record\nReviewer: codex-agent-paper-draft-semantic-pass\n")
        self.assertEqual(report_memo_coverage_errors(self.folder), ())

    def test_display_summary_is_not_a_source_assessment_input(self) -> None:
        data = json.loads(self.fidelity.read_text())
        data["model_conventions"][0]["report_summary"] = "Reader wording."
        self.fidelity.write_text(json.dumps(data))
        self.assertEqual(report_memo_coverage_errors(self.folder), ())

    def test_schema_one_cannot_satisfy_a_new_document_closeout(self) -> None:
        self.assessment["schema"] = 1
        del self.assessment["result_table"]
        self.save()
        errors = report_memo_coverage_errors(self.folder)
        self.assertTrue(any("expected schema 2" in error for error in errors))
        self.assertTrue(any("result_table is not an object" in error for error in errors))

    def test_selected_results_have_exact_grouped_row_mappings(self) -> None:
        self.install_text_source_results()
        self.assertEqual(report_memo_coverage_errors(self.folder), ())
        del self.assessment["result_table"]["results"]["lemma2"]
        self.save()
        self.assertTrue(any(
            "selected named result has no Section 4 mapping: lemma2" in error
            for error in report_memo_coverage_errors(self.folder)
        ))

    def test_unknown_result_and_unreviewed_grouping_fail(self) -> None:
        self.install_text_source_results()
        mapping = dict(self.assessment["result_table"]["results"]["theorem1"])
        mapping.pop("grouping_reason")
        self.assessment["result_table"]["results"]["theorem1"] = mapping
        self.assessment["result_table"]["results"]["unknown"] = dict(mapping)
        self.save()
        errors = report_memo_coverage_errors(self.folder)
        self.assertTrue(any("unknown selected result: unknown" in error for error in errors))
        self.assertTrue(any("without a grouping_reason" in error for error in errors))

    def test_source_absent_checkout_validates_portable_inventory(self) -> None:
        self.install_text_source_results()
        (self.folder / "source.txt").unlink()
        self.assertEqual(report_memo_coverage_errors(self.folder), ())

    def test_source_absent_checkout_still_needs_typed_inventory_receipt(self) -> None:
        self.install_text_source_results()
        (self.folder / "source.txt").unlink()
        source_map_path = self.folder / "audit/paper_statement_map.json"
        source_map = json.loads(source_map_path.read_text())
        source_map["source_named_result_inventory_review"]["complete"] = False
        source_map_path.write_text(json.dumps(source_map))
        self.assertTrue(any(
            "no complete typed named-result inventory receipt" in error
            for error in report_memo_coverage_errors(self.folder)
        ))

    def test_present_but_changed_source_does_not_use_portable_fallback(self) -> None:
        self.install_text_source_results()
        (self.folder / "source.txt").write_text(
            "Theorem 1. A changed theorem.\nLemma 2. The stable allocation is unique.\n"
        )
        self.assertTrue(any(
            "cannot verify the present source artifact" in error
            for error in report_memo_coverage_errors(self.folder)
        ))

    def test_source_receipt_and_inventory_changes_are_stale(self) -> None:
        self.install_text_source_results()
        source_map_path = self.folder / "audit/paper_statement_map.json"
        source_map = json.loads(source_map_path.read_text())
        source_map["source_named_result_inventory_review"][
            "discovered_named_result_sha256"
        ] = "0" * 64
        source_map_path.write_text(json.dumps(source_map))
        self.assertTrue(any(
            "current named-result receipt" in error
            for error in report_memo_coverage_errors(self.folder)
        ))
        source_map_path.write_text(json.dumps({
            **source_map,
            "source_named_result_inventory_review": {
                **source_map["source_named_result_inventory_review"],
                "discovered_named_result_sha256": self.assessment["result_table"]
                ["source_inventory"]["discovered_named_result_sha256"],
            },
        }))
        self.assessment["result_table"]["source_inventory"]["results"].pop("lemma2")
        self.save()
        self.assertTrue(any(
            "source inventory digest is stale" in error
            for error in report_memo_coverage_errors(self.folder)
        ))

    def test_present_source_rejects_coordinated_bogus_receipt_metadata(self) -> None:
        self.install_text_source_results()
        source_map_path = self.folder / "audit/paper_statement_map.json"
        source_map = json.loads(source_map_path.read_text())
        source_map["source_named_result_inventory_review"][
            "discovered_named_result_sha256"
        ] = "0" * 64
        source_map_path.write_text(json.dumps(source_map))
        inventory = self.assessment["result_table"]["source_inventory"]
        inventory["discovered_named_result_sha256"] = "0" * 64
        self.assessment["result_table"]["source_inventory_sha256"] = hashlib.sha256(
            json.dumps(
                inventory,
                ensure_ascii=True,
                sort_keys=True,
                separators=(",", ":"),
            ).encode()
        ).hexdigest()
        self.save()
        self.assertTrue(any(
            "named-result receipt is stale for the current source" in error
            for error in report_memo_coverage_errors(self.folder)
        ))

    def test_printed_text_label_must_match_visible_source_heading(self) -> None:
        self.install_text_source_results()
        self.assessment["result_table"]["results"]["theorem1"][
            "printed_label"
        ] = "Theorem 9"
        self.save()
        self.assertTrue(any(
            "does not match the visible source heading" in error
            for error in report_memo_coverage_errors(self.folder)
        ))

    def test_split_result_needs_justification_and_per_row_labels(self) -> None:
        self.install_text_source_results()
        report = self.report.read_text().replace(
            "| Theorems 1–2 | The conclusions are checked. "
            "[Explanation](docs/SOURCE_CLARIFICATIONS.md#positive-mass). |",
            "| Theorems 1–2 | The conclusions are checked. "
            "[Explanation](docs/SOURCE_CLARIFICATIONS.md#positive-mass). |\n"
            "| Theorem 1(b) | The second clause is checked. |",
        )
        self.report.write_text(report)
        self.assessment = coverage_template(self.folder)
        self.assessment["all_selected_semantic_review_sha256"] = "a" * 64
        self.assessment["report_inventory_complete"] = True
        self.assessment["items"] = {
            "defect/mass": {
                "disposition": "memo",
                "memo": "docs/SOURCE_CLARIFICATIONS.md",
                "memo_heading": "Positive mass",
                "memo_anchor": "positive-mass",
                "memo_sha256": memo_content_sha256(self.memo),
            },
            "convention/encoding": {
                "disposition": "not_material",
                "reason": "The encoding changes no premise.",
            },
        }
        table = self.assessment["result_table"]
        table["complete"] = True
        row_ids = list(table["rows"])
        table["rows"][row_ids[0]]["explanation_keys"] = ["defect/mass"]
        for result_id, mapping in table["results"].items():
            mapping["grouping_reason"] = "The first row groups the selected results."
            mapping["row_mappings"] = [
                {"report_label": "Theorems 1–2", "row_sha256": row_ids[0]}
            ]
            if result_id == "theorem1":
                mapping["row_mappings"].append(
                    {"report_label": "Theorem 1(b)", "row_sha256": row_ids[1]}
                )
        self.save()
        self.assertTrue(any(
            "without a split_reason" in error
            for error in report_memo_coverage_errors(self.folder)
        ))
        self.assessment["result_table"]["results"]["theorem1"][
            "split_reason"
        ] = "The report discusses the theorem's two clauses separately."
        self.save()
        self.assertEqual(report_memo_coverage_errors(self.folder), ())

    def test_result_deviation_needs_exact_row_memo_anchor(self) -> None:
        self.install_text_source_results()
        row_id = next(iter(self.assessment["result_table"]["rows"]))
        self.assessment["result_table"]["rows"][row_id]["explanation_keys"] = []
        self.save()
        self.assertTrue(any(
            "no exact Section 4 memo mapping for defect/mass" in error
            for error in report_memo_coverage_errors(self.folder)
        ))
        self.assessment["result_table"]["rows"][row_id]["explanation_keys"] = [
            "defect/mass"
        ]
        self.assessment["items"]["defect/mass"]["memo_anchor"] = "wrong-anchor"
        self.save()
        errors = report_memo_coverage_errors(self.folder)
        self.assertTrue(any("no exact reviewed memo target" in error for error in errors))
        self.assertTrue(any("memo anchor does not resolve" in error for error in errors))

    def test_proof_route_memo_can_have_section_seven_report_home(self) -> None:
        self.install_text_source_results()
        old_row_id = next(iter(self.assessment["result_table"]["rows"]))
        report = self.report.read_text().replace(
            "The conclusions are checked. "
            "[Explanation](docs/SOURCE_CLARIFICATIONS.md#positive-mass).",
            "The conclusions are checked.",
        ).replace(
            "## 10. Source Clarifications",
            "## 7. Proof-Strategy Deviations\n"
            "The corrected route is explained in the "
            "[memo](docs/SOURCE_CLARIFICATIONS.md#positive-mass).\n\n"
            "## 10. Source Clarifications",
        )
        self.report.write_text(report)
        rows, errors = section_four_result_table(report)
        self.assertEqual(errors, ())
        new_row_id = rows[0].sha256
        table = self.assessment["result_table"]
        table["rows"] = {
            new_row_id: {
                "explanation_keys": [],
                "supplemental_reason": "",
            }
        }
        for mapping in table["results"].values():
            mapping["row_mappings"][0]["row_sha256"] = new_row_id
        self.assessment["items"]["defect/mass"]["report_home"] = 7
        self.assessment["report_sha256"] = report_content_sha256(report)
        self.save()
        self.assertEqual(report_memo_coverage_errors(self.folder), ())
        self.report.write_text(report.replace(
            "[memo](docs/SOURCE_CLARIFICATIONS.md#positive-mass)",
            "memo",
        ))
        self.assessment["report_sha256"] = report_content_sha256(
            self.report.read_text()
        )
        self.save()
        self.assertTrue(any(
            "reviewed Section 7 report_home" in error
            for error in report_memo_coverage_errors(self.folder)
        ))

    def test_non_section_four_report_home_requires_exact_anchor_in_that_section(self) -> None:
        self.install_text_source_results()
        item = self.assessment["items"]["defect/mass"]
        item["report_home"] = 7
        item.pop("memo_heading")
        item.pop("memo_anchor")
        self.save()
        errors = report_memo_coverage_errors(self.folder)
        self.assertTrue(any(
            "Section 7 report_home needs an exact memo heading and anchor" in error
            for error in errors
        ))

        item["memo_heading"] = "Positive mass"
        item["memo_anchor"] = "positive-mass"
        self.save()
        errors = report_memo_coverage_errors(self.folder)
        self.assertTrue(any(
            "not linked from its reviewed Section 7 report_home" in error
            for error in errors
        ))

    def test_non_section_four_corrected_target_is_not_duplicated_in_result_row(self) -> None:
        raw_items = {
            "main": {
                "corrected_target": {"statement": "corrected"},
                "accepted_additional_assumptions": ["finite"],
            }
        }
        coverage_items = {
            "source/main/corrected_target": {
                "disposition": "memo",
                "report_home": 7,
            },
            "source/main/additional_assumptions": {
                "disposition": "memo",
                "report_home": 7,
            },
        }
        self.assertEqual(
            _required_result_explanation_keys(
                raw_items, ["main"], coverage_items
            ),
            set(),
        )
        coverage_items["source/main/corrected_target"]["report_home"] = 4
        self.assertEqual(
            _required_result_explanation_keys(
                raw_items, ["main"], coverage_items
            ),
            {"source/main/corrected_target"},
        )

    def test_non_section_four_pdf_home_uses_exact_path_link(self) -> None:
        self.install_text_source_results()
        old_row_id = next(iter(self.assessment["result_table"]["rows"]))
        report = self.report.read_text().replace(
            "The conclusions are checked. "
            "[Explanation](docs/SOURCE_CLARIFICATIONS.md#positive-mass).",
            "The conclusions are checked.",
        ).replace(
            "## 10. Source Clarifications",
            "## 7. Proof-Strategy Deviations\n"
            "The detailed replacement is in the [PDF](docs/details.pdf).\n\n"
            "## 10. Source Clarifications",
        )
        self.report.write_text(report)
        rows, errors = section_four_result_table(report)
        self.assertEqual(errors, ())
        new_row_id = rows[0].sha256
        table = self.assessment["result_table"]
        table["rows"] = {
            new_row_id: {"explanation_keys": [], "supplemental_reason": ""}
        }
        for mapping in table["results"].values():
            mapping["row_mappings"][0]["row_sha256"] = new_row_id
        pdf = self.folder / "docs/details.pdf"
        pdf.write_bytes(b"%PDF fixture")
        item = self.assessment["items"]["defect/mass"]
        item.update({
            "memo": "docs/details.pdf",
            "memo_sha256": hashlib.sha256(b"PDF explanation").hexdigest(),
            "report_home": 7,
        })
        item.pop("memo_heading")
        item.pop("memo_anchor")
        self.assessment["report_sha256"] = report_content_sha256(report)
        self.save()
        with mock.patch(
            "scripts.report_memo_coverage._memo_text",
            return_value="PDF explanation",
        ):
            self.assertEqual(report_memo_coverage_errors(self.folder), ())

    def test_exact_memo_link_may_be_in_result_cell(self) -> None:
        self.install_text_source_results()
        old_row_id = next(iter(self.assessment["result_table"]["rows"]))
        report = self.report.read_text().replace(
            "| Theorems 1–2 | The conclusions are checked. "
            "[Explanation](docs/SOURCE_CLARIFICATIONS.md#positive-mass). |",
            "| [Theorems 1–2](docs/SOURCE_CLARIFICATIONS.md#positive-mass) "
            "| The conclusions are checked. |",
        )
        self.report.write_text(report)
        rows, errors = section_four_result_table(report)
        self.assertEqual(errors, ())
        new_row_id = rows[0].sha256
        self.assessment["report_sha256"] = report_content_sha256(report)
        self.assessment["result_table"]["rows"] = {
            new_row_id: self.assessment["result_table"]["rows"][old_row_id]
        }
        for mapping in self.assessment["result_table"]["results"].values():
            mapping["row_mappings"][0]["row_sha256"] = new_row_id
        self.save()
        self.assertEqual(report_memo_coverage_errors(self.folder), ())

    def test_tex_reference_key_cannot_stand_in_for_printed_number(self) -> None:
        source_text = (
            "\\newtheorem{theorem}{Theorem}\n"
            "\\begin{theorem}\\label{thm:main}\n"
            "A stable allocation exists.\n"
            "\\end{theorem}\n"
        )
        source = self.folder / "source.tex"
        source.write_text(source_text)
        presentations = reviewed_source_presentation_inventory(
            source_text, source_path="source.tex", source_format="tex"
        ).classified
        source_sha256 = hashlib.sha256(source_text.encode()).hexdigest()
        quote = "\n".join(source_text.splitlines()[1:4])
        source_map = {
            "source_artifact_path": "source.tex",
            "source_artifact_sha256": source_sha256,
            "source_coverage_mode": "named_theoretical_statements",
            "source_named_result_inventory_review": {
                "complete": True,
                "source_artifact_sha256": source_sha256,
                "discovered_named_result_sha256": named_result_presentations_sha256(
                    presentations
                ),
            },
            "items": {
                "main": {
                    "source_kind": "theorem",
                    "source_anchor_evidence": [{
                        "path": "source.tex",
                        "line_start": 2,
                        "line_end": 4,
                        "quoted_text": quote,
                        "quoted_text_sha256": hashlib.sha256(quote.encode()).hexdigest(),
                    }],
                }
            },
        }
        (self.folder / "audit/paper_statement_map.json").write_text(json.dumps(source_map))
        self.report.write_text(
            "## 4. Result Comparison\n"
            "| Result | Comparison with source |\n| --- | --- |\n"
            "| Theorem 1 | Exact checked conclusion. |\n"
            "## 10. Source Clarifications\nNone.\n"
            "## 11. Paper Issues or Caveats\nNone.\n"
        )
        self.fidelity.write_text(json.dumps({"defects": [], "model_conventions": []}))
        self.assessment = coverage_template(self.folder)
        self.assessment["all_selected_semantic_review_sha256"] = "a" * 64
        self.assessment["report_inventory_complete"] = True
        self.assessment["result_table"]["complete"] = True
        row_id = next(iter(self.assessment["result_table"]["rows"]))
        mapping = self.assessment["result_table"]["results"]["main"]
        mapping["printed_label"] = "thm:main"
        mapping["printed_label_basis"] = "source_text_heading"
        mapping["row_mappings"] = [
            {"report_label": "Theorem 1", "row_sha256": row_id}
        ]
        mapping["grouping_reason"] = "The TeX key is not the rendered theorem number."
        self.save()
        errors = report_memo_coverage_errors(self.folder)
        self.assertTrue(any("valid human-facing printed label" in error for error in errors))
        self.assertTrue(any("visible source heading" in error for error in errors))
        mapping["printed_label"] = "Theorem 1"
        mapping["printed_label_basis"] = "reviewed_rendered_source"
        mapping.pop("grouping_reason")
        self.save()
        self.assertEqual(report_memo_coverage_errors(self.folder), ())

    def test_repeated_source_presentation_has_one_logical_result_mapping(self) -> None:
        source_text = (
            "Theorem 1. A stable allocation exists.\n\n"
            "Theorem 1. A stable allocation exists.\n"
        )
        source = self.folder / "source.txt"
        source.write_text(source_text)
        presentations = reviewed_source_presentation_inventory(
            source_text, source_path="source.txt", source_format="text"
        ).classified
        source_sha256 = hashlib.sha256(source_text.encode()).hexdigest()
        lines = source_text.splitlines()
        source_map = {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_sha256,
            "source_coverage_mode": "named_theoretical_statements",
            "source_named_result_inventory_review": {
                "complete": True,
                "source_artifact_sha256": source_sha256,
                "discovered_named_result_sha256": named_result_presentations_sha256(
                    presentations
                ),
            },
            "items": {
                "main": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [self.anchor("source.txt", 1, lines[0])],
                },
                "appendix": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:3",
                    "source_anchor_evidence": [self.anchor("source.txt", 3, lines[2])],
                    "source_presentation_alias": {
                        "schema": 1,
                        "relation": "repeated_source_presentation",
                        "label_relation": "same_visible_label",
                        "canonical_source_item": "main",
                        "semantic_basis": "The appendix repeats the same visible result.",
                        "validator": "fixture source reader",
                        "validated_at": "2026-09-06T00:00:00Z",
                    },
                },
            },
        }
        (self.folder / "audit/paper_statement_map.json").write_text(json.dumps(source_map))
        self.fidelity.write_text(json.dumps({"defects": [], "model_conventions": []}))
        self.report.write_text(
            "## 4. Result Comparison\n"
            "| Result | Comparison with source |\n| --- | --- |\n"
            "| Theorem 1 | Exact checked conclusion. |\n"
            "## 10. Source Clarifications\nNone.\n"
            "## 11. Paper Issues or Caveats\nNone.\n"
        )
        self.assessment = coverage_template(self.folder)
        self.assessment["all_selected_semantic_review_sha256"] = "a" * 64
        table = self.assessment["result_table"]
        self.assertEqual(set(table["results"]), {"main"})
        self.assertEqual(
            table["source_inventory"]["results"]["main"]["source_item_ids"],
            ["appendix", "main"],
        )
        self.assessment["report_inventory_complete"] = True
        table["complete"] = True
        row_id = next(iter(table["rows"]))
        table["results"]["main"]["row_mappings"] = [
            {"report_label": "Theorem 1", "row_sha256": row_id}
        ]
        self.save()
        self.assertEqual(report_memo_coverage_errors(self.folder), ())
        source.unlink()
        inventory = table["source_inventory"]
        inventory["results"]["main"]["presentations"] = [
            row
            for row in inventory["results"]["main"]["presentations"]
            if row["source_item_id"] != "appendix"
        ]
        table["source_inventory_sha256"] = hashlib.sha256(json.dumps(
            inventory, ensure_ascii=True, sort_keys=True, separators=(",", ":")
        ).encode()).hexdigest()
        self.save()
        self.assertTrue(any(
            "omits repeated source presentation records" in error
            for error in report_memo_coverage_errors(self.folder)
        ))
        inventory["results"]["main"]["source_item_ids"].remove("appendix")
        table["source_inventory_sha256"] = hashlib.sha256(json.dumps(
            inventory, ensure_ascii=True, sort_keys=True, separators=(",", ":")
        ).encode()).hexdigest()
        self.save()
        self.assertTrue(any(
            "omits a current repeated source presentation" in error
            for error in report_memo_coverage_errors(self.folder)
        ))

    def test_scope_excluded_canonical_accepts_its_current_explicit_alias(self) -> None:
        source_text = (
            "Theorem 1. A stable allocation exists.\n\n"
            "Theorem 1. A stable allocation exists.\n"
        )
        source = self.folder / "source.txt"
        source.write_text(source_text)
        presentations = reviewed_source_presentation_inventory(
            source_text, source_path="source.txt", source_format="text"
        ).classified
        source_sha256 = hashlib.sha256(source_text.encode()).hexdigest()
        lines = source_text.splitlines()
        source_map = {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_sha256,
            "source_coverage_mode": "named_theoretical_statements",
            "source_named_result_inventory_review": {
                "complete": True,
                "source_artifact_sha256": source_sha256,
                "discovered_named_result_sha256": named_result_presentations_sha256(
                    presentations
                ),
            },
            "items": {
                "main": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "inventory_role": "source_scope_exclusion",
                    "coverage_status": "user_approved_scope_exclusion",
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [
                        self.anchor("source.txt", 1, lines[0])
                    ],
                },
                "appendix": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:3",
                    "source_anchor_evidence": [
                        self.anchor("source.txt", 3, lines[2])
                    ],
                    "source_presentation_alias": {
                        "schema": 1,
                        "relation": "repeated_source_presentation",
                        "label_relation": "same_visible_label",
                        "canonical_source_item": "main",
                        "semantic_basis": "The appendix repeats the same visible result.",
                        "validator": "fixture source reader",
                        "validated_at": "2026-09-06T00:00:00Z",
                    },
                },
            },
        }
        (self.folder / "audit/paper_statement_map.json").write_text(
            json.dumps(source_map)
        )
        self.fidelity.write_text(json.dumps({"defects": [], "model_conventions": []}))
        self.report.write_text(
            "## 4. Result Comparison\n"
            "| Result | Comparison with source |\n| --- | --- |\n"
            "| Theorem 1 | Deferred source scope. |\n"
            "## 10. Source Clarifications\nNone.\n"
            "## 11. Paper Issues or Caveats\nNone.\n"
        )
        self.assessment = coverage_template(self.folder)
        self.assessment["all_selected_semantic_review_sha256"] = "a" * 64
        self.assessment["report_inventory_complete"] = True
        table = self.assessment["result_table"]
        self.assertEqual(set(table["results"]), {"main"})
        inventory = table["source_inventory"]
        inventory["results"]["main"]["presentations"] = [
            row
            for row in inventory["results"]["main"]["presentations"]
            if row["source_item_id"] == "appendix"
        ]
        table["source_inventory_sha256"] = hashlib.sha256(json.dumps(
            inventory,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode()).hexdigest()
        self.assertEqual(
            [
                row["source_item_id"]
                for row in inventory["results"]["main"][
                    "presentations"
                ]
            ],
            ["appendix"],
        )
        table["complete"] = True
        row_id = next(iter(table["rows"]))
        table["results"]["main"]["row_mappings"] = [
            {"report_label": "Theorem 1", "row_sha256": row_id}
        ]
        self.save()
        with mock.patch(
            "scripts.report_memo_coverage._current_source_result_inventory",
            return_value=inventory,
        ):
            self.assertEqual(report_memo_coverage_errors(self.folder), ())

        table["source_inventory"]["results"]["main"]["presentations"][0][
            "source_item_id"
        ] = "foreign"
        table["source_inventory_sha256"] = hashlib.sha256(json.dumps(
            table["source_inventory"],
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode()).hexdigest()
        self.save()
        with mock.patch(
            "scripts.report_memo_coverage._current_source_result_inventory",
            return_value=inventory,
        ):
            self.assertTrue(any(
                "source presentations omit their canonical or alias item" in error
                for error in report_memo_coverage_errors(self.folder)
            ))

    def test_named_presentation_can_share_span_with_supporting_source_items(self) -> None:
        source_text = "Theorem 1. A stable allocation exists.\n"
        source = self.folder / "source.txt"
        source.write_text(source_text)
        presentations = reviewed_source_presentation_inventory(
            source_text, source_path="source.txt", source_format="text"
        ).classified
        source_sha256 = hashlib.sha256(source_text.encode()).hexdigest()
        common_anchor = self.anchor("source.txt", 1, source_text.strip())
        source_map = {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_sha256,
            "source_coverage_mode": "named_theoretical_statements",
            "source_named_result_inventory_review": {
                "complete": True,
                "source_artifact_sha256": source_sha256,
                "discovered_named_result_sha256": named_result_presentations_sha256(
                    presentations
                ),
            },
            "items": {
                "main": {
                    "source_kind": "theorem",
                    "source_anchor_evidence": [common_anchor],
                },
                "supporting_formula": {
                    "source_kind": "formula",
                    "source_anchor_evidence": [common_anchor],
                },
                "assumption_context": {
                    "source_kind": "assumption",
                    "source_anchor_evidence": [common_anchor],
                },
            },
        }
        (self.folder / "audit/paper_statement_map.json").write_text(
            json.dumps(source_map)
        )
        self.fidelity.write_text(json.dumps({"defects": [], "model_conventions": []}))
        self.report.write_text(
            "## 4. Result Comparison\n"
            "| Result | Comparison with source |\n| --- | --- |\n"
            "| Theorem 1 | Exact checked conclusion. |\n"
            "## 10. Source Clarifications\nNone.\n"
            "## 11. Paper Issues or Caveats\nNone.\n"
        )
        self.assessment = coverage_template(self.folder)
        self.assessment["all_selected_semantic_review_sha256"] = "a" * 64
        self.assessment["report_inventory_complete"] = True
        table = self.assessment["result_table"]
        table["complete"] = True
        result = table["source_inventory"]["results"]["main"]
        self.assertEqual(
            result["source_item_ids"],
            ["assumption_context", "main", "supporting_formula"],
        )
        row_id = next(iter(table["rows"]))
        table["results"]["main"]["row_mappings"] = [
            {"report_label": "Theorem 1", "row_sha256": row_id}
        ]
        self.save()
        self.assertEqual(report_memo_coverage_errors(self.folder), ())

    def test_reviewed_source_label_need_not_repeat_internal_claim_kind(self) -> None:
        label, basis, numbering = _automatic_printed_label(
            {"source_format": "text"},
            {
                "kind": "claim",
                "presentations": [{"source_label": "Remark 1"}],
            },
        )
        self.assertEqual((label, basis, numbering), ("", "needs_review", "unnumbered"))

        self.install_text_source_results()
        mapping = self.assessment["result_table"]["results"]["theorem1"]
        mapping["printed_label"] = "Remark 1"
        mapping["printed_label_basis"] = "reviewed_rendered_source"
        mapping["numbering"] = "numbered"
        mapping["grouping_reason"] = "The source renders this claim as Remark 1."
        mapping["row_mappings"][0]["report_label"] = "Theorems 1–2"
        self.save()
        errors = report_memo_coverage_errors(self.folder)
        self.assertFalse(any("human-facing printed label" in error for error in errors))

    def test_arbitrary_prose_label_is_not_synthesized_as_a_numbered_theorem(self) -> None:
        self.assertEqual(
            _automatic_printed_label(
                {"source_format": "text"},
                {
                    "kind": "theorem",
                    "presentations": [{
                        "source_label": "the stable assignment has been achieved"
                    }],
                },
            ),
            ("", "needs_review", "unnumbered"),
        )

    def test_selected_semantic_owner_survives_mangled_source_heading(self) -> None:
        source_text = "Theorem\n1. A stable allocation exists.\n"
        source = self.folder / "source.txt"
        source.write_text(source_text)
        presentations = reviewed_source_presentation_inventory(
            source_text, source_path="source.txt", source_format="text"
        ).classified
        source_sha256 = hashlib.sha256(source_text.encode()).hexdigest()
        source_map = {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_sha256,
            "source_coverage_mode": "named_theoretical_statements",
            "source_named_result_inventory_review": {
                "complete": True,
                "source_artifact_sha256": source_sha256,
                "discovered_named_result_sha256": named_result_presentations_sha256(
                    presentations
                ),
            },
            "items": {
                "main": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "semantic_contract": {"spec_declaration": "Fixture.mainSpec"},
                    "source_anchor_evidence": [
                        {
                            "path": "source.txt",
                            "line_start": 1,
                            "line_end": 2,
                            "quoted_text": source_text.rstrip(),
                            "quoted_text_sha256": hashlib.sha256(
                                source_text.rstrip().encode()
                            ).hexdigest(),
                        }
                    ],
                }
            },
        }
        (self.folder / "audit/paper_statement_map.json").write_text(
            json.dumps(source_map)
        )
        table = coverage_template(self.folder)["result_table"]
        self.assertEqual(set(table["results"]), {"main"})
        self.assertEqual(
            table["source_inventory"]["results"]["main"]["presentations"],
            [],
        )
        self.assertEqual(
            _portable_source_inventory_errors(
                self.folder,
                table["source_inventory"],
                table["source_inventory_sha256"],
            )[0],
            [],
        )

    def test_quarantined_theorem_heading_is_not_a_result_table_conclusion(self) -> None:
        source_text = "Theorem 1. A false reverse implication.\n"
        source = self.folder / "source.txt"
        source.write_text(source_text)
        presentations = reviewed_source_presentation_inventory(
            source_text, source_path="source.txt", source_format="text"
        ).classified
        source_sha256 = hashlib.sha256(source_text.encode()).hexdigest()
        source_map = {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_sha256,
            "source_coverage_mode": "named_theoretical_statements",
            "source_named_result_inventory_review": {
                "complete": True,
                "source_artifact_sha256": source_sha256,
                "discovered_named_result_sha256": named_result_presentations_sha256(
                    presentations
                ),
            },
            "items": {
                "false_restatement": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "source_status": "quarantined_source_defect",
                    "inventory_role": "quarantined_source_defect",
                    "source_anchor_evidence": [
                        self.anchor("source.txt", 1, source_text.rstrip())
                    ],
                }
            },
        }
        (self.folder / "audit/paper_statement_map.json").write_text(
            json.dumps(source_map)
        )
        table = coverage_template(self.folder)["result_table"]
        self.assertEqual(table["results"], {})

    def test_labelled_assumption_is_not_a_result_table_conclusion(self) -> None:
        source_text = "Assumption A1. Arrivals follow a Poisson process.\n"
        source = self.folder / "source.txt"
        source.write_text(source_text)
        candidate = {
            "schema": 1,
            "id": "assumption_a1",
            "presentation_label": "Assumption A1",
            "visible_kind": "holistic",
            "scope_disposition": "material_named_claim",
            "semantic_basis": "A1 is a labelled model condition.",
            "discovery_basis": "holistic_full_text_review",
            "source_anchor": self.anchor("source.txt", 1, source_text.rstrip()),
        }
        presentations = reviewed_source_presentation_inventory(
            source_text,
            source_path="source.txt",
            source_format="text",
            candidate_dispositions=[candidate],
        ).classified
        source_sha256 = hashlib.sha256(source_text.encode()).hexdigest()
        source_map = {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_sha256,
            "source_coverage_mode": "named_theoretical_statements",
            "source_named_result_inventory_review": {
                "complete": True,
                "source_artifact_sha256": source_sha256,
                "discovered_named_result_sha256": named_result_presentations_sha256(
                    presentations
                ),
                "candidate_presentations": [candidate],
            },
            "items": {
                "arrival_condition": {
                    "source_kind": "assumption",
                    "claim_bearing": True,
                    "inventory_role": "source_semantic_declaration",
                    "source_anchor_evidence": [
                        self.anchor("source.txt", 1, source_text.rstrip())
                    ],
                }
            },
        }
        (self.folder / "audit/paper_statement_map.json").write_text(
            json.dumps(source_map)
        )
        table = coverage_template(self.folder)["result_table"]
        self.assertEqual(table["results"], {})

    def test_only_explicit_user_scope_exclusion_is_not_a_result(self) -> None:
        source_text = (
            "Lemma 8. An externally attributed result.\n\n"
            "Theorem 3.1. A selected result awaiting a direct proof.\n"
        )
        source = self.folder / "source.txt"
        source.write_text(source_text)
        presentations = reviewed_source_presentation_inventory(
            source_text, source_path="source.txt", source_format="text"
        ).classified
        source_sha256 = hashlib.sha256(source_text.encode()).hexdigest()
        lines = source_text.splitlines()
        source_map = {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_sha256,
            "source_coverage_mode": "named_theoretical_statements",
            "source_named_result_inventory_review": {
                "complete": True,
                "source_artifact_sha256": source_sha256,
                "discovered_named_result_sha256": named_result_presentations_sha256(
                    presentations
                ),
            },
            "items": {
                "excluded_lemma": {
                    "source_kind": "lemma",
                    "claim_bearing": True,
                    "inventory_role": "source_scope_exclusion",
                    "scope_disposition": "user_approved_scope_exclusion",
                    "source_anchor_evidence": [
                        self.anchor("source.txt", 1, lines[0])
                    ],
                },
                "selected_theorem": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "inventory_role": "source_scope_exclusion",
                    "scope_disposition": "requires_source_atomization_or_dedicated_spec",
                    "source_anchor_evidence": [
                        self.anchor("source.txt", 3, lines[2])
                    ],
                },
            },
        }
        (self.folder / "audit/paper_statement_map.json").write_text(
            json.dumps(source_map)
        )
        table = coverage_template(self.folder)["result_table"]
        self.assertEqual(set(table["results"]), {"selected_theorem"})

    def test_attributed_support_is_not_a_result_but_shared_direct_owner_is(self) -> None:
        source_text = "Theorem 7. A generalization bound holds.\n"
        source = self.folder / "source.txt"
        source.write_text(source_text)
        presentations = reviewed_source_presentation_inventory(
            source_text, source_path="source.txt", source_format="text"
        ).classified
        source_sha256 = hashlib.sha256(source_text.encode()).hexdigest()
        common_anchor = self.anchor("source.txt", 1, source_text.rstrip())
        source_map = {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_sha256,
            "source_coverage_mode": "named_theoretical_statements",
            "source_named_result_inventory_review": {
                "complete": True,
                "source_artifact_sha256": source_sha256,
                "discovered_named_result_sha256": named_result_presentations_sha256(
                    presentations
                ),
            },
            "items": {
                "attributed_support": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "source_status": "support_only",
                    "inventory_role": "proof_support",
                    "source_anchor_evidence": [common_anchor],
                },
                "direct_clause": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "semantic_contract": {"spec_declaration": "Fixture.directSpec"},
                    "source_anchor_evidence": [common_anchor],
                },
            },
        }
        (self.folder / "audit/paper_statement_map.json").write_text(
            json.dumps(source_map)
        )
        table = coverage_template(self.folder)["result_table"]
        self.assertEqual(set(table["results"]), {"direct_clause"})
        self.assertEqual(
            table["source_inventory"]["results"]["direct_clause"][
                "source_item_ids"
            ],
            ["direct_clause"],
        )

    def test_shared_result_honors_each_explicit_presentation_alias_owner(self) -> None:
        source_text = (
            "Theorem 3. The first clause holds, and the second clause holds.\n\n"
            "Theorem 3. The first clause holds, and the second clause holds.\n"
        )
        source = self.folder / "source.txt"
        source.write_text(source_text)
        presentations = reviewed_source_presentation_inventory(
            source_text, source_path="source.txt", source_format="text"
        ).classified
        source_sha256 = hashlib.sha256(source_text.encode()).hexdigest()
        lines = source_text.splitlines()

        def contract() -> dict[str, str]:
            return {"spec_declaration": "Fixture.clauseSpec"}

        def alias(canonical: str) -> dict[str, object]:
            return {
                "schema": 1,
                "relation": "repeated_source_presentation",
                "label_relation": "same_visible_label",
                "canonical_source_item": canonical,
                "semantic_basis": "The proof repeats this exact theorem clause.",
                "validator": "fixture source reader",
                "validated_at": "2026-09-06T00:00:00Z",
            }

        source_map = {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_sha256,
            "source_coverage_mode": "named_theoretical_statements",
            "source_named_result_inventory_review": {
                "complete": True,
                "source_artifact_sha256": source_sha256,
                "discovered_named_result_sha256": named_result_presentations_sha256(
                    presentations
                ),
            },
            "items": {
                "first": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:1",
                    "semantic_contract": contract(),
                    "source_anchor_evidence": [self.anchor("source.txt", 1, lines[0])],
                },
                "second": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:1",
                    "semantic_contract": contract(),
                    "source_anchor_evidence": [self.anchor("source.txt", 1, lines[0])],
                },
                "second_proof": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:3",
                    "source_presentation_alias": alias("second"),
                    "source_anchor_evidence": [self.anchor("source.txt", 3, lines[2])],
                },
            },
        }
        (self.folder / "audit/paper_statement_map.json").write_text(
            json.dumps(source_map)
        )
        table = coverage_template(self.folder)["result_table"]
        self.assertEqual(set(table["results"]), {"first"})
        source_result = table["source_inventory"]["results"]["first"]
        self.assertEqual(
            source_result["source_item_ids"],
            ["first", "second", "second_proof"],
        )
        self.assertEqual(
            _portable_source_inventory_errors(
                self.folder,
                table["source_inventory"],
                table["source_inventory_sha256"],
            )[0],
            [],
        )

    def test_gfm_heading_anchor_uses_markdown_link_text_only(self) -> None:
        heading = (
            "Theorem 4: population masses and positive tolerance "
            "([Section 5, p. 7](https://example.test/main); "
            "[Appendix E, p. 39](https://example.test/appendix))"
        )
        self.assertEqual(
            _heading_anchor(heading),
            "theorem-4-population-masses-and-positive-tolerance-section-5-p-7-appendix-e-p-39",
        )
        self.assertEqual(
            _heading_anchor("Lemmas 3.4--3.5: the perturbation seam"),
            "lemmas-3435-the-perturbation-seam",
        )


if __name__ == "__main__":
    unittest.main()
