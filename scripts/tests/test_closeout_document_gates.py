#!/usr/bin/env python3
"""Regression tests for shared strict/planner closeout document gates."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.closeout_document_gates import (
    closeout_document_hard_errors,
    final_holistic_audit_hard_errors,
)


class CloseoutDocumentGateTests(unittest.TestCase):
    def test_reader_structure_and_numbering_are_terminal_only(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            self._write_valid_source_audit(folder)
            (folder / "source_tex").mkdir()
            (folder / "source_tex/main.tex").write_text(
                r"\begin{theorem}\label{thm:raw-name}Claim.\end{theorem}",
                encoding="utf-8",
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "## 1. Human Verdict\nTheorem `raw-name` is checked.\n",
                encoding="utf-8",
            )
            early = closeout_document_hard_errors(
                folder, corrected_scope_current=False
            )
            terminal = closeout_document_hard_errors(
                folder, corrected_scope_current=False,
                require_visual_dag_inspection=True,
            )
        self.assertFalse(any("raw TeX label" in error.message for error in early))
        self.assertFalse(any("numbered sections" in error.message for error in early))
        self.assertTrue(any("raw TeX label" in error.message for error in terminal))
        self.assertTrue(any("missing" in error.message and "section" in error.message
                            for error in terminal))

    def test_saved_reviewer_prompt_pass_block_satisfies_document_gate(self) -> None:
        root = Path(__file__).resolve().parents[2]
        prompt = (
            root / "skills/econcs-formalizer/templates/FINAL_ADVERSARIAL_SOURCE_AUDIT_PROMPT.md"
        ).read_text(encoding="utf-8")
        target = "a" * 64
        pass_block = "\n".join(
            line[4:].replace("<SURFACE_SHA256>", target)
            for line in prompt.splitlines()
            if line.startswith("    ")
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "docs").mkdir()
            (folder / "docs/AGENT_SOURCE_AUDIT.md").write_text(
                pass_block + "\n", encoding="utf-8"
            )
            self.assertEqual(
                final_holistic_audit_hard_errors(
                    folder, target_surface_identity=target
                ),
                [],
            )

    def _write_valid_source_audit(self, folder: Path, *, target: str = "") -> None:
        docs = folder / "docs"
        docs.mkdir(parents=True, exist_ok=True)
        (docs / "AGENT_SOURCE_AUDIT.md").write_text(
            "## Overall status: PASS\n"
            + (
                f"- Reviewed final holistic audit surface identity: `{target}`\n"
                "- Final audit scope: `complete_current_surface`\n"
                if target
                else ""
            )
            + "This independent source-first review does not merely summarize existing "
            "sidecars. It builds a source inventory from the source itself and compares "
            "the Lean interface for omissions, hidden strengthening/weakening, and "
            "semantic mismatches.\n",
            encoding="utf-8",
        )

    def test_missing_or_incomplete_source_audit_is_a_hard_error(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            missing = closeout_document_hard_errors(
                folder, corrected_scope_current=False
            )
            self.assertEqual(len(missing), 1)
            self.assertIn("missing `docs/AGENT_SOURCE_AUDIT.md`", missing[0].message)

            self._write_valid_source_audit(folder)
            source_audit = folder / "docs" / "AGENT_SOURCE_AUDIT.md"
            source_audit.write_text(
                "## Overall status: NEEDS REVIEW\n", encoding="utf-8"
            )
            incomplete = closeout_document_hard_errors(
                folder, corrected_scope_current=False
            )
            self.assertTrue(
                any("Overall status: PASS" in error.message for error in incomplete)
            )

            source_audit.write_text(
                "## Overall status: PASS\n"
                "NEEDS AGENT REVIEW: scaffold has not performed the source read.\n",
                encoding="utf-8",
            )
            scaffold = closeout_document_hard_errors(
                folder, corrected_scope_current=False
            )
            self.assertTrue(any("still a scaffold" in error.message for error in scaffold))

    def test_overall_verdicts_must_agree_without_matching_finding_prose(self) -> None:
        target = "a" * 64
        for historical in (False, True):
            for statuses, accepted in (
                ([], False),
                (["PASS"], True),
                (["PASS", "PASS"], True),
                (["PASS", "FAIL"], False),
                (["FAIL", "PASS"], False),
                (["PASS", "NEEDS REVIEW"], False),
                (["PASS", ""], False),
            ):
                with self.subTest(historical=historical, statuses=statuses):
                    report = "".join(
                        f"## Overall status: {status}\n" for status in statuses
                    )
                    report += (
                        f"- Reviewed final holistic audit surface identity: `{target}`\n"
                    )
                    if not historical:
                        report += "- Final audit scope: `complete_current_surface`\n"
                    report += (
                        "### Finding 1\nStatus: FAIL in the initial review, now resolved.\n"
                        "## Finding status: FAIL\n"
                        "The earlier Overall status: FAIL is discussed here as prose.\n"
                    )
                    with mock.patch.object(Path, "is_file", return_value=True), \
                            mock.patch.object(Path, "read_text", return_value=report):
                        errors = final_holistic_audit_hard_errors(
                            Path("/in-memory"), target_surface_identity=target,
                            allow_historical_missing_scope=historical,
                        )
                    self.assertEqual(errors == [], accepted, errors)

    def test_terminal_audit_uses_identity_not_canned_prose(self) -> None:
        """A fresh review is substantive evidence, not a phrase-matching exercise."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            target = "a" * 64
            docs = folder / "docs"
            docs.mkdir()
            (docs / "AGENT_SOURCE_AUDIT.md").write_text(
                "## Overall status: PASS\n"
                f"- Reviewed final holistic audit surface identity: `{target}`\n"
                "- Final audit scope: `complete_current_surface`\n"
                "I reread the pinned source, reconstructed its selected theory "
                "surface, and compared it against the current Lean claims.\n",
                encoding="utf-8",
            )

            self.assertEqual(
                final_holistic_audit_hard_errors(
                    folder, target_surface_identity=target
                ),
                [],
            )

    def test_terminal_audit_rejects_a_bounded_recheck_attestation(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            target = "a" * 64
            docs = folder / "docs"
            docs.mkdir()
            (docs / "AGENT_SOURCE_AUDIT.md").write_text(
                "## Overall status: PASS\n"
                f"- Reviewed final holistic audit surface identity: `{target}`\n"
                "- Final audit scope: `bounded_repair_recheck`\n",
                encoding="utf-8",
            )

            errors = final_holistic_audit_hard_errors(
                folder, target_surface_identity=target
            )

        self.assertTrue(
            any("complete_current_surface" in error.message for error in errors),
            errors,
        )

    def test_historical_report_reader_preserves_exact_target_and_pass(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "docs").mkdir()
            target = "a" * 64
            report = folder / "docs/AGENT_SOURCE_AUDIT.md"
            report.write_text(
                "## Overall status: PASS\n"
                f"- Reviewed final holistic audit surface identity: `{target}`\n"
                "The independent audit reviewed the complete pinned source surface.\n",
                encoding="utf-8",
            )
            self.assertEqual(final_holistic_audit_hard_errors(
                folder, target_surface_identity=target,
                allow_historical_missing_scope=True,
            ), [])
            self.assertTrue(final_holistic_audit_hard_errors(
                folder, target_surface_identity=target,
            ))
            self.assertTrue(final_holistic_audit_hard_errors(
                folder, target_surface_identity="b" * 64,
                allow_historical_missing_scope=True,
            ))
            report.write_text(
                report.read_text(encoding="utf-8").replace("PASS", "NEEDS REVIEW"),
                encoding="utf-8",
            )
            self.assertTrue(final_holistic_audit_hard_errors(
                folder, target_surface_identity=target,
                allow_historical_missing_scope=True,
            ))

    def test_explicit_noncomplete_or_conflicting_scope_never_reads_as_legacy(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "docs").mkdir()
            target = "a" * 64
            for scope in (
                "- Final audit scope: `bounded_repair_recheck`\n",
                "- Final audit scope: `unknown_scope`\n",
                "Final audit scope: `bounded_repair_recheck`\n",
                "- Final audit scope:\n",
                "- Final audit scope: `complete_current_surface`\n"
                "- Final audit scope: `bounded_repair_recheck`\n",
            ):
                for legacy in (False, True):
                    with self.subTest(scope=scope, legacy=legacy):
                        (folder / "docs/AGENT_SOURCE_AUDIT.md").write_text(
                            "## Overall status: PASS\n"
                            f"- Reviewed final holistic audit surface identity: `{target}`\n"
                            + scope,
                            encoding="utf-8",
                        )
                        self.assertTrue(final_holistic_audit_hard_errors(
                            folder, target_surface_identity=target,
                            allow_historical_missing_scope=legacy,
                        ))

    def test_terminal_documents_reject_a_stale_human_review_packet(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "## DAG Audit\nThe rendered DAG was visually inspected.\n",
                encoding="utf-8",
            )
            with mock.patch(
                "scripts.closeout_document_gates.current_human_review_packet_errors",
                return_value=("docs/HUMAN_REVIEW_PACKET.tex: stale relative to the current graph",),
            ):
                errors = closeout_document_hard_errors(
                    folder,
                    corrected_scope_current=False,
                    check_final_holistic=False,
                    require_visual_dag_inspection=True,
                )

        self.assertTrue(
            any("human-review packet" in error.message for error in errors),
            errors,
        )

    def test_legacy_source_audit_does_not_acquire_current_plan_binding(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            self._write_valid_source_audit(folder)

            self.assertEqual(
                closeout_document_hard_errors(
                    folder,
                    corrected_scope_current=False,
                    final_holistic_required=False,
                    final_holistic_surface_sha256="d" * 64,
                ),
                [],
            )

    def test_semantic_preparation_can_defer_only_the_final_holistic_gate(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            errors = closeout_document_hard_errors(
                folder,
                corrected_scope_current=False,
                final_holistic_required=True,
                check_final_holistic=False,
            )
            self.assertEqual(errors, [])

    def test_final_holistic_audit_binds_exact_semantic_surface_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            target = "a" * 64
            self._write_valid_source_audit(folder, target="b" * 64)

            stale = final_holistic_audit_hard_errors(
                folder, target_surface_identity=target
            )
            self.assertEqual(len(stale), 1)
            self.assertIn("audit surface identity", stale[0].message)

            self._write_valid_source_audit(folder, target=target)
            self.assertEqual(
                final_holistic_audit_hard_errors(
                    folder, target_surface_identity=target
                ),
                [],
            )

    def test_policy_aware_final_audit_requires_the_frozen_panel_contract(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            target = "a" * 64
            self._write_valid_source_audit(folder, target=target)
            errors = final_holistic_audit_hard_errors(
                folder,
                target_surface_identity=target,
                review_policy_assurance={
                    "schema": 1,
                    "source_scope": "all_named_theory",
                    "repeat_final_scope": "main_primary",
                    "required_final_adversary_count": 1,
                },
            )

        self.assertEqual(len(errors), 1)
        self.assertIn("FINAL_ADVERSARIAL_REVIEW_PANEL.json", errors[0].message)

    def test_historical_plan_binding_remains_valid_until_recloseout(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            docs = folder / "docs"
            docs.mkdir(parents=True)
            (docs / "AGENT_SOURCE_AUDIT.md").write_text(
                "## Overall status: PASS\n"
                f"- Reviewed closeout plan identity: `{'a' * 64}`\n"
                "This independent source-first review does not merely summarize "
                "existing sidecars. It builds a source inventory from the source "
                "itself and compares the Lean interface for omissions, hidden "
                "strengthening/weakening, and semantic mismatches.\n",
                encoding="utf-8",
            )

            self.assertEqual(
                final_holistic_audit_hard_errors(
                    folder,
                    require_surface_binding=True,
                ),
                [],
            )
            errors = final_holistic_audit_hard_errors(
                folder,
                target_surface_identity="b" * 64,
            )
            self.assertTrue(
                any("exact current final holistic audit surface" in error.message for error in errors)
            )

    def test_current_corrected_scope_exempts_only_source_audit_requirement(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "TODO\n", encoding="utf-8"
            )

            errors = closeout_document_hard_errors(
                folder, corrected_scope_current=True
            )

            self.assertEqual(len(errors), 1)
            self.assertEqual(errors[0].path, folder / "FINAL_VALIDATION_REPORT.md")
            self.assertIn("stale placeholder", errors[0].message)

    def test_current_v11_requires_final_holistic_audit_despite_corrected_scope(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()

            errors = closeout_document_hard_errors(
                folder,
                corrected_scope_current=True,
                final_holistic_required=True,
            )

            self.assertEqual(len(errors), 1)
            self.assertIn("missing `docs/AGENT_SOURCE_AUDIT.md`", errors[0].message)

            (folder / "docs").mkdir()
            (folder / "docs" / "AGENT_SOURCE_AUDIT.md").write_text(
                "## Overall status: PASS\nHistorical corrected-scope note only.\n",
                encoding="utf-8",
            )
            incomplete = closeout_document_hard_errors(
                folder,
                corrected_scope_current=True,
                final_holistic_required=True,
            )
            self.assertTrue(
                any(
                    "final-audit identity binding" in error.message
                    for error in incomplete
                )
            )

            target = "c" * 64
            self._write_valid_source_audit(folder, target=target)
            self.assertEqual(
                closeout_document_hard_errors(
                    folder,
                    corrected_scope_current=True,
                    final_holistic_required=True,
                    final_holistic_surface_sha256=target,
                ),
                [],
            )

    def test_post_audit_placeholder_is_a_hard_error(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            self._write_valid_source_audit(folder)
            (folder / "docs" / "POST_FORMALIZATION_AUDIT.md").write_text(
                "- Not run.\n", encoding="utf-8"
            )

            errors = closeout_document_hard_errors(
                folder, corrected_scope_current=False
            )

            self.assertEqual(len(errors), 1)
            self.assertIn("post-formalization audit", errors[0].message)

    @mock.patch(
        "scripts.closeout_document_gates.current_human_review_packet_errors",
        return_value=(),
    )
    @mock.patch("scripts.closeout_document_gates.report_memo_coverage_errors", return_value=())
    def test_visual_dag_evidence_is_required_only_at_terminal_boundary(
        self, _memo_errors: mock.Mock, _packet_errors: mock.Mock
    ) -> None:
        def complete_report(dag_text: str) -> str:
            return "\n".join(
                f"## {number}. DAG Audit\n{dag_text}\n" if number == 16 else
                f"## {number}. Report section\nAssessed content.\n"
                for number in range(1, 22)
            )

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            report = folder / "FINAL_VALIDATION_REPORT.md"
            report.write_text(
                complete_report("The dependency graph was rendered successfully."),
                encoding="utf-8",
            )

            self.assertEqual(
                closeout_document_hard_errors(
                    folder,
                    corrected_scope_current=False,
                    check_final_holistic=False,
                ),
                [],
            )
            missing = closeout_document_hard_errors(
                folder,
                corrected_scope_current=False,
                check_final_holistic=False,
                require_visual_dag_inspection=True,
            )
            self.assertEqual(len(missing), 1)
            self.assertIn("visual inspection", missing[0].message)

            report.write_text(
                "## Source Notes\nThe source PDF was visually inspected.\n"
                + complete_report("The dependency graph was rendered successfully."),
                encoding="utf-8",
            )
            misplaced = closeout_document_hard_errors(
                folder,
                corrected_scope_current=False,
                check_final_holistic=False,
                require_visual_dag_inspection=True,
            )
            self.assertEqual(len(misplaced), 1)
            self.assertIn("DAG Audit", misplaced[0].message)

            report.write_text(
                complete_report("The rendered PDF was visually inspected for readability and overlap."),
                encoding="utf-8",
            )
            self.assertEqual(
                closeout_document_hard_errors(
                    folder,
                    corrected_scope_current=False,
                    check_final_holistic=False,
                    require_visual_dag_inspection=True,
                ),
                [],
            )

    def test_memo_coverage_blocks_terminal_documents_without_blocking_semantic_intake(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            with (
                mock.patch("scripts.closeout_document_gates.report_memo_coverage_errors",
                           return_value=("material clarification has no linked memo",)) as coverage,
                mock.patch("scripts.closeout_document_gates.current_human_review_packet_errors",
                           return_value=()),
            ):
                early = closeout_document_hard_errors(
                    folder, corrected_scope_current=False, check_final_holistic=False,
                )
                self.assertEqual(early, [])
                coverage.assert_not_called()
                terminal = closeout_document_hard_errors(
                    folder, corrected_scope_current=False, check_final_holistic=False,
                    require_visual_dag_inspection=True,
                )
                coverage.assert_called_once_with(
                    folder,
                    expected_all_selected_semantic_review_sha256=None,
                )
                self.assertEqual(len(terminal), 1)
                self.assertEqual(terminal[0].path, folder / "docs/REPORT_MEMO_COVERAGE.json")
                self.assertIn("material clarification", terminal[0].message)

    def test_terminal_document_gate_compares_plan_bound_semantic_basis(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            with (
                mock.patch(
                    "scripts.closeout_document_gates.report_memo_coverage_errors",
                    return_value=(),
                ) as coverage,
                mock.patch(
                    "scripts.closeout_document_gates.current_human_review_packet_errors",
                    return_value=(),
                ),
                mock.patch(
                    "scripts.closeout_document_gates.final_holistic_audit_hard_errors",
                    return_value=[],
                ),
            ):
                closeout_document_hard_errors(
                    folder,
                    corrected_scope_current=False,
                    final_holistic_required=True,
                    check_final_holistic=False,
                    require_visual_dag_inspection=True,
                    all_selected_semantic_review_sha256="d" * 64,
                )

            coverage.assert_called_once_with(
                folder,
                expected_all_selected_semantic_review_sha256="d" * 64,
            )

    def test_strict_can_supply_a_legacy_post_audit_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            self._write_valid_source_audit(folder)
            legacy_post_audit = folder / "POST_FORMALIZATION_AUDIT.md"
            legacy_post_audit.write_text("TODO\n", encoding="utf-8")

            errors = closeout_document_hard_errors(
                folder,
                corrected_scope_current=False,
                post_formalization_audit=legacy_post_audit,
            )

            self.assertEqual(len(errors), 1)
            self.assertEqual(errors[0].path, legacy_post_audit)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
