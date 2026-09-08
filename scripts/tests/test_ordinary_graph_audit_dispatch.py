"""Ordinary CI validates recorded graphs without replaying private producers."""

import json
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from scripts import audit_evidence_integrity as evidence
from scripts import audit_repository as audit
from scripts import closeout_document_gates as documents
from scripts.repository_check_registry import ordinary_repository_checks


class OrdinaryGraphAuditTests(unittest.TestCase):
    def setUp(self):
        self.stack = ExitStack()
        self.addCleanup(self.stack.close)
        self.root = Path(self.stack.enter_context(tempfile.TemporaryDirectory()))
        self.folder = self.root / "papers" / "AB24Example"
        self.folder.mkdir(parents=True)
        self.stack.enter_context(patch.object(audit, "ROOT", self.root))
        self.stack.enter_context(patch.object(audit, "PAPERS", self.root / "papers"))
        self.stack.enter_context(patch.object(audit, "PAPER_STATUS_FILE", self.root / "papers/status.json"))
        self.stack.enter_context(patch.object(audit, "paper_dirs", return_value=[self.folder]))
        self.stack.enter_context(patch.object(audit, "ACTIVE_PAPERS", set()))

    def registry(self, require_source_bytes=True):
        return {check.name: check for check in ordinary_repository_checks(
            audit, include_active=True, strict_style=False,
            library_premise_audit=False, paper_filter=None,
            require_source_bytes=require_source_bytes, deep_paper_prose=False,
        )}

    def status(self, **updates):
        entry = {
            "id": self.folder.name, "title": "Example", "source_version": "v1",
            "build_target": self.folder.name, "status": "formalized",
            "review_entrypoint": "review-dashboard.sh",
            "human_review": {"reviewed_rows": 0, "total_rows": 1, "stale_rows": 0, "mismatch_rows": 0},
        }
        entry.update(updates)
        (self.folder / "status.json").write_text(json.dumps(entry), encoding="utf-8")
        audit.PAPER_STATUS_FILE.write_text(json.dumps({"schema": 1, "papers": [entry]}), encoding="utf-8")
        return entry

    def test_canonical_errors_block_and_selected_graphs_never_fall_back(self):
        error = evidence.Finding("ERROR", self.folder.name, "papers/AB24Example/audit/receipt.json", "invalid current graph")
        for require_source in (True, False):
            with self.subTest(require_source=require_source), patch.object(
                evidence, "graph_native_closure_fast_path_findings", return_value=[error],
            ) as validator, patch.object(audit, "check_machine_paper_status", return_value=[]) as machine:
                checks = self.registry(require_source)
                findings = checks["graph_native_paper_closure"].run()
                self.assertEqual([(f.severity, f.message) for f in findings], [("ERROR", "invalid current graph")])
                checks["machine_paper_status"].run()
                self.assertEqual(machine.call_args.kwargs["graph_native_papers"], {self.folder.name})
                validator.assert_called_once_with(self.folder, release=False, require_source_bytes=require_source)

    def test_legacy_papers_are_not_selected_and_selection_does_not_leak_between_runs(self):
        with patch.object(evidence, "graph_native_closure_fast_path_findings", return_value=[]), patch.object(
            audit, "check_machine_paper_status", return_value=[],
        ) as machine:
            first = self.registry()
            first["graph_native_paper_closure"].run()
            first["machine_paper_status"].run()
            self.assertEqual(machine.call_args.kwargs["graph_native_papers"], {self.folder.name})
            with patch.object(evidence, "graph_native_closure_fast_path_findings", return_value=None):
                first["graph_native_paper_closure"].run()
            first["machine_paper_status"].run()
            self.assertEqual(machine.call_args.kwargs["graph_native_papers"], set())
            second = self.registry()
            with patch.object(evidence, "graph_native_closure_fast_path_findings", return_value=None):
                second["graph_native_paper_closure"].run()
            second["machine_paper_status"].run()
            self.assertEqual(machine.call_args.kwargs["graph_native_papers"], set())

    def test_only_explicit_public_mode_uses_recorded_public_document_inputs(self):
        for require_source in (True, False):
            with self.subTest(require_source=require_source), patch.object(
                evidence, "graph_native_closure_fast_path_findings", return_value=[],
            ), patch.object(audit, "check_dag_and_validation_report_closeout", return_value=[]) as document_check:
                checks = self.registry(require_source)
                checks["graph_native_paper_closure"].run()
                checks["dag_and_validation_report_closeout"].run()
                selected = document_check.call_args.kwargs["public_graph_papers"]
                self.assertEqual(set(selected), set() if require_source else {self.folder.name})

    def test_selected_graph_skips_legacy_reconstruction_but_keeps_basic_status_validation(self):
        self.status()
        with patch.object(audit, "current_author_approved_corrected_scope", side_effect=AssertionError("legacy replay")):
            self.assertEqual(audit.check_machine_paper_status(graph_native_papers={self.folder.name}), [])
            self.status(title="")
            findings = audit.check_machine_paper_status(graph_native_papers={self.folder.name})
            self.assertTrue(any(f.severity == "ERROR" and "missing `title`" in f.message for f in findings))
            self.status(human_summary_review={"status": "human_approved"})
            findings = audit.check_machine_paper_status(graph_native_papers={self.folder.name})
            self.assertTrue(any(f.severity == "ERROR" and "no `human_summary`" in f.message for f in findings))

    def test_unfinished_papers_keep_existing_validation(self):
        self.status(status="in progress", paper_interface={}, review_surface={})
        with patch.object(audit, "current_author_approved_corrected_scope", side_effect=RuntimeError("legacy gate reached")):
            with self.assertRaisesRegex(RuntimeError, "legacy gate reached"):
                audit.check_machine_paper_status(graph_native_papers=set())

    def test_transitive_interface_import_is_allowed_but_missing_export_still_blocks(self):
        self.status()
        (self.folder / "PaperInterface.lean").write_text("def exampleSpec : Prop := True\n", encoding="utf-8")
        (self.folder / "ProofInterface.lean").write_text("import AB24Example.PaperInterface\n", encoding="utf-8")
        self.folder.with_suffix(".lean").write_text("import AB24Example.ProofInterface\n", encoding="utf-8")
        findings = audit.check_post_paper_audit_interfaces(True)
        self.assertFalse(any(f.severity == "ERROR" for f in findings), findings)
        (self.folder / "ProofInterface.lean").write_text("-- import AB24Example.PaperInterface\n", encoding="utf-8")
        findings = audit.check_post_paper_audit_interfaces(True)
        self.assertTrue(any(f.severity == "ERROR" and "through its imports" in f.message for f in findings))

    def test_authenticated_source_definitions_are_not_rejected_by_legacy_tuple_heuristic(self):
        self.status()
        (self.folder / "PaperInterface.lean").write_text("def exampleSpec : (Nat → Prop) × (Nat → Prop) := (fun _ => True, fun _ => True)\n", encoding="utf-8")
        self.folder.with_suffix(".lean").write_text("import AB24Example.PaperInterface\n", encoding="utf-8")
        self.assertTrue(any("tuple/prod" in f.message for f in audit.check_post_paper_audit_interfaces(True)))
        self.assertFalse(any("tuple/prod" in f.message for f in audit.check_post_paper_audit_interfaces(True, graph_native_papers={self.folder.name})))

    def test_public_documents_still_require_packet_artifacts_and_valid_report_sections(self):
        docs = self.folder / "docs"
        docs.mkdir()
        (self.folder / "FINAL_VALIDATION_REPORT.md").write_text("# Report\n", encoding="utf-8")
        with patch.object(documents, "final_report_section_errors", return_value=["required report section absent"]), patch.object(
            documents, "reader_facing_result_label_errors", return_value=[],
        ), patch.object(documents, "current_approved_review_context_report_errors", return_value=[]), patch.object(
            documents, "report_memo_coverage_errors", side_effect=AssertionError("private memo evidence"),
        ), patch.object(documents, "current_human_review_packet_errors", side_effect=AssertionError("private cache")):
            errors = documents.closeout_document_hard_errors(
                self.folder, corrected_scope_current=False, check_final_holistic=False,
                require_visual_dag_inspection=True, check_private_review_artifacts=False,
            )
            self.assertTrue(any("required report section absent" in error.message for error in errors))
            self.assertEqual(sum("published human-review packet" in error.message for error in errors), 2)
            for suffix in ("pdf", "tex"):
                (docs / f"HUMAN_REVIEW_PACKET.{suffix}").write_text("published artifact", encoding="utf-8")
            errors = documents.closeout_document_hard_errors(
                self.folder, corrected_scope_current=False, check_final_holistic=False,
                require_visual_dag_inspection=True, check_private_review_artifacts=False,
            )
            self.assertFalse(any("published human-review packet" in error.message for error in errors))

    def test_default_document_gate_still_checks_private_review_inputs(self):
        with patch.object(documents, "report_memo_coverage_errors", return_value=["missing private coverage"]) as coverage, patch.object(
            documents, "current_human_review_packet_errors", return_value=["missing private cache"],
        ) as packet, patch.object(documents, "final_holistic_audit_hard_errors", return_value=[]) as holistic:
            errors = documents.closeout_document_hard_errors(self.folder, corrected_scope_current=False, require_visual_dag_inspection=True)
            self.assertTrue(any("missing private coverage" in error.message for error in errors))
            self.assertTrue(any("missing private cache" in error.message for error in errors))
            coverage.assert_called_once()
            packet.assert_called_once()
            holistic.assert_called_once()


if __name__ == "__main__":
    unittest.main()
