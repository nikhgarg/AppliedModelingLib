"""CI dispatch must preserve strict graph validation and legacy audit failures."""

from __future__ import annotations

import contextlib
import io
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import audit_statement_coverage as gate


ROOT = Path(__file__).resolve().parents[2]
FOLDER = ROOT / "papers" / "ExamplePaper"


class StatementCoverageGateTests(unittest.TestCase):
    def test_valid_graph_revalidates_exact_inputs_without_dashboard_reconstruction(self):
        warning = gate.audit_evidence_integrity.Finding(
            "WARN", FOLDER.name, "status.json", "human review pending"
        )
        for kind in ("statement", "coverage"):
            for require_bytes in (True, False):
                with self.subTest(kind=kind, require_bytes=require_bytes), patch.object(
                    gate.audit_evidence_integrity,
                    "graph_native_closure_fast_path_findings", return_value=[warning],
                ) as validate, patch.object(
                    gate.review_dashboard, "print_statement_audit_status",
                ) as statement, patch.object(
                    gate.review_dashboard, "print_paper_coverage_audit_status",
                ) as coverage, contextlib.redirect_stdout(io.StringIO()) as output:
                    self.assertFalse(gate.audit_paper(FOLDER, kind, require_source_bytes=require_bytes))
                validate.assert_called_once_with(
                    FOLDER, release=False, require_source_bytes=require_bytes,
                )
                statement.assert_not_called()
                coverage.assert_not_called()
                self.assertIn("human review pending", output.getvalue())

    def test_invalid_selected_graph_cannot_fall_back_to_passing_legacy_rows(self):
        error = gate.audit_evidence_integrity.Finding(
            "ERROR", FOLDER.name, "receipt", "source/Lean binding differs"
        )
        for kind in ("statement", "coverage"):
            with self.subTest(kind=kind), patch.object(
                gate.audit_evidence_integrity,
                "graph_native_closure_fast_path_findings", return_value=[error],
            ), patch.object(gate.review_dashboard, "print_statement_audit_status") as statement, patch.object(
                gate.review_dashboard, "print_paper_coverage_audit_status",
            ) as coverage, contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertTrue(gate.audit_paper(FOLDER, kind))
            statement.assert_not_called()
            coverage.assert_not_called()
            self.assertIn("source/Lean binding differs", output.getvalue())

    def test_unselected_graph_retains_both_legacy_gate_outcomes(self):
        for kind, target in (
            ("statement", "print_statement_audit_status"),
            ("coverage", "print_paper_coverage_audit_status"),
        ):
            for failure in (False, True):
                with self.subTest(kind=kind, failure=failure), patch.object(
                    gate.audit_evidence_integrity,
                    "graph_native_closure_fast_path_findings", return_value=None,
                ), patch.object(gate.review_dashboard, target, return_value=failure) as legacy:
                    self.assertEqual(gate.audit_paper(FOLDER, kind), failure)
                legacy.assert_called_once_with(FOLDER.name)

    def test_cli_preserves_paper_selection_strict_default_and_failed_exit(self):
        for extra in ([], ["--allow-missing-source-bytes"]):
            with self.subTest(extra=extra), patch.object(
                gate.review_dashboard, "iter_paper_folders", return_value=[FOLDER],
            ) as select, patch.object(gate, "audit_paper", return_value=True) as audit, contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(gate.main(["--kind", "coverage", "--paper", FOLDER.name, *extra]), 1)
            select.assert_called_once_with(FOLDER.name)
            audit.assert_called_once_with(FOLDER, "coverage", require_source_bytes=not extra)

    def test_exception_blocks_and_remaining_papers_are_checked(self):
        folders = [FOLDER, FOLDER.with_name("SecondPaper")]
        with patch.object(gate.review_dashboard, "iter_paper_folders", return_value=folders), patch.object(
            gate, "audit_paper", side_effect=[ValueError("invalid credential"), False],
        ) as audit, contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(gate.main(["--kind", "statement"]), 1)
        self.assertEqual(audit.call_count, 2)
        self.assertIn("invalid credential", output.getvalue())

    def test_empty_selection_is_not_success(self):
        with patch.object(gate.review_dashboard, "iter_paper_folders", return_value=[]), contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as error:
                gate.main(["--kind", "statement", "--paper", "MissingPaper"])
        self.assertEqual(error.exception.code, 2)

    def test_direct_cli_starts_from_unrelated_directory_without_pythonpath(self):
        environment = dict(os.environ)
        environment.pop("PYTHONPATH", None)
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run(
                [sys.executable, str(ROOT / "scripts/audit_statement_coverage.py"), "--help"],
                cwd=directory, env=environment, capture_output=True, text=True, timeout=30,
            )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_actual_workflow_commands_use_public_override_only_in_public_mode(self):
        workflow = (ROOT / ".github/workflows/lean_action_ci.yml").read_text()
        for name, kind in (("Audit statement translations", "statement"), ("Audit paper coverage", "coverage")):
            step = workflow.split(f"      - name: {name}\n", 1)[1].split("      - name:", 1)[0]
            body = step.split("        run: |\n", 1)[1]
            body = "\n".join(line[10:] for line in body.splitlines())
            for mode in ("true", "false", "", "unexpected"):
                with self.subTest(kind=kind, mode=mode):
                    result = subprocess.run(
                        ["bash", "-c", "python3() { printf '%s\\n' \"$@\"; }\n" + body],
                        env=dict(os.environ, PUBLIC_SOURCE_MODE=mode), capture_output=True, text=True, check=True,
                    )
                    expected = ["scripts/audit_statement_coverage.py", "--kind", kind]
                    if mode == "true":
                        expected.append("--allow-missing-source-bytes")
                    self.assertEqual(result.stdout.splitlines(), expected)


if __name__ == "__main__":
    unittest.main()
