#!/usr/bin/env python3
"""Regressions for fail-closed source-record artifact publication."""

from __future__ import annotations

import ast
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from scripts import source_record_artifact_io as ARTIFACTS


ROOT = Path(__file__).resolve().parents[2]
AUDIT_PATH = ROOT / "skills/econcs-formalizer/scripts/source_record_audit.py"
ARTIFACT_PATH = ROOT / "scripts/source_record_artifact_io.py"
MOVED_NAMES = {
    "atomic_write_text_if_changed",
    "canonical_source_record_audit_path",
    "finalize_source_record_audit_output",
    "load_json_object",
    "source_record_audit_output_path",
}


class SourceRecordArtifactArchitectureTests(unittest.TestCase):
    def test_producer_imports_artifact_authority_without_duplicates(self) -> None:
        tree = ast.parse(AUDIT_PATH.read_text(encoding="utf-8"))
        definitions = {
            node.name
            for node in tree.body
            if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
        }
        self.assertTrue(MOVED_NAMES.isdisjoint(definitions))
        imported: set[str] = set()
        for node in tree.body:
            if (
                isinstance(node, ast.ImportFrom)
                and node.module == "scripts.source_record_artifact_io"
            ):
                imported.update(alias.asname or alias.name for alias in node.names)
        self.assertTrue(MOVED_NAMES <= imported)

    def test_artifact_authority_has_no_project_semantic_imports(self) -> None:
        tree = ast.parse(ARTIFACT_PATH.read_text(encoding="utf-8"))
        project_imports: list[str] = []
        for node in tree.body:
            if isinstance(node, ast.ImportFrom) and str(node.module or "").startswith("scripts"):
                project_imports.append(str(node.module))
            elif isinstance(node, ast.Import):
                project_imports.extend(
                    alias.name for alias in node.names if alias.name.startswith("scripts")
                )
        self.assertEqual(project_imports, [])


class SourceRecordAtomicWriteTests(unittest.TestCase):
    def test_generated_text_write_is_atomic_and_skips_identical_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "source_record_audit.json"
            path.write_text("old payload\n", encoding="utf-8")
            before = path.stat()

            self.assertFalse(
                ARTIFACTS.atomic_write_text_if_changed(path, "old payload\n")
            )
            unchanged = path.stat()
            self.assertEqual(unchanged.st_ino, before.st_ino)
            self.assertEqual(unchanged.st_mtime_ns, before.st_mtime_ns)

            observed: dict[str, object] = {}
            real_replace = ARTIFACTS.os.replace

            def observe_replace(source: object, destination: object) -> None:
                source_path = Path(str(source))
                destination_path = Path(str(destination))
                observed["same_directory"] = (
                    source_path.parent == destination_path.parent
                )
                observed["destination_before_replace"] = (
                    destination_path.read_text(encoding="utf-8")
                )
                observed["temporary_payload"] = source_path.read_text(
                    encoding="utf-8"
                )
                real_replace(source, destination)

            with patch.object(ARTIFACTS.os, "replace", side_effect=observe_replace):
                self.assertTrue(
                    ARTIFACTS.atomic_write_text_if_changed(path, "new payload\n")
                )

            self.assertEqual(path.read_text(encoding="utf-8"), "new payload\n")
            self.assertEqual(observed["same_directory"], True)
            self.assertEqual(
                observed["destination_before_replace"], "old payload\n"
            )
            self.assertEqual(observed["temporary_payload"], "new payload\n")
            self.assertEqual(list(path.parent.glob(f".{path.name}.*.tmp")), [])

class SourceRecordCanonicalOutputTests(unittest.TestCase):
    """The canonical cache is evidence, never a diagnostic destination."""

    def test_zero_selected_no_lean_cannot_overwrite_direct_canonical_out(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            paper_dir = root / "papers" / "Fixture"
            canonical = paper_dir / "audit" / "source_record_audit.json"
            canonical.parent.mkdir(parents=True)
            canonical.write_text('{"prior":"full-audit"}\n', encoding="utf-8")
            result = ARTIFACTS.finalize_source_record_audit_output(
                SimpleNamespace(out=str(canonical), no_lean=True),
                root,
                paper_dir,
                json.dumps(
                    {
                        "lean_check": {
                            "command": "skipped Lean check: no source-record rows or fields",
                            "returncode": 0,
                        }
                    }
                ),
                lean_returncode=0,
                has_recursion_failures=False,
            )
            self.assertEqual(result, 2)
            self.assertEqual(
                canonical.read_text(encoding="utf-8"), '{"prior":"full-audit"}\n'
            )

    def test_default_full_success_refreshes_canonical_cache_with_compact_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            paper_dir = root / "papers" / "Fixture"
            canonical = paper_dir / "audit" / "source_record_audit.json"
            canonical.parent.mkdir(parents=True)
            canonical.write_text('{"prior":"full-audit"}\n', encoding="utf-8")
            stdout = io.StringIO()
            with redirect_stdout(stdout):
                result = ARTIFACTS.finalize_source_record_audit_output(
                    SimpleNamespace(out=None, no_lean=False, stdout=False, paper="Fixture"),
                    root,
                    paper_dir,
                    '{"new":"full-audit"}',
                    lean_returncode=0,
                    has_recursion_failures=False,
                )
            self.assertEqual(result, 0)
            self.assertIn('"canonical_refreshed": true', stdout.getvalue())
            self.assertNotIn('"new":"full-audit"', stdout.getvalue())
            self.assertEqual(
                canonical.read_text(encoding="utf-8"), '{"new":"full-audit"}\n'
            )

    def test_explicit_stdout_full_success_leaves_canonical_cache_unchanged(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            paper_dir = root / "papers" / "Fixture"
            canonical = paper_dir / "audit" / "source_record_audit.json"
            canonical.parent.mkdir(parents=True)
            canonical.write_text('{"prior":"full-audit"}\n', encoding="utf-8")
            stdout = io.StringIO()
            with redirect_stdout(stdout):
                result = ARTIFACTS.finalize_source_record_audit_output(
                    SimpleNamespace(out=None, no_lean=False, stdout=True, paper="Fixture"),
                    root,
                    paper_dir,
                    '{"new":"full-audit"}',
                    lean_returncode=0,
                    has_recursion_failures=False,
                )
            self.assertEqual(result, 0)
            self.assertIn('"new":"full-audit"', stdout.getvalue())
            self.assertEqual(
                canonical.read_text(encoding="utf-8"), '{"prior":"full-audit"}\n'
            )

    def test_recursion_failure_cannot_replace_canonical_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            paper_dir = root / "papers" / "Fixture"
            canonical = paper_dir / "audit" / "source_record_audit.json"
            canonical.parent.mkdir(parents=True)
            canonical.write_text('{"prior":"full-audit"}\n', encoding="utf-8")

            result = ARTIFACTS.finalize_source_record_audit_output(
                SimpleNamespace(out=str(canonical), no_lean=False),
                root,
                paper_dir,
                '{"new":"incomplete"}',
                lean_returncode=0,
                has_recursion_failures=True,
            )

            self.assertEqual(result, 3)
            self.assertEqual(
                canonical.read_text(encoding="utf-8"), '{"prior":"full-audit"}\n'
            )

    def test_frozen_input_change_cannot_replace_canonical_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            paper_dir = root / "papers" / "Fixture"
            canonical = paper_dir / "audit" / "source_record_audit.json"
            canonical.parent.mkdir(parents=True)
            canonical.write_text('{"prior":"full-audit"}\n', encoding="utf-8")

            result = ARTIFACTS.finalize_source_record_audit_output(
                SimpleNamespace(out=str(canonical), no_lean=False),
                root,
                paper_dir,
                '{"new":"raced"}',
                lean_returncode=0,
                has_recursion_failures=False,
                input_change_during_scan_error="paper source changed during scan",
            )

            self.assertEqual(result, 4)
            self.assertEqual(
                canonical.read_text(encoding="utf-8"), '{"prior":"full-audit"}\n'
            )

    def test_failed_lean_writes_only_noncanonical_diagnostic(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            paper_dir = root / "papers" / "Fixture"
            canonical = paper_dir / "audit" / "source_record_audit.json"
            canonical.parent.mkdir(parents=True)
            canonical.write_text('{"prior":"full-audit"}\n', encoding="utf-8")
            diagnostic = root / "diagnostic.json"
            result = ARTIFACTS.finalize_source_record_audit_output(
                SimpleNamespace(out=str(diagnostic), no_lean=False),
                root,
                paper_dir,
                '{"lean_check":{"returncode":1}}',
                lean_returncode=1,
                has_recursion_failures=False,
            )
            self.assertEqual(result, 2)
            self.assertEqual(
                diagnostic.read_text(encoding="utf-8"),
                '{"lean_check":{"returncode":1}}\n',
            )
            self.assertEqual(
                canonical.read_text(encoding="utf-8"), '{"prior":"full-audit"}\n'
            )


if __name__ == "__main__":
    unittest.main()
