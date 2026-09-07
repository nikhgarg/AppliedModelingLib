#!/usr/bin/env python3
"""Architecture regressions for the source-record operational runtime."""

from __future__ import annotations

import ast
from contextlib import redirect_stderr
import fcntl
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from scripts import source_record_runtime as RUNTIME


ROOT = Path(__file__).resolve().parents[2]
AUDIT_PATH = ROOT / "skills/econcs-formalizer/scripts/source_record_audit.py"
RUNTIME_PATH = ROOT / "scripts/source_record_runtime.py"
MOVED_NAMES = {
    "CapturedSubprocessResult",
    "SourceRecordAuditLockUnavailable",
    "run_source_record_subprocess",
    "source_record_audit_lock",
    "source_record_audit_lock_path",
    "source_record_audit_lock_status",
    "source_record_progress",
    "source_record_progress_phase",
    "structural_scan_progress_summary",
}
CONSUMED_RUNTIME_NAMES = MOVED_NAMES - {
    "CapturedSubprocessResult",
    "source_record_audit_lock_path",
}


class SourceRecordRuntimeArchitectureTests(unittest.TestCase):
    def test_semantic_producer_imports_runtime_without_duplicate_definitions(self) -> None:
        tree = ast.parse(AUDIT_PATH.read_text(encoding="utf-8"))
        local_definitions = {
            node.name
            for node in tree.body
            if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
        }
        self.assertTrue(MOVED_NAMES.isdisjoint(local_definitions))
        imported: set[str] = set()
        for node in tree.body:
            if (
                isinstance(node, ast.ImportFrom)
                and node.module == "scripts.source_record_runtime"
            ):
                imported.update(alias.asname or alias.name for alias in node.names)
        self.assertTrue(CONSUMED_RUNTIME_NAMES <= imported)

    def test_runtime_has_no_project_semantic_imports(self) -> None:
        tree = ast.parse(RUNTIME_PATH.read_text(encoding="utf-8"))
        project_imports: list[str] = []
        for node in tree.body:
            if isinstance(node, ast.ImportFrom) and str(node.module or "").startswith(
                "scripts"
            ):
                project_imports.append(str(node.module))
            elif isinstance(node, ast.Import):
                project_imports.extend(
                    alias.name for alias in node.names if alias.name.startswith("scripts")
                )
        self.assertEqual(project_imports, [])

    def test_operational_summary_preserves_strict_integer_counts(self) -> None:
        self.assertEqual(
            RUNTIME.structural_scan_progress_summary(
                {
                    "stages": [
                        {
                            "requested_count": 3,
                            "reused_count": 2,
                            "fresh_count": 1,
                            "missing_count": 0,
                            "batch_count": 1,
                        },
                        {
                            "requested_count": True,
                            "reused_count": "1",
                            "fresh_count": None,
                        },
                    ]
                }
            ),
            "3 requested; 2 reused; 1 fresh; 0 missing; 1 Lean batches",
        )


class SourceRecordRuntimeBehaviorTests(unittest.TestCase):
    def test_lock_status_reports_holder_metadata_without_reclaiming_it(self) -> None:
        """A PID namespace mismatch is observable, never a recovery signal."""

        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            lock_path = root / ".lake" / "source-record-audit.lock"
            lock_path.parent.mkdir(parents=True)
            owner = {
                "schema": RUNTIME.SOURCE_RECORD_AUDIT_LOCK_SCHEMA,
                "pid": 2,
                "paper": "FixturePaper",
                "operation": "source_record_scan",
                "started_at_epoch": 1.0,
                "heartbeat_at_epoch": 2.0,
            }
            lock_path.write_text(json.dumps(owner), encoding="utf-8")
            holder = subprocess.Popen(
                [
                    sys.executable,
                    "-c",
                    (
                        "import fcntl, pathlib, sys, time; "
                        "path = pathlib.Path(sys.argv[1]); "
                        "handle = path.open('a+'); "
                        "fcntl.flock(handle.fileno(), fcntl.LOCK_EX); "
                        "print('locked', flush=True); time.sleep(30)"
                    ),
                    str(lock_path),
                ],
                stdout=subprocess.PIPE,
                text=True,
            )
            try:
                assert holder.stdout is not None
                self.assertEqual(holder.stdout.readline().strip(), "locked")
                before = lock_path.stat().st_ino
                status = RUNTIME.source_record_audit_lock_status(root)
                self.assertTrue(status["held"])
                self.assertEqual(status["state"], "held")
                self.assertEqual(status["owner_visibility"], "recorded")
                self.assertEqual(status["owner"], owner)
                self.assertEqual(lock_path.stat().st_ino, before)
            finally:
                holder.terminate()
                holder.wait(timeout=10)
                if holder.stdout is not None:
                    holder.stdout.close()

    def test_lock_owner_metadata_is_written_and_cleared_with_the_lease(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            lock_path = root / ".lake" / "source-record-audit.lock"
            with RUNTIME.source_record_audit_lock(
                root,
                0,
                owner={
                    "paper": "FixturePaper",
                    "operation": "source_record_scan",
                    "request_id": "fixture-request",
                    "ignored": "not serialized",
                },
            ):
                with redirect_stderr(io.StringIO()):
                    RUNTIME.source_record_progress("fixture exact manifest phase started")
                owner = json.loads(lock_path.read_text(encoding="utf-8"))
                self.assertEqual(owner["schema"], RUNTIME.SOURCE_RECORD_AUDIT_LOCK_SCHEMA)
                self.assertEqual(owner["paper"], "FixturePaper")
                self.assertEqual(owner["operation"], "source_record_scan")
                self.assertEqual(owner["request_id"], "fixture-request")
                self.assertNotIn("ignored", owner)
                self.assertEqual(owner["progress_sequence"], 1)
                self.assertEqual(
                    owner["progress_message"], "fixture exact manifest phase started"
                )
                self.assertGreaterEqual(
                    float(owner["progress_at_epoch"]), float(owner["started_at_epoch"])
                )
                self.assertGreaterEqual(
                    float(owner["heartbeat_at_epoch"]), float(owner["started_at_epoch"])
                )
            status = RUNTIME.source_record_audit_lock_status(root)
            self.assertFalse(status["held"])
            self.assertEqual(status["state"], "available")
            self.assertEqual(status["owner_visibility"], "empty")

    def test_lock_status_treats_malformed_or_oversized_owner_bytes_as_diagnostic_only(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            lock_path = root / ".lake" / "source-record-audit.lock"
            lock_path.parent.mkdir(parents=True)
            lock_path.write_bytes(b"\xff")
            malformed = RUNTIME.source_record_audit_lock_status(root)
            self.assertFalse(malformed["held"])
            self.assertEqual(malformed["state"], "available")
            self.assertEqual(malformed["owner_visibility"], "updating_or_malformed")

            lock_path.write_bytes(
                b"x" * (RUNTIME.SOURCE_RECORD_AUDIT_LOCK_MAX_OWNER_BYTES + 1)
            )
            oversized = RUNTIME.source_record_audit_lock_status(root)
            self.assertFalse(oversized["held"])
            self.assertEqual(oversized["owner_visibility"], "too_large")

            lock_path.write_text(
                json.dumps({"pid": 2, "started_at_epoch": 1.0}), encoding="utf-8"
            )
            stale = RUNTIME.source_record_audit_lock_status(root)
            self.assertFalse(stale["held"])
            self.assertEqual(stale["owner_visibility"], "last_owner")

    def test_source_subprocess_receives_the_active_audit_lock_fd(self) -> None:
        """A detached Lake child keeps serialization if its supervisor disappears."""

        class CompletedChild:
            returncode = 0

            @staticmethod
            def communicate(*, timeout: float) -> tuple[str, None]:
                return "", None

        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            with RUNTIME.source_record_audit_lock(root, 0):
                active_fd = RUNTIME._ACTIVE_SOURCE_RECORD_AUDIT_LOCK_FD.get()
                self.assertIsInstance(active_fd, int)
                with patch.object(
                    RUNTIME.subprocess, "Popen", return_value=CompletedChild()
                ) as popen:
                    result = RUNTIME.run_source_record_subprocess(
                        [sys.executable, "-c", "pass"],
                        cwd=root,
                        phase="fixture inherited lock child",
                        timeout_seconds=1,
                    )
                self.assertEqual(result.returncode, 0)
                self.assertEqual(popen.call_args.kwargs["pass_fds"], (active_fd,))
                self.assertTrue(popen.call_args.kwargs["close_fds"])

    def test_inherited_lock_fd_survives_parent_descriptor_close(self) -> None:
        """Kernel flock ownership follows the child, not the lost supervisor."""

        def probe(path: Path) -> str:
            command = [
                sys.executable,
                "-c",
                (
                    "import fcntl, pathlib, sys; "
                    "handle = pathlib.Path(sys.argv[1]).open('a+'); "
                    "\ntry:\n"
                    " fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB); "
                    " print('available')\n"
                    "except BlockingIOError:\n"
                    " print('held')\n"
                ),
                str(path),
            ]
            return subprocess.check_output(command, text=True).strip()

        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            lock_path = root / ".lake" / "source-record-audit.lock"
            lock_path.parent.mkdir(parents=True)
            parent_handle = lock_path.open("a+", encoding="utf-8")
            child: subprocess.Popen[str] | None = None
            try:
                fcntl.flock(parent_handle.fileno(), fcntl.LOCK_EX)
                child = subprocess.Popen(
                    [sys.executable, "-c", "import time; time.sleep(0.4)"],
                    pass_fds=(parent_handle.fileno(),),
                    start_new_session=True,
                    text=True,
                )
                parent_handle.close()
                self.assertEqual(probe(lock_path), "held")
                child.wait(timeout=5)
                self.assertEqual(probe(lock_path), "available")
            finally:
                if not parent_handle.closed:
                    parent_handle.close()
                if child is not None and child.poll() is None:
                    child.terminate()
                    child.wait(timeout=5)

    def test_fails_fast_when_another_process_holds_the_repository_lock(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            lock_path = root / ".lake" / "source-record-audit.lock"
            lock_path.parent.mkdir(parents=True)
            holder = subprocess.Popen(
                [
                    sys.executable,
                    "-c",
                    (
                        "import fcntl, pathlib, sys, time; "
                        "path = pathlib.Path(sys.argv[1]); "
                        "handle = path.open('a+'); "
                        "fcntl.flock(handle.fileno(), fcntl.LOCK_EX); "
                        "print('locked', flush=True); time.sleep(30)"
                    ),
                    str(lock_path),
                ],
                stdout=subprocess.PIPE,
                text=True,
            )
            try:
                assert holder.stdout is not None
                self.assertEqual(holder.stdout.readline().strip(), "locked")
                with self.assertRaises(RUNTIME.SourceRecordAuditLockUnavailable):
                    with RUNTIME.source_record_audit_lock(root, 0):
                        self.fail("a held source-record lock must not be re-entered")
            finally:
                holder.terminate()
                holder.wait(timeout=10)
                if holder.stdout is not None:
                    holder.stdout.close()

    def test_structural_stage_progress_reports_requested_reused_fresh_and_missing(
        self,
    ) -> None:
        summary = RUNTIME.structural_scan_progress_summary(
            {
                "stages": [
                    {
                        "requested_count": 3,
                        "reused_count": 2,
                        "fresh_count": 1,
                        "missing_count": 0,
                        "batch_count": 1,
                    },
                    {
                        "requested_count": 2,
                        "reused_count": 1,
                        "fresh_count": 1,
                        "missing_count": 1,
                        "batch_count": 1,
                    },
                ]
            }
        )

        self.assertEqual(
            summary,
            "5 requested; 3 reused; 2 fresh; 1 missing; 2 Lean batches",
        )

    def test_progress_is_best_effort_when_the_caller_stream_is_closed(self) -> None:
        class ClosedStream:
            def write(self, _text: str) -> int:
                raise BrokenPipeError("fixture closed stream")

            def flush(self) -> None:
                raise BrokenPipeError("fixture closed stream")

        with patch.object(RUNTIME.sys, "stderr", ClosedStream()):
            RUNTIME.source_record_progress("fixture progress")

    def test_timeout_kills_the_isolated_process_group_and_reports_phase(self) -> None:
        diagnostics = io.StringIO()
        with redirect_stderr(diagnostics):
            result = RUNTIME.run_source_record_subprocess(
                [sys.executable, "-c", "import time; time.sleep(30)"],
                cwd=ROOT,
                phase="fixture bounded child",
                timeout_seconds=0.1,
                heartbeat_seconds=0.01,
            )

        self.assertTrue(result.timed_out)
        self.assertEqual(result.returncode, 124)
        self.assertIn("fixture bounded child", result.stdout)
        self.assertIn("killed its Lake/Lean process group", result.stdout)
        self.assertIn("fixture bounded child started", diagnostics.getvalue())
        self.assertIn("killed its Lake/Lean process group", diagnostics.getvalue())


if __name__ == "__main__":
    unittest.main()
