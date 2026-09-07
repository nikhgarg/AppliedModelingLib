#!/usr/bin/env python3
"""Tests for durable, non-authoritative paper-closeout execution state."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.closeout_execution_state import (
    CloseoutExecutionLease,
    atomic_write_json,
    closeout_worker_state_path,
    current_process_identity,
    default_closeout_execution_path,
    effective_closeout_execution_state,
    execution_lock_is_held,
    read_execution_state,
    running_execution_summary,
)


class CloseoutExecutionStateTests(unittest.TestCase):
    def test_effective_state_recovers_only_the_exact_terminal_child(self) -> None:
        command = ["python3", "scripts/audit_repository.py", "--paper", "Fixture"]
        child_identity = {"pid": 2_000_000_000, "start_ticks": "17"}

        def write_states(root: Path, raw_overrides: dict[str, object]) -> None:
            worker_path = closeout_worker_state_path(root, "Fixture")
            raw_path = default_closeout_execution_path(root, "Fixture")
            atomic_write_json(
                worker_path,
                {
                    "schema": 1,
                    "acceptance_credential": False,
                    "state": "running",
                    "paper": "Fixture",
                    "command": command,
                    "child_process_identity": child_identity,
                },
            )
            atomic_write_json(
                raw_path,
                {
                    "schema": 1,
                    "acceptance_credential": False,
                    "state": "complete",
                    "paper": "Fixture",
                    "command": command,
                    "process_identity": child_identity,
                    "exit_code": 0,
                    **raw_overrides,
                },
            )

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            write_states(root, {})
            payload, error, namespace, _path = effective_closeout_execution_state(
                root, "Fixture"
            )
            self.assertEqual(error, "")
            self.assertEqual(namespace, "raw_recovered_child")
            self.assertEqual(payload["state"], "complete")

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            worker_path = closeout_worker_state_path(root, "Fixture")
            raw_path = default_closeout_execution_path(root, "Fixture")
            request = {
                "deep_paper_prose": False,
                "operational_plan_identity": "a" * 64,
                "operational_plan_identity_schema": "closeout-execution-input-graph-v2",
            }
            atomic_write_json(
                worker_path,
                {
                    "schema": 1,
                    "acceptance_credential": False,
                    "state": "running",
                    "paper": "Fixture",
                    "command": command,
                    "request": request,
                    "child_process_identity": child_identity,
                },
            )
            atomic_write_json(
                raw_path,
                {
                    "schema": 1,
                    "acceptance_credential": False,
                    "state": "complete",
                    "paper": "Fixture",
                    "command": command,
                    "process_identity": child_identity,
                    "exit_code": 0,
                    "result": {"semantic_closeout_passed": True},
                },
            )
            payload, error, namespace, _path = effective_closeout_execution_state(
                root, "Fixture"
            )
            self.assertEqual(error, "")
            self.assertEqual(namespace, "raw_recovered_child")
            self.assertEqual(payload["request"], request)
            self.assertEqual(
                payload["result"]["operational_plan_identity"],
                "a" * 64,
            )
            self.assertEqual(
                payload["result"]["operational_plan_identity_schema"],
                "closeout-execution-input-graph-v2",
            )

        variants = {
            "identity": {"process_identity": {"pid": 9}},
            "command": {"command": ["different"]},
            "paper": {"paper": "Other"},
            "state": {"state": "running"},
        }
        for label, overrides in variants.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory() as temp_dir:
                root = Path(temp_dir)
                write_states(root, overrides)
                payload, error, namespace, _path = effective_closeout_execution_state(
                    root, "Fixture"
                )
                self.assertIsNone(payload)
                self.assertTrue(error)
                self.assertIn("recovery", namespace)

    def test_effective_state_rejects_wrong_paper_terminal(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            raw_path = default_closeout_execution_path(root, "Fixture")
            atomic_write_json(
                raw_path,
                {
                    "schema": 1,
                    "acceptance_credential": False,
                    "state": "complete",
                    "paper": "Other",
                    "exit_code": 0,
                    "result": {"semantic_closeout_passed": True},
                },
            )
            payload, error, namespace, _path = effective_closeout_execution_state(
                root, "Fixture"
            )
            self.assertIsNone(payload)
            self.assertIn("different paper", error)
            self.assertEqual(namespace, "raw_recovery_required")

    def test_live_lease_blocks_duplicate_and_persists_completion(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            state_path = Path(temp_dir) / "paper_closeout_execution.json"
            lease, error = CloseoutExecutionLease.acquire(
                state_path,
                paper="Fixture",
                command=["python3", "scripts/audit_repository.py"],
            )
            self.assertEqual(error, "")
            self.assertIsNotNone(lease)
            assert lease is not None

            active = running_execution_summary(state_path)
            self.assertIsNotNone(active)
            assert active is not None
            self.assertEqual(active["paper"], "Fixture")

            lease.heartbeat(
                stage="primary_paper_gate",
                completed_units=3,
                total_units=8,
                cache_hits=2,
                cache_misses=1,
                details={"status": "started"},
            )
            running, heartbeat_error = read_execution_state(state_path)
            self.assertEqual(heartbeat_error, "")
            assert running is not None
            self.assertEqual(running["progress"]["stage"], "primary_paper_gate")
            self.assertEqual(running["progress"]["completed_units"], 3)
            self.assertIn("heartbeat_at", running["progress"])

            duplicate, duplicate_error = CloseoutExecutionLease.acquire(
                state_path,
                paper="Fixture",
                command=["duplicate"],
            )
            self.assertIsNone(duplicate)
            self.assertIn("already running", duplicate_error)

            lease.complete(
                exit_code=0,
                result={"semantic_closeout_passed": True, "trace": {}},
            )
            payload, read_error = read_execution_state(state_path)
            self.assertEqual(read_error, "")
            self.assertIsNotNone(payload)
            assert payload is not None
            self.assertEqual(payload["state"], "complete")
            self.assertFalse(payload["acceptance_credential"])
            self.assertTrue(payload["result"]["semantic_closeout_passed"])
            self.assertNotIn("progress", payload)
            self.assertTrue(lease.lock_path.exists())
            self.assertFalse(execution_lock_is_held(state_path))
            self.assertIsNone(running_execution_summary(state_path))

    def test_dead_process_lock_is_reclaimed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            state_path = Path(temp_dir) / "paper_closeout_execution.json"
            lock_path = state_path.with_name(f"{state_path.name}.lock")
            lock_path.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "acceptance_credential": False,
                        "paper": "Fixture",
                        "lease_id": "dead",
                        "process_identity": {"pid": 2_000_000_000},
                    }
                ),
                encoding="utf-8",
            )
            self.assertFalse(execution_lock_is_held(state_path))

            lease, error = CloseoutExecutionLease.acquire(
                state_path,
                paper="Fixture",
                command=["replacement"],
            )
            self.assertEqual(error, "")
            self.assertIsNotNone(lease)
            assert lease is not None
            self.assertEqual(
                json.loads(lock_path.read_text(encoding="utf-8"))["lease_id"],
                lease.lease_id,
            )
            lease.fail("fixture stop")

            payload, read_error = read_execution_state(state_path)
            self.assertEqual(read_error, "")
            self.assertEqual(payload["state"], "aborted")
            self.assertEqual(payload["failure"], "fixture stop")

    def test_live_legacy_lock_blocks_flock_migration_without_state(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            state_path = Path(temp_dir) / "paper_closeout_execution.json"
            lock_path = state_path.with_name(f"{state_path.name}.lock")
            lock_path.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "acceptance_credential": False,
                        "paper": "Fixture",
                        "lease_id": "legacy-live",
                        "process_identity": current_process_identity(),
                    }
                ),
                encoding="utf-8",
            )
            self.assertTrue(execution_lock_is_held(state_path))

            lease, error = CloseoutExecutionLease.acquire(
                state_path,
                paper="Fixture",
                command=["replacement"],
            )
            self.assertIsNone(lease)
            self.assertIn("legacy paper closeout is already running", error)
            self.assertEqual(
                json.loads(lock_path.read_text(encoding="utf-8"))["lease_id"],
                "legacy-live",
            )

    def test_migration_retries_when_legacy_lock_path_is_unlinked(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            state_path = Path(temp_dir) / "paper_closeout_execution.json"
            lock_path = state_path.with_name(f"{state_path.name}.lock")
            lock_path.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "acceptance_credential": False,
                        "paper": "Fixture",
                        "lease_id": "legacy-stale",
                        "process_identity": {"pid": 2_000_000_000},
                    }
                ),
                encoding="utf-8",
            )

            def unlink_during_migration(fd: int, path: Path) -> str:
                path.unlink()
                return ""

            with mock.patch(
                "scripts.closeout_execution_state._legacy_lock_conflict",
                side_effect=unlink_during_migration,
            ):
                lease, error = CloseoutExecutionLease.acquire(
                    state_path,
                    paper="Fixture",
                    command=["replacement"],
                )
            self.assertEqual(error, "")
            self.assertIsNotNone(lease)
            assert lease is not None
            self.assertTrue(lock_path.exists())
            self.assertTrue(execution_lock_is_held(state_path))
            self.assertEqual(
                json.loads(lock_path.read_text(encoding="utf-8"))["lease_id"],
                lease.lease_id,
            )
            lease.fail("fixture stop")

    def test_inherited_flock_survives_supervisor_fd_close(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            state_path = Path(temp_dir) / "paper_closeout_execution.json"
            lease, error = CloseoutExecutionLease.acquire(
                state_path,
                paper="Fixture",
                command=["audit"],
                launch_id="a" * 32,
            )
            self.assertEqual(error, "")
            assert lease is not None

            child = subprocess.Popen(
                [sys.executable, "-c", "import time; time.sleep(0.5)"],
                pass_fds=(lease.lock_fd,),
            )
            lease.record_child_process(child.pid)
            # Model an abrupt supervisor exit: close its descriptor without an
            # explicit LOCK_UN. The inherited audit descriptor retains it.
            os.close(lease.lock_fd)
            lease.lock_fd = -1
            self.assertTrue(execution_lock_is_held(state_path))
            self.assertIsNotNone(running_execution_summary(state_path))
            child.wait(timeout=2)
            abandoned = json.loads(state_path.read_text(encoding="utf-8"))
            abandoned["process_identity"] = {"pid": 2_000_000_000}
            atomic_write_json(state_path, abandoned)
            self.assertFalse(execution_lock_is_held(state_path))
            self.assertIsNone(running_execution_summary(state_path))

    def test_replaced_lock_path_cannot_admit_duplicate_live_worker(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            state_path = Path(temp_dir) / "paper_closeout_execution.json"
            lease, error = CloseoutExecutionLease.acquire(
                state_path,
                paper="Fixture",
                command=["audit"],
            )
            self.assertEqual(error, "")
            assert lease is not None

            lease.lock_path.unlink()
            lease.lock_path.write_text(
                json.dumps({"lock_backend": "flock_v1"}), encoding="utf-8"
            )
            self.assertFalse(execution_lock_is_held(state_path))
            self.assertIsNotNone(running_execution_summary(state_path))

            duplicate, duplicate_error = CloseoutExecutionLease.acquire(
                state_path,
                paper="Fixture",
                command=["duplicate"],
            )
            self.assertIsNone(duplicate)
            self.assertIn("already running", duplicate_error)
            lease.fail("fixture stop")


if __name__ == "__main__":
    unittest.main()
