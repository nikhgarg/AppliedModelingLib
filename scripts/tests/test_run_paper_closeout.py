#!/usr/bin/env python3
"""Tests for the detached paper-closeout launcher."""

from __future__ import annotations

import hashlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import run_paper_closeout as runner_cli
from scripts.current_closeout import worker as runner


class RunPaperCloseoutTests(unittest.TestCase):
    def test_cli_delegates_to_the_current_worker_service(self) -> None:
        self.assertIs(runner_cli.main, runner.main)

    def setUp(self) -> None:
        engine_guard = mock.patch.object(
            runner, "runtime_engine_registration_error", return_value=""
        )
        engine_guard.start()
        self.addCleanup(engine_guard.stop)

    def test_plan_receipt_reuse_requires_registered_clean_head_engine(self) -> None:
        with (
            mock.patch.object(
                runner,
                "runtime_engine_registration_error",
                return_value="formalization engine runtime material differs from clean HEAD",
            ),
            mock.patch.object(runner, "load_validated_closeout_plan_receipt") as load,
        ):
            error = runner._plan_receipt_error(
                "Fixture",
                deep_paper_prose=False,
                plan_identity="a" * 64,
            )
        self.assertIn("runtime is not registered", error)
        self.assertIn("differs from clean HEAD", error)
        load.assert_not_called()

    def test_audit_command_does_not_sniff_audit_source_capabilities(self) -> None:
        with mock.patch.object(Path, "read_text") as read_text:
            command = runner._audit_command("Fixture", deep_paper_prose=False)
        self.assertNotIn("--no-closeout-state", command)
        self.assertEqual(
            command[1:3], ["-m", "scripts.current_closeout.strict_runner"]
        )
        self.assertNotIn("--paper-closeout", command)
        self.assertNotIn("--closeout-trace", command)
        read_text.assert_not_called()

        command = runner._audit_command("Fixture", deep_paper_prose=True)
        self.assertIn("--deep-paper-prose", command)

        command = runner._audit_command(
            "Fixture", deep_paper_prose=False, plan_identity="a" * 64
        )
        self.assertEqual(
            command[-2:], ["--operational-plan-identity", "a" * 64]
        )

    def test_inner_closeout_progress_mirrors_only_matching_plan(self) -> None:
        progress_state = {
            "paper": "Fixture",
            "state": "running",
            "request": {"operational_plan_identity": "a" * 64},
            "progress": {
                "stage": "primary_paper_gate",
                "completed_units": 4,
                "total_units": runner.STRICT_CLOSEOUT_STAGE_COUNT,
                "details": {"status": "started"},
            },
        }
        with (
            mock.patch.object(
                runner, "default_closeout_execution_path", return_value=Path("inner.json")
            ),
            mock.patch.object(
                runner, "read_execution_state", return_value=(progress_state, "")
            ),
        ):
            mirrored = runner._inner_closeout_progress("Fixture", "a" * 64)

        self.assertEqual(
            mirrored,
            (
                "primary_paper_gate",
                4,
                runner.STRICT_CLOSEOUT_STAGE_COUNT,
                {
                    "status": "started",
                    "inner_execution_state": "running",
                    "progress_source": "current_closeout_strict_runner",
                },
            ),
        )

    def test_inner_closeout_progress_rejects_stale_plan(self) -> None:
        progress_state = {
            "paper": "Fixture",
            "state": "running",
            "request": {"operational_plan_identity": "b" * 64},
            "progress": {
                "stage": "primary_paper_gate",
                "completed_units": 4,
                "total_units": runner.STRICT_CLOSEOUT_STAGE_COUNT,
            },
        }
        with mock.patch.object(
            runner, "read_execution_state", return_value=(progress_state, "")
        ):
            self.assertIsNone(
                runner._inner_closeout_progress("Fixture", "a" * 64)
            )

    def test_inner_closeout_progress_accepts_registered_final_stage(self) -> None:
        progress_state = {
            "paper": "Fixture",
            "state": "running",
            "request": {"operational_plan_identity": "a" * 64},
            "progress": {
                "stage": "final_input_check",
                "completed_units": runner.STRICT_CLOSEOUT_STAGE_COUNT,
                "total_units": runner.STRICT_CLOSEOUT_STAGE_COUNT,
            },
        }
        with mock.patch.object(
            runner, "read_execution_state", return_value=(progress_state, "")
        ):
            mirrored = runner._inner_closeout_progress("Fixture", "a" * 64)
        self.assertIsNotNone(mirrored)
        assert mirrored is not None
        self.assertEqual(mirrored[:3], (
            "final_input_check",
            runner.STRICT_CLOSEOUT_STAGE_COUNT,
            runner.STRICT_CLOSEOUT_STAGE_COUNT,
        ))

    def test_inner_closeout_progress_rejects_unregistered_stage(self) -> None:
        progress_state = {
            "paper": "Fixture",
            "state": "running",
            "request": {"operational_plan_identity": "a" * 64},
            "progress": {
                "stage": "ad_hoc_extra_stage",
                "completed_units": 1,
                "total_units": runner.STRICT_CLOSEOUT_STAGE_COUNT,
            },
        }
        with mock.patch.object(
            runner, "read_execution_state", return_value=(progress_state, "")
        ):
            self.assertIsNone(
                runner._inner_closeout_progress("Fixture", "a" * 64)
            )

    def test_completed_state_returns_recorded_exit_without_running_audit(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            state = Path(temp_dir) / "state.json"
            runner.atomic_write_json(
                state,
                {
                    "schema": 1,
                    "acceptance_credential": False,
                    "paper": "Fixture",
                    "state": "complete",
                    "launch_id": "a" * 32,
                    "exit_code": 1,
                },
            )
            with (
                mock.patch.object(runner, "worker_state_path", return_value=state),
                mock.patch.object(runner.time, "sleep") as sleep,
            ):
                self.assertEqual(
                    runner._wait_for_worker("Fixture", None, launch_id="a" * 32),
                    1,
                )
            sleep.assert_not_called()

    def test_wait_ignores_terminal_state_from_previous_launch(self) -> None:
        old = {
            "schema": 1,
            "acceptance_credential": False,
            "state": "complete",
            "launch_id": "a" * 32,
            "exit_code": 1,
        }
        current = {
            **old,
            "launch_id": "b" * 32,
            "exit_code": 0,
        }
        process = mock.Mock()
        process.poll.return_value = None
        with (
            mock.patch.object(
                runner, "read_execution_state", side_effect=[(old, ""), (current, "")]
            ),
            mock.patch.object(runner.time, "sleep") as sleep,
        ):
            result = runner._wait_for_worker("Fixture", process, launch_id="b" * 32)
        self.assertEqual(result, 0)
        sleep.assert_called_once_with(1.0)

    def test_launch_refuses_to_attach_to_different_closeout_profile(self) -> None:
        plan_identity = "a" * 64
        active = {
            "paper": "Fixture",
            "launch_id": "a" * 32,
            "request": runner._request_identity(
                "Fixture",
                deep_paper_prose=False,
                plan_identity=plan_identity,
            ),
        }
        with (
            mock.patch.object(runner, "running_execution_summary", return_value=active),
            mock.patch.object(runner.subprocess, "Popen") as popen,
        ):
            result = runner._launch(
                "Fixture",
                deep_paper_prose=True,
                no_wait=False,
                plan_identity=plan_identity,
                new_run=True,
            )
        self.assertEqual(result, 3)
        popen.assert_not_called()

    def test_launch_rejects_dirty_engine_before_attaching_to_live_worker(self) -> None:
        with (
            mock.patch.object(
                runner,
                "runtime_engine_registration_error",
                return_value="formalization engine runtime material differs from clean HEAD",
            ),
            mock.patch.object(runner, "running_execution_summary") as running,
            mock.patch.object(runner.subprocess, "Popen") as popen,
        ):
            result = runner._launch(
                "Fixture",
                deep_paper_prose=False,
                no_wait=True,
                plan_identity="a" * 64,
                new_run=False,
            )
        self.assertEqual(result, 6)
        running.assert_not_called()
        popen.assert_not_called()

    def test_matching_completed_plan_is_idempotent(self) -> None:
        plan_identity = "f" * 64
        request = runner._request_identity(
            "Fixture",
            deep_paper_prose=False,
            plan_identity=plan_identity,
        )
        prior = {
            "schema": 1,
            "acceptance_credential": False,
            "state": "complete",
            "launch_id": "a" * 32,
            "request": request,
            "exit_code": 0,
            "result": {"acceptance_credential": False},
        }
        with (
            mock.patch.object(runner, "running_execution_summary", return_value=None),
            mock.patch.object(runner, "read_execution_state", return_value=(prior, "")),
            mock.patch.object(runner, "_plan_receipt_error", return_value=""),
            mock.patch.object(runner.subprocess, "Popen") as popen,
        ):
            result = runner._launch(
                "Fixture",
                deep_paper_prose=False,
                no_wait=False,
                plan_identity=plan_identity,
                new_run=False,
            )
        self.assertEqual(result, 0)
        popen.assert_not_called()

    def test_prior_terminal_state_requires_explicit_new_run_when_plan_changed(
        self,
    ) -> None:
        prior = {
            "schema": 1,
            "acceptance_credential": False,
            "state": "complete",
            "launch_id": "a" * 32,
            "request": {},
            "exit_code": 0,
        }
        with (
            mock.patch.object(runner, "running_execution_summary", return_value=None),
            mock.patch.object(runner, "read_execution_state", return_value=(prior, "")),
            mock.patch.object(runner, "_plan_receipt_error", return_value=""),
            mock.patch.object(runner.subprocess, "Popen") as popen,
        ):
            result = runner._launch(
                "Fixture",
                deep_paper_prose=False,
                no_wait=False,
                plan_identity="b" * 64,
                new_run=False,
            )
        self.assertEqual(result, 4)
        popen.assert_not_called()

    def test_stale_printed_plan_starts_one_worker_for_authoritative_recheck(self) -> None:
        plan_identity = "f" * 64
        prior = {
            "schema": 1,
            "acceptance_credential": False,
            "state": "complete",
            "launch_id": "a" * 32,
            "request": runner._request_identity(
                "Fixture",
                deep_paper_prose=False,
                plan_identity=plan_identity,
            ),
            "exit_code": 0,
        }
        process = mock.Mock()
        process.pid = 17
        with (
            mock.patch.object(runner, "running_execution_summary", return_value=None),
            mock.patch.object(runner, "read_execution_state", return_value=(prior, "")),
            mock.patch.object(
                runner,
                "_plan_receipt_error",
                return_value="closeout content inputs changed",
            ),
            mock.patch.object(
                runner.subprocess, "Popen", return_value=process
            ) as popen,
            mock.patch.object(runner, "_wait_for_worker", return_value=6),
        ):
            result = runner._launch(
                "Fixture",
                deep_paper_prose=False,
                no_wait=False,
                plan_identity=plan_identity,
                new_run=True,
            )
        self.assertEqual(result, 6)
        popen.assert_called_once()
        command = popen.call_args.args[0]
        self.assertEqual(
            Path(command[1]),
            runner.ROOT / "scripts" / "run_paper_closeout.py",
        )

    def test_lock_handoff_waits_for_new_running_state(self) -> None:
        active = {"paper": "Fixture", "launch_id": "b" * 32}
        with (
            mock.patch.object(
                runner,
                "running_execution_summary",
                side_effect=[None, None, active],
            ),
            mock.patch.object(
                runner, "execution_lock_is_held", side_effect=[True, True]
            ),
            mock.patch.object(runner.time, "sleep") as sleep,
        ):
            observed, unresolved = runner._running_after_lock_transition(
                Path("state.json")
            )
        self.assertEqual(observed, active)
        self.assertFalse(unresolved)
        sleep.assert_called_once_with(0.05)

    def test_launch_waits_for_raw_closeout_state_publication(self) -> None:
        with (
            mock.patch.object(
                runner,
                "_running_after_lock_transition",
                side_effect=[(None, False), (None, True)],
            ) as transition,
            mock.patch.object(runner.subprocess, "Popen") as popen,
        ):
            result = runner._launch(
                "Fixture",
                deep_paper_prose=False,
                no_wait=False,
                plan_identity="a" * 64,
                new_run=True,
            )
        self.assertEqual(result, 5)
        self.assertEqual(transition.call_count, 2)
        popen.assert_not_called()

    def test_no_wait_start_timeout_is_explicitly_unknown(self) -> None:
        process = mock.Mock()
        process.poll.return_value = None
        with (
            mock.patch.object(runner, "read_execution_state", return_value=(None, "")),
            mock.patch.object(runner.time, "monotonic", side_effect=[0.0, 11.0]),
        ):
            result = runner._wait_for_start(
                "Fixture", process, launch_id="a" * 32, timeout_seconds=10.0
            )
        self.assertEqual(result, 5)

    def test_status_never_launches_work(self) -> None:
        payload = {
            "schema": 1,
            "acceptance_credential": False,
            "state": "complete",
            "exit_code": 0,
        }
        with (
            mock.patch.object(
                runner, "read_execution_state", return_value=(payload, "")
            ),
            mock.patch.object(runner, "running_execution_summary", return_value=None),
            mock.patch.object(
                runner,
                "load_final_closure_receipt",
                side_effect=runner.FinalClosureReceiptError("missing receipt"),
            ),
            mock.patch.object(runner.subprocess, "Popen") as popen,
        ):
            self.assertEqual(runner._status("Fixture"), 0)
        popen.assert_not_called()

    def test_status_separates_canonical_closeout_from_old_worker_state(self) -> None:
        operational = {
            "schema": 1,
            "acceptance_credential": False,
            "state": "complete",
            "exit_code": 7,
            "result": {"receipt_finalization_failed": True},
        }
        receipt = mock.Mock(
            path=Path("/repo/papers/Fixture/FINAL_CLOSURE_RECEIPT.md"),
            payload={
                "schema": 6,
                "closed_at": "2026-08-26",
                "accepted_graph": {
                    "pointer": "papers/Fixture/audit/current_accepted_graph.json",
                    "graph_sha256": "a" * 64,
                },
            },
        )
        stdout = io.StringIO()
        with (
            mock.patch.object(runner, "ROOT", Path("/repo")),
            mock.patch.object(
                runner,
                "effective_closeout_execution_state",
                return_value=(operational, "", "worker", Path("state.json")),
            ),
            mock.patch.object(runner, "running_execution_summary", return_value=None),
            mock.patch.object(runner, "load_final_closure_receipt", return_value=receipt),
            mock.patch("sys.stdout", stdout),
        ):
            self.assertEqual(runner._status("Fixture"), 0)

        output = json.loads(stdout.getvalue())
        self.assertEqual(output["canonical_closeout"]["state"], "recorded")
        self.assertEqual(
            output["canonical_closeout"]["accepted_graph_sha256"], "a" * 64
        )
        self.assertNotIn("acceptance_credential", output)
        self.assertFalse(output["operational_execution"]["acceptance_credential"])
        self.assertEqual(output["operational_execution"]["exit_code"], 7)

    def test_worker_records_immutable_log_and_terminal_result(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            launch_id = "a" * 32
            command = [sys.executable, "-c", "print('strict fixture passed')"]
            with (
                mock.patch.object(runner, "ROOT", root),
                mock.patch.object(runner, "_audit_command", return_value=command),
                mock.patch.object(runner, "_plan_receipt_error", return_value=""),
                mock.patch.object(
                    runner,
                    "_inner_current_closeout_finalization",
                    return_value={"canonical_receipt": "papers/Fixture/FINAL_CLOSURE_RECEIPT.md"},
                ),
            ):
                result = runner._worker(
                    "Fixture",
                    deep_paper_prose=False,
                    launch_id=launch_id,
                    plan_identity="f" * 64,
                )
                state, error = runner.read_execution_state(
                    runner.worker_state_path("Fixture")
                )
                log_path = runner.worker_log_path("Fixture", launch_id)
            self.assertEqual(result, 0)
            self.assertEqual(error, "")
            assert state is not None
            self.assertEqual(state["state"], "complete")
            self.assertEqual(state["launch_id"], launch_id)
            self.assertEqual(
                state["result"]["audit_log_sha256"],
                hashlib.sha256(log_path.read_bytes()).hexdigest(),
            )
            self.assertEqual(
                state["result"]["operational_plan_identity_schema"],
                runner.OPERATIONAL_PLAN_IDENTITY_SCHEMA,
            )
            self.assertEqual(
                state["result"]["closeout_finalization"]["canonical_receipt"],
                "papers/Fixture/FINAL_CLOSURE_RECEIPT.md",
            )

    def test_worker_never_reconstructs_current_publication_from_child_exit(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            launch_id = "e" * 32
            command = [sys.executable, "-c", "print('current closeout published')"]
            published = {
                "canonical_receipt": "papers/Fixture/FINAL_CLOSURE_RECEIPT.md",
                "evidence_lane": "obligation-graph",
            }
            with (
                mock.patch.object(runner, "ROOT", root),
                mock.patch.object(runner, "_audit_command", return_value=command),
                mock.patch.object(runner, "_plan_receipt_error", return_value=""),
                mock.patch.object(
                    runner,
                    "_inner_current_closeout_finalization",
                    return_value=published,
                ),
            ):
                result = runner._worker(
                    "Fixture",
                    deep_paper_prose=False,
                    launch_id=launch_id,
                    plan_identity="f" * 64,
                )
                state, error = runner.read_execution_state(
                    runner.worker_state_path("Fixture")
                )
        self.assertEqual(result, 0)
        self.assertEqual(error, "")
        assert state is not None
        self.assertEqual(state["result"]["closeout_finalization"], published)
        self.assertFalse(hasattr(runner, "finalize_passed_closeout"))

    def test_worker_invalidates_success_when_plan_changes_during_audit(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            launch_id = "b" * 32
            command = [sys.executable, "-c", "print('audit passed')"]
            with (
                mock.patch.object(runner, "ROOT", root),
                mock.patch.object(runner, "_audit_command", return_value=command),
                mock.patch.object(
                    runner,
                    "_plan_receipt_error",
                    return_value="content inputs changed",
                ),
            ):
                result = runner._worker(
                    "Fixture",
                    deep_paper_prose=False,
                    launch_id=launch_id,
                    plan_identity="f" * 64,
                )
                state, error = runner.read_execution_state(
                    runner.worker_state_path("Fixture")
                )
            self.assertEqual(result, 6)
            self.assertEqual(error, "")
            assert state is not None
            self.assertEqual(state["exit_code"], 6)
            self.assertEqual(state["result"]["audit_exit_code"], 0)
            self.assertFalse(state["result"]["semantic_closeout_passed"])
            self.assertTrue(state["result"]["replan_required"])

    def test_worker_fails_closed_when_child_has_no_publication_record(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            launch_id = "d" * 32
            command = [sys.executable, "-c", "print('audit passed')"]
            with (
                mock.patch.object(runner, "ROOT", root),
                mock.patch.object(runner, "_audit_command", return_value=command),
                mock.patch.object(runner, "_plan_receipt_error", return_value=""),
                mock.patch.object(
                    runner,
                    "_inner_current_closeout_finalization",
                    return_value=None,
                ),
            ):
                result = runner._worker(
                    "Fixture",
                    deep_paper_prose=False,
                    launch_id=launch_id,
                    plan_identity="f" * 64,
                )
                state, error = runner.read_execution_state(
                    runner.worker_state_path("Fixture")
                )
        self.assertEqual(result, 7)
        self.assertEqual(error, "")
        assert state is not None
        self.assertTrue(state["result"]["semantic_closeout_passed"])
        self.assertEqual(state["result"]["audit_exit_code"], 0)
        self.assertTrue(state["result"]["receipt_finalization_failed"])
        self.assertIn("without its in-process publication record", state["result"]["reason"])

    def test_worker_preserves_failed_child_exit_without_postrun_revalidation(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            launch_id = "c" * 32
            command = [sys.executable, "-c", "raise SystemExit(4)"]
            with (
                mock.patch.object(runner, "ROOT", root),
                mock.patch.object(runner, "_audit_command", return_value=command),
                mock.patch.object(runner, "_plan_receipt_error") as plan_error,
            ):
                result = runner._worker(
                    "Fixture",
                    deep_paper_prose=False,
                    launch_id=launch_id,
                    plan_identity="f" * 64,
                )
                state, error = runner.read_execution_state(
                    runner.worker_state_path("Fixture")
                )
            self.assertEqual(result, 4)
            self.assertEqual(error, "")
            plan_error.assert_not_called()
            assert state is not None
            self.assertEqual(state["exit_code"], 4)
            self.assertEqual(state["result"]["audit_exit_code"], 4)
            self.assertFalse(state["result"]["semantic_closeout_passed"])
            self.assertNotIn("replan_required", state["result"])


if __name__ == "__main__":
    unittest.main()
