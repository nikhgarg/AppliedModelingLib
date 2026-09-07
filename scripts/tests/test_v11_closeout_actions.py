from __future__ import annotations

import builtins
import importlib
import unittest
from unittest import mock

from scripts.current_closeout.actions import (
    CURRENT_PYTHON_ACTION_ENTRYPOINTS,
    CURRENT_PYTHON_ACTION_SERVICES,
    classify_v11_worker_disposition,
    render_v11_operator_actions,
    schedule_v11_closeout,
)
from scripts.current_closeout.reducer import (
    V11CloseoutState,
    V11Decision,
    V11NextAction,
    V11WorkerDisposition,
)


class V11CloseoutActionTests(unittest.TestCase):
    def test_every_stable_action_cli_delegates_to_its_package_service(self) -> None:
        self.assertEqual(
            set(CURRENT_PYTHON_ACTION_SERVICES),
            set(CURRENT_PYTHON_ACTION_ENTRYPOINTS),
        )
        for entrypoint, (service_module, attribute) in (
            CURRENT_PYTHON_ACTION_SERVICES.items()
        ):
            with self.subTest(entrypoint=entrypoint):
                cli_module = importlib.import_module(
                    entrypoint.removesuffix(".py").replace("/", ".")
                )
                service = importlib.import_module(service_module)
                self.assertIs(
                    getattr(cli_module, attribute),
                    getattr(service, attribute),
                )

    def current_state(self) -> V11CloseoutState:
        return V11CloseoutState(
            structure_current=True,
            lean_graph_current=True,
            semantic_review_current=True,
            compiled_inputs_current=True,
            realization_current=True,
            plan_identity_current=True,
            final_source_audit_current=True,
            accepted_graph_current=False,
        )

    def test_every_reducer_action_has_one_explicit_adapter_route(self) -> None:
        expected_first = {
            V11NextAction.REUSE_ACCEPTED_GRAPH: None,
            V11NextAction.REPAIR_STRUCTURE: "resolve_static_closeout_blockers",
            V11NextAction.ACQUIRE_LEAN_GRAPH: "prepare_v11_lean_review_graph",
            V11NextAction.REVIEW_SEMANTIC_DELTA: "repair_current_v11_audit",
            V11NextAction.REBUILD: "paper_build",
            V11NextAction.REPAIR_REALIZATION: (
                "resolve_realization_receipt_preflight"
            ),
            V11NextAction.PUBLISH_PLAN: "publish_current_closeout_plan",
            V11NextAction.PERFORM_FINAL_SOURCE_AUDIT: (
                "perform_final_adversarial_source_audit"
            ),
            V11NextAction.INSPECT_WORKER_RECOVERY: "inspect_closeout_recovery",
            V11NextAction.INSPECT_FAILED_WORKER: "inspect_existing_closeout",
            V11NextAction.RUN_STRICT_CLOSEOUT: "strict_closeout",
        }
        self.assertEqual(set(expected_first), set(V11NextAction))
        rendered_python_entrypoints: set[str] = set()
        for action, expected in expected_first.items():
            with self.subTest(action=action.value):
                rendered = render_v11_operator_actions(
                    V11Decision(action),
                    paper="Fixture",
                    plan_identity="a" * 64,
                    final_holistic_surface_identity="b" * 64,
                    realization_receipt_preflight={
                        "current": action is not V11NextAction.REPAIR_REALIZATION,
                    },
                )
                self.assertEqual(
                    rendered[0]["id"] if rendered else None,
                    expected,
                )
                for item in rendered:
                    argv = item.get("argv")
                    if isinstance(argv, list) and argv[:1] == ["python3"]:
                        self.assertGreaterEqual(len(argv), 2)
                        rendered_python_entrypoints.add(str(argv[1]))
                if action is V11NextAction.PERFORM_FINAL_SOURCE_AUDIT:
                    self.assertEqual(
                        rendered[0]["final_holistic_surface_identity"],
                        "b" * 64,
                    )
        self.assertEqual(
            rendered_python_entrypoints,
            set(CURRENT_PYTHON_ACTION_ENTRYPOINTS),
        )

    def test_action_adapter_performs_no_io_or_subprocess_work(self) -> None:
        with (
            mock.patch.object(
                builtins,
                "open",
                side_effect=AssertionError("action adapter opened a file"),
            ),
            mock.patch(
                "subprocess.run",
                side_effect=AssertionError("action adapter ran a subprocess"),
            ),
        ):
            result = schedule_v11_closeout(
                self.current_state(),
                paper="Fixture",
                plan_identity="b" * 64,
            )
        self.assertEqual(result["next_action"]["id"], "strict_closeout")

    def test_worker_reuse_requires_exact_plan_and_schema(self) -> None:
        exact_result = {
            "state": "complete",
            "result": {
                "operational_plan_identity": "c" * 64,
                "operational_plan_identity_schema": "schema-1",
                "semantic_closeout_passed": True,
            },
        }
        self.assertEqual(
            classify_v11_worker_disposition(
                exact_result,
                prior_execution_error="",
                plan_identity="c" * 64,
                plan_identity_schema="schema-1",
            ),
            V11WorkerDisposition.SAME_PLAN_FAILED,
        )
        for mutation in (
            {"operational_plan_identity": "d" * 64},
            {"operational_plan_identity_schema": "schema-2"},
        ):
            changed = {
                "state": "complete",
                "result": {**exact_result["result"], **mutation},
            }
            self.assertEqual(
                classify_v11_worker_disposition(
                    changed,
                    prior_execution_error="",
                    plan_identity="c" * 64,
                    plan_identity_schema="schema-1",
                ),
                V11WorkerDisposition.DIFFERENT_PLAN,
            )

    def test_unpublished_worker_result_never_becomes_acceptance_authority(self) -> None:
        finalization_failure = {
            "state": "complete",
            "result": {
                "operational_plan_identity": "e" * 64,
                "operational_plan_identity_schema": "schema-1",
                "audit_exit_code": 0,
                "receipt_finalization_failed": True,
                "replan_required": False,
            },
        }
        self.assertEqual(
            classify_v11_worker_disposition(
                finalization_failure,
                prior_execution_error="",
                plan_identity="e" * 64,
                plan_identity_schema="schema-1",
            ),
            V11WorkerDisposition.SAME_PLAN_FAILED,
        )
        changed = {
            **finalization_failure,
            "result": {**finalization_failure["result"], "replan_required": True},
        }
        self.assertEqual(
            classify_v11_worker_disposition(
                changed,
                prior_execution_error="",
                plan_identity="e" * 64,
                plan_identity_schema="schema-1",
            ),
            V11WorkerDisposition.SAME_PLAN_FAILED,
        )


if __name__ == "__main__":
    unittest.main()
