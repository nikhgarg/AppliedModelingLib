from __future__ import annotations

import unittest
from dataclasses import replace

from scripts.current_closeout.reducer import (
    V11CloseoutState,
    V11NextAction,
    V11WorkerDisposition,
    reduce_v11_closeout,
)


class V11CloseoutReducerTests(unittest.TestCase):
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

    def test_each_missing_fact_selects_its_unique_earliest_transition(self) -> None:
        base = self.current_state()
        cases = {
            "structure_current": V11NextAction.REPAIR_STRUCTURE,
            "lean_graph_current": V11NextAction.ACQUIRE_LEAN_GRAPH,
            "semantic_review_current": V11NextAction.REVIEW_SEMANTIC_DELTA,
            "compiled_inputs_current": V11NextAction.REBUILD,
            "realization_current": V11NextAction.REPAIR_REALIZATION,
            "plan_identity_current": V11NextAction.PUBLISH_PLAN,
            "final_source_audit_current": (
                V11NextAction.PERFORM_FINAL_SOURCE_AUDIT
            ),
        }
        for field, expected in cases.items():
            with self.subTest(field=field):
                self.assertEqual(
                    reduce_v11_closeout(replace(base, **{field: False})).action,
                    expected,
                )

    def test_worker_states_cannot_adopt_an_unbound_legacy_completion(self) -> None:
        base = self.current_state()
        self.assertEqual(
            reduce_v11_closeout(
                replace(base, worker=V11WorkerDisposition.SAME_PLAN_FAILED)
            ).action,
            V11NextAction.INSPECT_FAILED_WORKER,
        )
        changed = reduce_v11_closeout(
            replace(base, worker=V11WorkerDisposition.DIFFERENT_PLAN)
        )
        self.assertEqual(changed.action, V11NextAction.RUN_STRICT_CLOSEOUT)
        self.assertTrue(changed.requires_new_worker)
        self.assertEqual(
            reduce_v11_closeout(
                replace(base, worker=V11WorkerDisposition.STATE_ERROR)
            ).action,
            V11NextAction.INSPECT_WORKER_RECOVERY,
        )

    def test_current_accepted_graph_is_terminal(self) -> None:
        state = replace(
            self.current_state(),
            accepted_graph_current=True,
            structure_current=False,
            semantic_review_current=False,
            compiled_inputs_current=False,
        )
        self.assertEqual(
            reduce_v11_closeout(state).action,
            V11NextAction.REUSE_ACCEPTED_GRAPH,
        )

    def test_no_change_without_accepted_graph_runs_one_strict_worker(self) -> None:
        decision = reduce_v11_closeout(self.current_state())
        self.assertEqual(decision.action, V11NextAction.RUN_STRICT_CLOSEOUT)
        self.assertFalse(decision.requires_new_worker)


if __name__ == "__main__":
    unittest.main()
