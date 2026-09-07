#!/usr/bin/env python3
"""Pure next-action reducer for the current graph-native closeout package.

This module owns no files, subprocesses, locks, receipts, or semantic checks.
Its inputs are already-validated facts.  It makes impossible the historical
states that had accumulated in the generic closeout scheduler: a v11 closeout
cannot adopt an unbound v10 worker, consult dashboard caches, or request a raw
receipt transition.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum


class V11NextAction(str, Enum):
    """The closed set of operator transitions in one current closeout."""

    REUSE_ACCEPTED_GRAPH = "reuse_accepted_graph"
    REPAIR_STRUCTURE = "repair_structure"
    ACQUIRE_LEAN_GRAPH = "acquire_lean_graph"
    REVIEW_SEMANTIC_DELTA = "review_semantic_delta"
    REBUILD = "rebuild"
    REPAIR_REALIZATION = "repair_realization"
    PUBLISH_PLAN = "publish_plan"
    PERFORM_FINAL_SOURCE_AUDIT = "perform_final_source_audit"
    INSPECT_WORKER_RECOVERY = "inspect_worker_recovery"
    INSPECT_FAILED_WORKER = "inspect_failed_worker"
    RUN_STRICT_CLOSEOUT = "run_strict_closeout"


class V11WorkerDisposition(str, Enum):
    """Only worker states that can affect a current plan."""

    ABSENT = "absent"
    STATE_ERROR = "state_error"
    DIFFERENT_PLAN = "different_plan"
    SAME_PLAN_FAILED = "same_plan_failed"


@dataclass(frozen=True)
class V11CloseoutState:
    """Validated facts consumed by the current-protocol state machine."""

    structure_current: bool
    lean_graph_current: bool
    semantic_review_current: bool
    compiled_inputs_current: bool
    realization_current: bool
    plan_identity_current: bool
    final_source_audit_current: bool
    accepted_graph_current: bool
    worker: V11WorkerDisposition = V11WorkerDisposition.ABSENT


@dataclass(frozen=True)
class V11Decision:
    """One deterministic action and whether a replacement worker is needed."""

    action: V11NextAction
    requires_new_worker: bool = False


def reduce_v11_closeout(state: V11CloseoutState) -> V11Decision:
    """Return the unique earliest transition for an already-validated state.

    Ordering is dependency ordering, not convenience ordering.  No later fact
    can compensate for an earlier missing obligation.  A current accepted graph
    is checked before constructing prospective state and therefore terminates
    immediately.
    """

    if state.accepted_graph_current:
        return V11Decision(V11NextAction.REUSE_ACCEPTED_GRAPH)
    if not state.structure_current:
        return V11Decision(V11NextAction.REPAIR_STRUCTURE)
    if not state.lean_graph_current:
        return V11Decision(V11NextAction.ACQUIRE_LEAN_GRAPH)
    if not state.semantic_review_current:
        return V11Decision(V11NextAction.REVIEW_SEMANTIC_DELTA)
    if not state.compiled_inputs_current:
        return V11Decision(V11NextAction.REBUILD)
    if not state.realization_current:
        return V11Decision(V11NextAction.REPAIR_REALIZATION)
    if not state.plan_identity_current:
        return V11Decision(V11NextAction.PUBLISH_PLAN)
    if not state.final_source_audit_current:
        return V11Decision(V11NextAction.PERFORM_FINAL_SOURCE_AUDIT)
    if state.worker is V11WorkerDisposition.STATE_ERROR:
        return V11Decision(V11NextAction.INSPECT_WORKER_RECOVERY)
    if state.worker is V11WorkerDisposition.SAME_PLAN_FAILED:
        return V11Decision(V11NextAction.INSPECT_FAILED_WORKER)
    if state.worker is V11WorkerDisposition.DIFFERENT_PLAN:
        return V11Decision(
            V11NextAction.RUN_STRICT_CLOSEOUT,
            requires_new_worker=True,
        )
    return V11Decision(V11NextAction.RUN_STRICT_CLOSEOUT)
