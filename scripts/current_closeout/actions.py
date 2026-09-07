#!/usr/bin/env python3
"""One operator-action adapter for the pure current-v11 closeout reducer.

The reducer owns transition ordering.  This module only renders its one
decision as a bounded command or inspection action.  It performs no file
reads, semantic validation, graph discovery, receipt publication, or worker
launch.  Keeping every current action in one exhaustive adapter prevents an
early and a late scheduler from drifting into different protocols.
"""

from __future__ import annotations

import shlex
from collections.abc import Iterable, Mapping
from types import MappingProxyType
from typing import Any

from scripts.current_closeout.reducer import (
    V11CloseoutState,
    V11Decision,
    V11NextAction,
    V11WorkerDisposition,
    reduce_v11_closeout,
)

PLANNER_ENTRYPOINT = "scripts/closeout_reuse_plan.py"
WORKER_ENTRYPOINT = "scripts/run_paper_closeout.py"
CURRENT_PYTHON_ACTION_SERVICES = MappingProxyType(
    {
        PLANNER_ENTRYPOINT: ("scripts.current_closeout.planner", "main"),
        WORKER_ENTRYPOINT: ("scripts.current_closeout.worker", "main"),
    }
)
CURRENT_PYTHON_ACTION_ENTRYPOINTS = frozenset(CURRENT_PYTHON_ACTION_SERVICES)


def classify_v11_worker_disposition(
    prior_execution: Mapping[str, Any] | None,
    *,
    prior_execution_error: str,
    plan_identity: str,
    plan_identity_schema: str,
) -> V11WorkerDisposition:
    """Classify a worker only by its relation to one exact current plan."""

    if prior_execution_error:
        return V11WorkerDisposition.STATE_ERROR
    if not isinstance(prior_execution, Mapping):
        return V11WorkerDisposition.ABSENT
    if prior_execution.get("state") != "complete":
        return V11WorkerDisposition.STATE_ERROR
    result = prior_execution.get("result")
    result = result if isinstance(result, Mapping) else {}
    same_plan = (
        str(result.get("operational_plan_identity") or "") == plan_identity
        and str(result.get("operational_plan_identity_schema") or "")
        == plan_identity_schema
    )
    if not same_plan:
        return V11WorkerDisposition.DIFFERENT_PLAN
    # The planner already checked the canonical accepted graph first. A
    # completed same-plan worker that reaches this branch therefore did not
    # publish while its issuer-protected CurrentCloseoutPass was alive. Its
    # serialized result is diagnostics, never deferred acceptance authority.
    return V11WorkerDisposition.SAME_PLAN_FAILED


def _action(
    action_id: str,
    argv: Iterable[str],
    *,
    state: str,
    reason: str,
    **extra: Any,
) -> dict[str, Any]:
    command = [str(item) for item in argv]
    return {
        "id": action_id,
        "state": state,
        "required": True,
        "argv": command,
        "command": shlex.join(command),
        "reason": reason,
        **extra,
    }


def _replan_action(
    paper: str,
    *,
    action_id: str,
    state: str,
    reason: str,
) -> dict[str, Any]:
    return _action(
        action_id,
        ["python3", PLANNER_ENTRYPOINT, "--paper", paper],
        state=state,
        reason=reason,
    )


def render_v11_operator_actions(
    decision: V11Decision,
    *,
    paper: str,
    plan_identity: str = "",
    final_holistic_surface_identity: str = "",
    deep_paper_prose: bool = False,
    structure_errors: Iterable[str] = (),
    semantic_errors: Iterable[str] = (),
    realization_receipt_preflight: Mapping[str, Any] | None = None,
    final_source_audit_errors: Iterable[str] = (),
    prior_execution_error: str = "",
) -> list[dict[str, Any]]:
    """Render every reducer decision without choosing another transition."""

    action = decision.action
    structure = [str(error) for error in structure_errors if str(error).strip()]
    semantic = [str(error) for error in semantic_errors if str(error).strip()]
    final_errors = [
        str(error) for error in final_source_audit_errors if str(error).strip()
    ]
    preflight = dict(realization_receipt_preflight or {})

    if action is V11NextAction.REUSE_ACCEPTED_GRAPH:
        return []
    if action is V11NextAction.REPAIR_STRUCTURE:
        return [
            _action(
                "resolve_static_closeout_blockers",
                [],
                state="ready_now",
                reason=(
                    "; ".join(structure)
                    or "the typed paper/source/proof structure is incomplete"
                ),
                errors=structure,
            )
        ]
    if action is V11NextAction.ACQUIRE_LEAN_GRAPH:
        return [
            _action(
                "prepare_v11_lean_review_graph",
                [
                    "python3",
                    PLANNER_ENTRYPOINT,
                    "--paper",
                    paper,
                    "--prepare-v11-lean-review-graph",
                ],
                state="ready_now",
                reason=(
                    "acquire the one Lean-owned source-claim and prerequisite "
                    "graph before semantic review"
                ),
            ),
            _replan_action(
                paper,
                action_id="replan_after_v11_lean_review_graph",
                state="after_lean_graph_preparation",
                reason="validate the acquired graph before semantic review",
            ),
        ]
    if action is V11NextAction.REVIEW_SEMANTIC_DELTA:
        return [
            _action(
                "repair_current_v11_audit",
                [],
                state="ready_now",
                reason=(
                    "; ".join(semantic)
                    or "the current graph-native semantic review has unresolved items"
                ),
                errors=semantic,
            ),
            _replan_action(
                paper,
                action_id="replan_after_current_v11_repair",
                state="after_manual_semantic_repair",
                reason="revalidate the repaired graph-native audit before closeout",
            ),
        ]
    if action is V11NextAction.REBUILD:
        return [
            _action(
                "paper_build",
                ["env", "LEAN_NUM_THREADS=1", "lake", "build", f"+{paper}"],
                state="ready_now",
                reason=(
                    "restore the compiled paper artifact without reopening "
                    "semantic review"
                ),
            ),
            _replan_action(
                paper,
                action_id="replan_after_build",
                state="after_paper_build",
                reason="validate the rebuilt artifact before freezing closeout inputs",
            ),
        ]
    if action is V11NextAction.REPAIR_REALIZATION:
        raw_errors = preflight.get("errors")
        errors = (
            [str(error) for error in raw_errors]
            if isinstance(raw_errors, list)
            else []
        )
        return [
            _action(
                "resolve_realization_receipt_preflight",
                [],
                state="ready_now",
                reason=(
                    "the current Lean graph does not authenticate every exact "
                    "source-to-Spec proof realization"
                    + (": " + "; ".join(errors[:3]) if errors else "")
                ),
                errors=errors,
            )
        ]
    if action is V11NextAction.PUBLISH_PLAN:
        return [
            _action(
                "publish_current_closeout_plan",
                [],
                state="internal_transition",
                reason=(
                    "freeze the exact current inputs and publish the operational "
                    "plan before the final source audit or worker"
                ),
            )
        ]
    if action is V11NextAction.PERFORM_FINAL_SOURCE_AUDIT:
        return [
            _action(
                "perform_final_adversarial_source_audit",
                [],
                state="ready_now",
                reason=(
                    "perform only the missing independent final review identified "
                    "below against the frozen policy-selected source-and-Lean "
                    "surface; retain valid prior panel entries and bind each new "
                    "audit artifact to this exact comparison identity"
                ),
                final_holistic_surface_identity=final_holistic_surface_identity,
                errors=final_errors,
            ),
            _replan_action(
                paper,
                action_id="replan_after_final_adversarial_source_audit",
                state="after_final_adversarial_source_audit",
                reason=(
                    "verify that the required independent reviewer panel names the "
                    "unchanged comparison surface before scheduling strict closeout"
                ),
            ),
        ]
    status_argv = [
        "python3",
        WORKER_ENTRYPOINT,
        "--paper",
        paper,
        "--status",
    ]
    if action is V11NextAction.INSPECT_WORKER_RECOVERY:
        return [
            _action(
                "inspect_closeout_recovery",
                status_argv,
                state="ready_now",
                reason=(
                    prior_execution_error
                    or "the current worker state is not a completed exact-plan result"
                ),
            )
        ]
    if action is V11NextAction.INSPECT_FAILED_WORKER:
        retry_argv = [
            "python3",
            WORKER_ENTRYPOINT,
            "--paper",
            paper,
        ]
        if deep_paper_prose:
            retry_argv.append("--deep-paper-prose")
        retry_argv.extend(["--plan-identity", plan_identity, "--new-run"])
        return [
            _action(
                "inspect_existing_closeout",
                status_argv,
                state="ready_now",
                reason=(
                    "the same current-input plan has a terminal result but no "
                    "current accepted graph; inspect the record before explicitly "
                    "starting a replacement in-process transaction"
                ),
            ),
            _action(
                "strict_closeout_after_failure_confirmation",
                retry_argv,
                state="after_operator_confirms_retry_required",
                reason=(
                    "retry the exact failed plan only after inspecting its durable "
                    "terminal record"
                ),
            ),
        ]
    if action is V11NextAction.RUN_STRICT_CLOSEOUT:
        argv = [
            "python3",
            WORKER_ENTRYPOINT,
            "--paper",
            paper,
        ]
        if deep_paper_prose:
            argv.append("--deep-paper-prose")
        argv.extend(["--plan-identity", plan_identity])
        if decision.requires_new_worker:
            argv.append("--new-run")
        return [
            _action(
                "strict_closeout",
                argv,
                state="ready_now",
                reason="run the one exact-plan graph-native closeout transaction",
            )
        ]
    raise AssertionError(f"unhandled v11 action: {action!r}")


def schedule_v11_closeout(
    state: V11CloseoutState,
    *,
    paper: str,
    plan_identity: str = "",
    final_holistic_surface_identity: str = "",
    deep_paper_prose: bool = False,
    structure_errors: Iterable[str] = (),
    semantic_errors: Iterable[str] = (),
    realization_receipt_preflight: Mapping[str, Any] | None = None,
    final_source_audit_errors: Iterable[str] = (),
    prior_execution_error: str = "",
    summary: Mapping[str, Any] | None = None,
    include_final_source_audit_projection: bool = False,
) -> dict[str, Any]:
    """Reduce one validated state and render its sole current action."""

    decision = reduce_v11_closeout(state)
    preflight = dict(
        realization_receipt_preflight
        or {"state": "not_checked", "current": True, "required": False}
    )
    actions = render_v11_operator_actions(
        decision,
        paper=paper,
        plan_identity=plan_identity,
        final_holistic_surface_identity=final_holistic_surface_identity,
        deep_paper_prose=deep_paper_prose,
        structure_errors=structure_errors,
        semantic_errors=semantic_errors,
        realization_receipt_preflight=preflight,
        final_source_audit_errors=final_source_audit_errors,
        prior_execution_error=prior_execution_error,
    )
    current_summary = summary or {}
    ready_action = next(
        (item for item in actions if item.get("state") == "ready_now"),
        actions[0] if actions else None,
    )
    result: dict[str, Any] = {
        "semantic_review_reuse_ready": state.semantic_review_current,
        "compiled_artifacts_ready": state.compiled_inputs_current,
        "closeout_complete": decision.action is V11NextAction.REUSE_ACCEPTED_GRAPH,
        "next_action": ready_action,
        "future_reuse_pin_maintenance": {
            "required_for_this_closeout": False,
            "statement_items": int(
                current_summary.get("statement_future_reuse_pin_missing") or 0
            ),
            "coverage_items": int(
                current_summary.get("coverage_future_reuse_pin_missing") or 0
            ),
            "policy": "historical reuse pins are not current-v11 obligations",
        },
        "realization_receipt_preflight": preflight,
        "v11_reducer": {
            "action": decision.action.value,
            "worker_disposition": state.worker.value,
            (
                "legacy_adoption_consulted"
                if include_final_source_audit_projection
                else "legacy_scheduler_consulted"
            ): False,
            "acceptance_credential": False,
        },
        "actions": actions,
    }
    if include_final_source_audit_projection:
        final_errors = [
            str(error)
            for error in final_source_audit_errors
            if str(error).strip()
        ]
        result.update(
            {
                "final_holistic_audit_ready": state.final_source_audit_current,
                "final_holistic_audit_errors": final_errors,
            }
        )
    return result
