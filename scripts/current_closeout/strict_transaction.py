"""Canonical stage registry for one current-protocol strict closeout.

This module is deliberately declarative.  The executor owns the work and the
worker owns survivability, but both must describe the same transaction rather
than maintaining independent progress constants.
"""

from __future__ import annotations

from collections.abc import Sequence

STRICT_CLOSEOUT_EXECUTION_STAGES = (
    "closeout_artifact_preflight",
    "acquire_exact_context",
    "route_schema_preflight",
    "acquire_lean_context",
    "current_evidence_transaction_preflight",
    "paper_root_build",
    "primary_paper_gate",
    "evidence_integrity",
    "conclusion_provenance",
    "final_input_check",
)
STRICT_CLOSEOUT_STAGE_COUNT = len(STRICT_CLOSEOUT_EXECUTION_STAGES)
_STRICT_CLOSEOUT_EXECUTION_STAGE_SET = frozenset(
    STRICT_CLOSEOUT_EXECUTION_STAGES
)
class StrictTransactionError(ValueError):
    """Current closeout progress is not an exact runtime-stage prefix."""


def current_closeout_execution_projection(
    completed_stages: Sequence[str] = (),
) -> dict[str, object]:
    """Project the exact current runtime-gate prefix without minting receipts.

    The executor-owned runtime capability, not this presentation projection,
    proves that the gates ran.  Requiring an exact prefix keeps progress output
    fail closed while avoiding a second legacy-shaped stage DAG.
    """

    completed = tuple(completed_stages)
    if completed != STRICT_CLOSEOUT_EXECUTION_STAGES[: len(completed)]:
        raise StrictTransactionError(
            "current closeout progress is not an exact execution-stage prefix"
        )
    completed_set = frozenset(completed)
    next_stage = (
        STRICT_CLOSEOUT_EXECUTION_STAGES[len(completed)]
        if len(completed) < STRICT_CLOSEOUT_STAGE_COUNT
        else None
    )
    return {
        "schema": 2,
        "acceptance_credential": False,
        "operational_scheduling_only": True,
        "current_prefix_length": len(completed),
        "next_stage": next_stage,
        "stages": [
            {
                "id": stage,
                "dependencies": (
                    []
                    if index == 0
                    else [STRICT_CLOSEOUT_EXECUTION_STAGES[index - 1]]
                ),
                "state": "completed" if stage in completed_set else "pending",
            }
            for index, stage in enumerate(STRICT_CLOSEOUT_EXECUTION_STAGES)
        ],
    }


def require_strict_closeout_stage(stage: str) -> str:
    """Return a registered stage name or reject implementation drift."""

    if stage not in _STRICT_CLOSEOUT_EXECUTION_STAGE_SET:
        raise ValueError(f"unregistered strict closeout stage: {stage!r}")
    return stage


__all__ = [
    "STRICT_CLOSEOUT_EXECUTION_STAGES",
    "STRICT_CLOSEOUT_STAGE_COUNT",
    "StrictTransactionError",
    "current_closeout_execution_projection",
    "require_strict_closeout_stage",
]
