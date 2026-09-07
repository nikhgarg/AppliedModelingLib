"""Exact frozen-input mutation check for current closeout transactions."""

from __future__ import annotations

from pathlib import Path

from scripts.evidence_run_context import V11EvidenceRunContext


def current_evidence_input_mutations(context: object) -> tuple[Path, ...]:
    """Return changed current input paths, rejecting a foreign context.

    This is a byte-identity check only.  Semantic validators and Lean build
    providers retain their separate accepting obligations.
    """

    if not isinstance(context, V11EvidenceRunContext) or not context.issued_by_builder:
        raise ValueError(
            "current input mutation check requires its exact builder-issued "
            "v11 transaction"
        )
    return context.changed_input_paths()


__all__ = ["current_evidence_input_mutations"]
