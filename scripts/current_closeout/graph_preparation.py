"""Acquire and checkpoint one non-accepting current-v11 Lean review graph.

This service owns graph preparation independently of legacy evidence lanes and
presentation rendering. It elaborates the exact typed paper transaction,
validates the retained Lean surface, and persists only the content-addressed
operational graph checkpoint. Human packet/dashboard caches are derived later
by their renderer and are never part of graph acquisition or acceptance.
"""

from __future__ import annotations

from collections.abc import Mapping
from pathlib import Path
from types import MappingProxyType

from scripts.current_closeout.evidence_transaction import (
    build_current_v11_context_with_graph_checkpoint,
    build_current_v11_evidence_run_context,
)
from scripts.current_closeout.lean_review_graph import (
    V11LeanReviewGraphCarrierMismatch,
    checkpoint_builder_issued_v11_lean_review_graph,
    stable_json_sha256,
)
from scripts.current_closeout.realization import V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
from scripts.current_closeout.review_surface import (
    V11LeanReviewSurface,
    build_accepting_v11_review_surface,
)
from scripts.obligation_routes import EvidenceRouteSet, ObligationRouteError


def _changed_input_error(context: object) -> str:
    changed_input_paths = getattr(context, "changed_input_paths", None)
    if not callable(changed_input_paths):
        return "v11 Lean graph transaction cannot verify frozen inputs"
    changed = tuple(changed_input_paths())
    if not changed:
        return ""
    return "v11 Lean graph inputs changed during preparation: " + "; ".join(
        sorted(str(path) for path in changed)
    )


def prepare_v11_lean_review_graph(
    repository_root: Path,
    folder: Path,
) -> Mapping[str, object]:
    """Acquire and checkpoint one exact non-accepting current-v11 graph."""

    root = repository_root.resolve()
    paper_folder = folder.resolve()
    context = build_current_v11_context_with_graph_checkpoint(
        paper_folder,
        repository_root=root,
    )
    if not context.v11_lean_claim_graph_selected:
        raise ValueError("paper does not select the v11 Lean claim-graph protocol")
    try:
        route_set = EvidenceRouteSet.from_source_map(context.statement_map)
    except ObligationRouteError as exc:
        raise ValueError("v11 Lean graph has invalid typed routes: " + str(exc)) from exc
    expected_specs = route_set.result_specifications()
    if not expected_specs:
        raise ValueError("v11 Lean graph has no selected result specifications")

    try:
        surface = build_accepting_v11_review_surface(
            root,
            paper_folder,
            expected_specs,
            context=context,
        )
    except V11LeanReviewGraphCarrierMismatch:
        # A checkpoint is an optimization, not authority. Reacquire once from
        # the exact current transaction and apply the same strict projection.
        context = build_current_v11_evidence_run_context(
            paper_folder,
            repository_root=root,
        )
        surface = build_accepting_v11_review_surface(
            root,
            paper_folder,
            expected_specs,
            context=context,
        )
    if not isinstance(surface, V11LeanReviewSurface):
        raise TypeError("v11 Lean graph builder returned a non-accepting projection")

    provider = surface.build_input_provider
    if not hasattr(provider, "finalize_unchanged") or not provider.finalize_unchanged():
        raise ValueError("Lean import-closure inputs changed during graph preparation")
    mutation_error = _changed_input_error(context)
    if mutation_error:
        raise ValueError(mutation_error)

    reference = checkpoint_builder_issued_v11_lean_review_graph(
        paper_folder,
        context,
        repository_root=root,
    )
    if reference is None:
        raise ValueError("completed v11 Lean graph could not be checkpointed")

    diagnostics = dict(context.runtime_cache_diagnostics())
    return MappingProxyType(
        {
            "schema": 1,
            "paper": paper_folder.name,
            "acceptance_credential": False,
            "operational_scheduling_only": True,
            "semantic_judgments_issued": False,
            "presentation_materialized": False,
            "graph_reference": dict(reference),
            "graph_request_sha256": stable_json_sha256(surface.graph_request),
            "specification_count": len(surface.semantic_targets),
            "paper_prerequisite_count": len(surface.paper_semantic_targets),
            "library_prerequisite_count": len(surface.library_semantic_targets),
            "proof_contract_count": len(surface.semantic_contracts),
            "checkpoint_reused": diagnostics.get("v11_graph_carrier_reuses", 0) > 0,
            "runtime_cache_diagnostics": diagnostics,
        }
    )


def persist_retained_v11_lean_review_graph(
    repository_root: Path,
    folder: Path,
    evidence_context: object | None,
) -> str:
    """Checkpoint an already-retained current graph without rendering it."""

    if evidence_context is None:
        return ""
    if (
        getattr(evidence_context, "source_semantic_lane", "")
        != V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
    ):
        return ""
    try:
        checkpoint_builder_issued_v11_lean_review_graph(
            folder.resolve(),
            evidence_context,
            repository_root=repository_root.resolve(),
        )
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        # The checkpoint grants no acceptance. A failure is visible so a later
        # planner does not silently reacquire work that might have been saved.
        return str(exc)
    return ""


__all__ = [
    "persist_retained_v11_lean_review_graph",
    "prepare_v11_lean_review_graph",
]
