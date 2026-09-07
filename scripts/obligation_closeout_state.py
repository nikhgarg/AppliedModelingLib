#!/usr/bin/env python3
"""Thin repository adapter for the immutable obligation-evidence architecture.

The pure planner owns graph difference and integrity verification. The store
owns exact content-addressed retrieval. This module joins those two boundaries
without invoking Lean, an LLM, a legacy aggregate audit, or a repair fallback.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any, Iterable, Mapping

try:
    from scripts.obligation_evidence_graph import ObligationEvidenceGraph
    from scripts.obligation_evidence_planner import (
        ObligationEvidencePlan,
        ObligationEvidencePlanningError,
        VerifiedPaperObligationEvidence,
        plan_complete_paper_obligation_evidence,
        verify_complete_paper_obligation_evidence,
    )
    from scripts.obligation_evidence_store import (
        ObligationEvidenceStoreError,
        load_obligation_evidence_store_snapshot,
        load_paper_obligation_bundle,
    )
    from scripts.obligation_paper_index import PaperObligationIndex
    from scripts.obligation_preflight import ObligationStructuralPreflight
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from obligation_evidence_graph import ObligationEvidenceGraph
    from obligation_evidence_planner import (
        ObligationEvidencePlan,
        ObligationEvidencePlanningError,
        VerifiedPaperObligationEvidence,
        plan_complete_paper_obligation_evidence,
        verify_complete_paper_obligation_evidence,
    )
    from obligation_evidence_store import (
        ObligationEvidenceStoreError,
        load_obligation_evidence_store_snapshot,
        load_paper_obligation_bundle,
    )
    from obligation_paper_index import PaperObligationIndex
    from obligation_preflight import ObligationStructuralPreflight


class ObligationCloseoutStateError(ValueError):
    """Stored evidence is unavailable or disagrees with the required paper."""


def plan_stored_paper_obligations(
    root: Path,
    paper: str,
    paper_index: PaperObligationIndex | Mapping[str, Any],
    required_graph: ObligationEvidenceGraph,
    *,
    preflight: ObligationStructuralPreflight,
    authenticated_authority_sha256s: Iterable[str],
) -> ObligationEvidencePlan:
    """Return the exact resumable queue from independently stored objects."""

    try:
        snapshot = load_obligation_evidence_store_snapshot(
            root,
            paper,
            required_graph,
        )
        return plan_complete_paper_obligation_evidence(
            paper_index,
            required_graph,
            snapshot.available_leaves,
            snapshot.issuances,
            preflight=preflight,
            authenticated_authority_sha256s=authenticated_authority_sha256s,
        )
    except (ObligationEvidenceStoreError, ObligationEvidencePlanningError) as exc:
        raise ObligationCloseoutStateError(str(exc)) from exc


def verify_current_stored_paper_obligations(
    root: Path,
    paper: str,
    paper_index: PaperObligationIndex,
    required_graph: ObligationEvidenceGraph,
    *,
    preflight: ObligationStructuralPreflight,
    authenticated_authority_sha256s: Iterable[str],
) -> VerifiedPaperObligationEvidence:
    """Verify the selected bundle exactly; never plan, produce, or repair."""

    try:
        loaded = load_paper_obligation_bundle(root, paper)
    except ObligationEvidenceStoreError as exc:
        raise ObligationCloseoutStateError(str(exc)) from exc
    if loaded.graph.graph_sha256 != required_graph.graph_sha256:
        raise ObligationCloseoutStateError(
            "current obligation bundle selects a different required graph"
        )
    if loaded.paper_index.index_sha256 != paper_index.index_sha256:
        raise ObligationCloseoutStateError(
            "current obligation bundle selects a different complete paper index"
        )
    try:
        return verify_complete_paper_obligation_evidence(
            paper_index,
            required_graph,
            {
                digest: leaf.projection()
                for digest, leaf in loaded.graph.leaves.items()
            },
            loaded.issuances.values(),
            preflight=preflight,
            authenticated_authority_sha256s=authenticated_authority_sha256s,
        )
    except ObligationEvidencePlanningError as exc:
        raise ObligationCloseoutStateError(str(exc)) from exc
