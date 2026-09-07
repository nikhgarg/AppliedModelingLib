#!/usr/bin/env python3
"""Pure leaf-DAG planner and terminal integrity verifier for closeout evidence.

This module never reads a repository, invokes Lean, calls a semantic judge, or
repairs evidence. It compares one required immutable graph with supplied leaf
objects and issuance attestations, then reports exact work in dependency order.
An existing semantic leaf without an authenticated issuance is an attestation
task, not a request to rerun the semantic producer.

The terminal helper proves graph/evidence/authority completeness only. Current
source bytes, Lean controls, focused build, and the frozen-input mutation guard
remain separate current-control authorities required by the final closeout
verifier.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, Iterable, Mapping

try:
    from scripts.obligation_evidence_graph import (
        ObligationEvidenceGraph,
        ObligationKind,
        diff_obligation_graph,
    )
    from scripts.obligation_evidence_issuance import (
        ObligationEvidenceIssuance,
        ObligationEvidenceIssuanceError,
        validate_obligation_evidence_issuance,
    )
    from scripts.obligation_paper_index import (
        PaperObligationIndex,
        PaperObligationIndexError,
        validate_paper_obligation_index,
    )
    from scripts.obligation_preflight import ObligationStructuralPreflight
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from obligation_evidence_graph import (
        ObligationEvidenceGraph,
        ObligationKind,
        diff_obligation_graph,
    )
    from obligation_evidence_issuance import (
        ObligationEvidenceIssuance,
        ObligationEvidenceIssuanceError,
        validate_obligation_evidence_issuance,
    )
    from obligation_paper_index import (
        PaperObligationIndex,
        PaperObligationIndexError,
        validate_paper_obligation_index,
    )
    from obligation_preflight import ObligationStructuralPreflight


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class ObligationEvidencePlanningError(ValueError):
    """The planner inputs are malformed or terminal verification is incomplete."""


def _digests(values: Iterable[object], field: str) -> tuple[str, ...]:
    result: set[str] = set()
    for value in values:
        digest = str(value or "").strip().lower()
        if not SHA256_RE.fullmatch(digest):
            raise ObligationEvidencePlanningError(f"{field} is not SHA-256")
        result.add(digest)
    return tuple(sorted(result))


@dataclass(frozen=True)
class ObligationWorkItem:
    """One exact non-producing action selected by graph difference."""

    leaf_sha256: str
    kind: ObligationKind
    action: str

    def projection(self) -> dict[str, str]:
        return {
            "leaf_sha256": self.leaf_sha256,
            "kind": self.kind.value,
            "action": self.action,
        }


@dataclass(frozen=True)
class ObligationEvidencePlan:
    graph_sha256: str
    reusable_leaf_sha256s: tuple[str, ...]
    missing_leaf_sha256s: tuple[str, ...]
    corrupt_leaf_sha256s: tuple[str, ...]
    unattested_leaf_sha256s: tuple[str, ...]
    corrupt_issuance_sha256s: tuple[str, ...]
    blocked_by_missing: Mapping[str, tuple[str, ...]]
    work_queue: tuple[ObligationWorkItem, ...]

    @property
    def complete(self) -> bool:
        return not (
            self.missing_leaf_sha256s
            or self.corrupt_leaf_sha256s
            or self.unattested_leaf_sha256s
            or self.corrupt_issuance_sha256s
            or self.blocked_by_missing
        )

    def projection(self) -> dict[str, Any]:
        return {
            "schema": 1,
            "acceptance_credential": False,
            "graph_sha256": self.graph_sha256,
            "complete": self.complete,
            "reusable_leaf_sha256s": list(self.reusable_leaf_sha256s),
            "missing_leaf_sha256s": list(self.missing_leaf_sha256s),
            "corrupt_leaf_sha256s": list(self.corrupt_leaf_sha256s),
            "unattested_leaf_sha256s": list(self.unattested_leaf_sha256s),
            "corrupt_issuance_sha256s": list(self.corrupt_issuance_sha256s),
            "blocked_by_missing": {
                key: list(value) for key, value in sorted(self.blocked_by_missing.items())
            },
            "work_queue": [item.projection() for item in self.work_queue],
        }


@dataclass(frozen=True)
class VerifiedObligationEvidence:
    """Cheap integrity result; not the final current-control acceptance token."""

    graph_sha256: str
    leaf_sha256s: tuple[str, ...]
    authenticated_authority_sha256s: tuple[str, ...]

    def projection(self) -> dict[str, Any]:
        return {
            "schema": 1,
            "acceptance_credential": False,
            "graph_sha256": self.graph_sha256,
            "leaf_sha256s": list(self.leaf_sha256s),
            "authenticated_authority_sha256s": list(
                self.authenticated_authority_sha256s
            ),
        }


@dataclass(frozen=True)
class VerifiedPaperObligationEvidence:
    """Complete paper-surface integrity result, still pending current controls."""

    paper_index_sha256: str
    evidence: VerifiedObligationEvidence

    def projection(self) -> dict[str, Any]:
        return {
            "schema": 1,
            "acceptance_credential": False,
            "complete_paper_surface": True,
            "paper_index_sha256": self.paper_index_sha256,
            "evidence": self.evidence.projection(),
        }


def plan_obligation_evidence(
    required_graph: ObligationEvidenceGraph,
    available_leaves: Mapping[str, object],
    issuances: Iterable[ObligationEvidenceIssuance | Mapping[str, Any]],
    *,
    authenticated_authority_sha256s: Iterable[str],
) -> ObligationEvidencePlan:
    """Return exact missing/corrupt/unattested leaves without producing work."""

    authorities = set(
        _digests(authenticated_authority_sha256s, "authenticated authority")
    )
    difference = diff_obligation_graph(required_graph, available_leaves)
    issued_by_leaf: dict[str, set[str]] = {}
    corrupt_issuances: set[str] = set()
    for raw in issuances:
        projection = raw.projection() if isinstance(raw, ObligationEvidenceIssuance) else raw
        supplied = (
            str(projection.get("issuance_sha256") or "").strip().lower()
            if isinstance(projection, Mapping)
            else ""
        )
        try:
            issuance = validate_obligation_evidence_issuance(projection)
        except ObligationEvidenceIssuanceError:
            if SHA256_RE.fullmatch(supplied):
                corrupt_issuances.add(supplied)
            else:
                raise ObligationEvidencePlanningError(
                    "malformed issuance has no attributable SHA-256 identity"
                )
            continue
        if issuance.authority_sha256 in authorities:
            issued_by_leaf.setdefault(issuance.leaf_sha256, set()).add(
                issuance.issuance_sha256
            )

    present = set(difference.reusable_leaf_sha256s)
    unattested = present - set(issued_by_leaf)
    reusable = present - unattested
    reproduce = set(difference.missing_leaf_sha256s) | set(
        difference.corrupt_leaf_sha256s
    )
    queue: list[ObligationWorkItem] = []
    for digest in required_graph.topological_leaf_sha256s:
        leaf = required_graph.leaves[digest]
        if digest in reproduce:
            queue.append(
                ObligationWorkItem(
                    leaf_sha256=digest,
                    kind=leaf.kind,
                    action="produce_leaf",
                )
            )
        elif digest in unattested:
            queue.append(
                ObligationWorkItem(
                    leaf_sha256=digest,
                    kind=leaf.kind,
                    action="authenticate_existing_leaf",
                )
            )
    return ObligationEvidencePlan(
        graph_sha256=required_graph.graph_sha256,
        reusable_leaf_sha256s=tuple(sorted(reusable)),
        missing_leaf_sha256s=difference.missing_leaf_sha256s,
        corrupt_leaf_sha256s=difference.corrupt_leaf_sha256s,
        unattested_leaf_sha256s=tuple(sorted(unattested)),
        corrupt_issuance_sha256s=tuple(sorted(corrupt_issuances)),
        blocked_by_missing=MappingProxyType(dict(difference.blocked_by_missing)),
        work_queue=tuple(queue),
    )


def _require_complete_plan(plan: ObligationEvidencePlan) -> None:
    if plan.complete:
        return
    details = []
    for label, values in (
        ("missing", plan.missing_leaf_sha256s),
        ("corrupt", plan.corrupt_leaf_sha256s),
        ("unattested", plan.unattested_leaf_sha256s),
        ("corrupt issuance", plan.corrupt_issuance_sha256s),
        ("blocked", tuple(plan.blocked_by_missing)),
    ):
        if values:
            details.append(f"{label}: {', '.join(values)}")
    raise ObligationEvidencePlanningError(
        "obligation evidence is incomplete; " + "; ".join(details)
    )


def _validated_complete_paper_index(
    paper_index: PaperObligationIndex | Mapping[str, Any],
    graph: ObligationEvidenceGraph,
    preflight: ObligationStructuralPreflight,
) -> PaperObligationIndex:
    projection = (
        paper_index.projection()
        if isinstance(paper_index, PaperObligationIndex)
        else paper_index
    )
    try:
        return validate_paper_obligation_index(
            projection,
            graph=graph,
            require_complete=True,
            preflight=preflight,
        )
    except PaperObligationIndexError as exc:
        raise ObligationEvidencePlanningError(str(exc)) from exc


def verify_complete_obligation_evidence(
    required_graph: ObligationEvidenceGraph,
    available_leaves: Mapping[str, object],
    issuances: Iterable[ObligationEvidenceIssuance | Mapping[str, Any]],
    *,
    authenticated_authority_sha256s: Iterable[str],
) -> VerifiedObligationEvidence:
    """Fail with exact leaf IDs; never invoke a planner fallback or producer."""

    authorities = _digests(
        authenticated_authority_sha256s, "authenticated authority"
    )
    plan = plan_obligation_evidence(
        required_graph,
        available_leaves,
        issuances,
        authenticated_authority_sha256s=authorities,
    )
    _require_complete_plan(plan)
    return VerifiedObligationEvidence(
        graph_sha256=required_graph.graph_sha256,
        leaf_sha256s=tuple(sorted(required_graph.leaves)),
        authenticated_authority_sha256s=authorities,
    )


def plan_complete_paper_obligation_evidence(
    paper_index: PaperObligationIndex | Mapping[str, Any],
    required_graph: ObligationEvidenceGraph,
    available_leaves: Mapping[str, object],
    issuances: Iterable[ObligationEvidenceIssuance | Mapping[str, Any]],
    *,
    preflight: ObligationStructuralPreflight,
    authenticated_authority_sha256s: Iterable[str],
) -> ObligationEvidencePlan:
    """Plan only after the cheap preflight proves the graph is the whole paper."""

    _validated_complete_paper_index(paper_index, required_graph, preflight)
    return plan_obligation_evidence(
        required_graph,
        available_leaves,
        issuances,
        authenticated_authority_sha256s=authenticated_authority_sha256s,
    )


def verify_complete_paper_obligation_evidence(
    paper_index: PaperObligationIndex | Mapping[str, Any],
    required_graph: ObligationEvidenceGraph,
    available_leaves: Mapping[str, object],
    issuances: Iterable[ObligationEvidenceIssuance | Mapping[str, Any]],
    *,
    preflight: ObligationStructuralPreflight,
    authenticated_authority_sha256s: Iterable[str],
) -> VerifiedPaperObligationEvidence:
    """Require a complete preflight-owned paper index before graph verification."""

    index = _validated_complete_paper_index(
        paper_index, required_graph, preflight
    )
    authorities = _digests(
        authenticated_authority_sha256s, "authenticated authority"
    )
    plan = plan_obligation_evidence(
        required_graph,
        available_leaves,
        issuances,
        authenticated_authority_sha256s=authorities,
    )
    _require_complete_plan(plan)
    evidence = VerifiedObligationEvidence(
        graph_sha256=required_graph.graph_sha256,
        leaf_sha256s=tuple(sorted(required_graph.leaves)),
        authenticated_authority_sha256s=authorities,
    )
    return VerifiedPaperObligationEvidence(
        paper_index_sha256=index.index_sha256,
        evidence=evidence,
    )
