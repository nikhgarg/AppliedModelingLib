#!/usr/bin/env python3
"""The one accepting object for a completely verified paper obligation DAG.

The semantic graph remains an immutable reusable subgraph.  Acceptance adds one
terminal ``paper_closure`` root that binds the complete preflight-owned paper
index and the registered verifier that rechecked all current controls.  No
bundle, receipt, report, pointer, or issuance object independently grants
acceptance.
"""

from __future__ import annotations

import sys
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.obligation_evidence_contracts import (
    PAPER_CLOSURE_CONTRACT,
    STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT,
)
from scripts.obligation_evidence_graph import (
    ACCEPTED_OBLIGATION_EVIDENCE_GRAPH_SCHEMA,
    ObligationEvidenceError,
    ObligationEvidenceGraph,
    ObligationEvidenceLeaf,
    ObligationKind,
    build_obligation_graph,
    paper_closure_leaf,
    validate_obligation_graph,
)
from scripts.obligation_paper_bundle import (
    paper_obligation_terminal_verification_sha256,
)
from scripts.obligation_paper_index import (
    PaperObligationIndex,
    PaperObligationIndexError,
    validate_paper_obligation_index,
)
from scripts.obligation_preflight import ObligationStructuralPreflight
from scripts.strict_closeout_authority import (
    StrictCloseoutAuthority,
    StrictCloseoutAuthorityError,
    recorded_strict_closeout_authority,
    validate_strict_closeout_authority,
)


class AcceptedObligationGraphError(ValueError):
    """The purported accepted graph is incomplete or not terminally verified."""


@dataclass(frozen=True)
class AcceptedObligationGraphCredential:
    """Authenticated accepting DAG and its stable semantic subgraph."""

    accepted_graph: ObligationEvidenceGraph
    semantic_graph: ObligationEvidenceGraph
    paper_index: PaperObligationIndex
    closure_leaf: ObligationEvidenceLeaf

    @property
    def graph_sha256(self) -> str:
        """Return the sole machine acceptance-credential identity."""

        return self.accepted_graph.graph_sha256

    @property
    def graph(self) -> ObligationEvidenceGraph:
        """Compatibility-neutral name for validators of semantic controls."""

        return self.semantic_graph


def _semantic_subgraph(
    accepted_graph: ObligationEvidenceGraph,
) -> tuple[ObligationEvidenceGraph, ObligationEvidenceLeaf]:
    try:
        graph = validate_obligation_graph(
            accepted_graph.projection(),
            leaves={
                digest: leaf.projection()
                for digest, leaf in accepted_graph.leaves.items()
            },
        )
    except ObligationEvidenceError as exc:
        raise AcceptedObligationGraphError(str(exc)) from exc
    if (
        graph.schema != ACCEPTED_OBLIGATION_EVIDENCE_GRAPH_SCHEMA
        or len(graph.root_leaf_sha256s) != 1
    ):
        raise AcceptedObligationGraphError(
            "canonical acceptance requires one schema-2 accepted obligation graph"
        )
    closure = graph.leaves[graph.root_leaf_sha256s[0]]
    if (
        closure.kind is not ObligationKind.PAPER_CLOSURE
        or closure.contract_sha256
        not in {
            PAPER_CLOSURE_CONTRACT.contract_sha256,
            STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT.contract_sha256,
        }
    ):
        raise AcceptedObligationGraphError(
            "accepted graph root does not use the registered paper-closure contract"
        )
    try:
        semantic = build_obligation_graph(
            (
                leaf
                for digest, leaf in graph.leaves.items()
                if digest != closure.leaf_sha256
            ),
            root_leaf_sha256s=closure.depends_on,
        )
    except ObligationEvidenceError as exc:
        raise AcceptedObligationGraphError(str(exc)) from exc
    if semantic.graph_sha256 != closure.semantic_payload["semantic_graph_sha256"]:
        raise AcceptedObligationGraphError(
            "accepted graph root binds a different semantic graph"
        )
    return semantic, closure


def build_accepted_obligation_graph(
    semantic_graph: ObligationEvidenceGraph,
    paper_index: PaperObligationIndex,
    *,
    preflight: ObligationStructuralPreflight,
    strict_closeout_authority: StrictCloseoutAuthority,
    final_holistic_audit_surface_sha256: str,
    source_assurance_sha256: str,
) -> AcceptedObligationGraphCredential:
    """Add the sole accepting root after current complete-surface verification."""

    try:
        semantic = validate_obligation_graph(
            semantic_graph.projection(),
            leaves={
                digest: leaf.projection()
                for digest, leaf in semantic_graph.leaves.items()
            },
        )
        if semantic.schema == ACCEPTED_OBLIGATION_EVIDENCE_GRAPH_SCHEMA:
            raise AcceptedObligationGraphError(
                "an accepted graph cannot be nested inside another accepted graph"
            )
        index = validate_paper_obligation_index(
            paper_index.projection(),
            graph=semantic,
            require_complete=True,
            preflight=preflight,
        )
    except (ObligationEvidenceError, PaperObligationIndexError) as exc:
        raise AcceptedObligationGraphError(str(exc)) from exc
    try:
        authority = validate_strict_closeout_authority(strict_closeout_authority)
    except StrictCloseoutAuthorityError as exc:
        raise AcceptedObligationGraphError(str(exc)) from exc
    if authority.paper != preflight.paper:
        raise AcceptedObligationGraphError(
            "strict closeout authority belongs to another paper"
        )
    terminal = paper_obligation_terminal_verification_sha256(
        index,
        semantic,
        final_holistic_audit_surface_sha256=final_holistic_audit_surface_sha256,
        source_assurance_sha256=source_assurance_sha256,
    )
    closure = paper_closure_leaf(
        contract_sha256=STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT.contract_sha256,
        semantic_graph_sha256=semantic.graph_sha256,
        paper_index_sha256=index.index_sha256,
        terminal_verification_sha256=terminal,
        terminal_authority_sha256=authority.authority_sha256,
        semantic_root_leaf_sha256s=semantic.root_leaf_sha256s,
        strict_closeout_authority=authority.projection(),
        final_holistic_audit_surface_sha256=final_holistic_audit_surface_sha256,
        source_assurance_sha256=source_assurance_sha256,
    )
    try:
        accepted = build_obligation_graph(
            [*semantic.leaves.values(), closure],
            root_leaf_sha256s=[closure.leaf_sha256],
        )
    except ObligationEvidenceError as exc:
        raise AcceptedObligationGraphError(str(exc)) from exc
    return validate_accepted_obligation_graph(
        accepted,
        index,
        preflight=preflight,
        authenticated_authority_sha256s=[authority.engine_tree_sha256],
    )


def validate_accepted_obligation_graph(
    accepted_graph: ObligationEvidenceGraph,
    paper_index: PaperObligationIndex,
    *,
    preflight: ObligationStructuralPreflight,
    authenticated_authority_sha256s: Iterable[str],
    require_current_aggregate_identity: bool = True,
) -> AcceptedObligationGraphCredential:
    """Authenticate the accepted graph without running any evidence producer."""

    semantic, closure = _semantic_subgraph(accepted_graph)
    try:
        index = validate_paper_obligation_index(
            paper_index.projection(),
            graph=semantic,
            require_complete=True,
            preflight=preflight,
            require_current_aggregate_identity=(
                require_current_aggregate_identity
            ),
        )
    except PaperObligationIndexError as exc:
        raise AcceptedObligationGraphError(str(exc)) from exc
    payload = closure.semantic_payload
    if payload["paper_index_sha256"] != index.index_sha256:
        raise AcceptedObligationGraphError(
            "accepted graph root binds a different complete paper index"
        )
    current_contract = (
        closure.contract_sha256
        == STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT.contract_sha256
    )
    if current_contract:
        try:
            strict_authority = recorded_strict_closeout_authority(
                payload.get("strict_closeout_authority")
            )
        except StrictCloseoutAuthorityError as exc:
            raise AcceptedObligationGraphError(str(exc)) from exc
        if strict_authority.paper != preflight.paper:
            raise AcceptedObligationGraphError(
                "recorded strict closeout authority belongs to another paper"
            )
        if payload["terminal_authority_sha256"] != strict_authority.authority_sha256:
            raise AcceptedObligationGraphError(
                "accepted graph root does not bind its recorded strict authority"
            )
        expected_terminal = paper_obligation_terminal_verification_sha256(
            index,
            semantic,
            final_holistic_audit_surface_sha256=payload[
                "final_holistic_audit_surface_sha256"
            ],
            source_assurance_sha256=payload["source_assurance_sha256"],
        )
    else:
        strict_authority = None
        expected_terminal = paper_obligation_terminal_verification_sha256(
            index, semantic
        )
    if payload["terminal_verification_sha256"] != expected_terminal:
        raise AcceptedObligationGraphError(
            "accepted graph root has a stale terminal-verification identity"
        )
    authorities = {str(value).strip().lower() for value in authenticated_authority_sha256s}
    if current_contract:
        assert strict_authority is not None
        if strict_authority.engine_tree_sha256 not in authorities:
            raise AcceptedObligationGraphError(
                "accepted graph strict authority uses an unregistered engine"
            )
    elif payload["terminal_authority_sha256"] not in authorities:
        raise AcceptedObligationGraphError(
            "accepted graph root was not issued by an authenticated terminal verifier"
        )
    return AcceptedObligationGraphCredential(
        accepted_graph=accepted_graph,
        semantic_graph=semantic,
        paper_index=index,
        closure_leaf=closure,
    )
