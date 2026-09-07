#!/usr/bin/env python3
"""Complete persisted-paper bundle over graph, preflight index, and issuances.

The semantic graph does not contain provenance, and an issuance does not prove
the graph is the whole paper. A schema-1 bundle is therefore only an integrity
object: it selects one complete preflight-owned paper index and at least one
issuance for every required leaf. A schema-2 bundle is the sole acceptance
credential only after the terminal verifier has selected exactly one issuance
per leaf under the common terminal graph/index assurance record.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, Iterable, Mapping

try:
    from scripts.obligation_evidence_graph import ObligationEvidenceGraph
    from scripts.obligation_evidence_issuance import (
        ObligationEvidenceIssuance,
        ObligationEvidenceIssuanceError,
        TERMINAL_PAPER_CLOSURE_ASSURANCE_SHA256,
        validate_obligation_evidence_issuance,
    )
    from scripts.obligation_paper_index import (
        PaperObligationIndex,
        PaperObligationIndexError,
        validate_paper_obligation_index,
    )
    from scripts.obligation_preflight import ObligationStructuralPreflight
    from scripts.portable_evidence_identity import portable_evidence_sha256
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from obligation_evidence_graph import ObligationEvidenceGraph
    from obligation_evidence_issuance import (
        ObligationEvidenceIssuance,
        ObligationEvidenceIssuanceError,
        TERMINAL_PAPER_CLOSURE_ASSURANCE_SHA256,
        validate_obligation_evidence_issuance,
    )
    from obligation_paper_index import (
        PaperObligationIndex,
        PaperObligationIndexError,
        validate_paper_obligation_index,
    )
    from obligation_preflight import ObligationStructuralPreflight
    from portable_evidence_identity import portable_evidence_sha256


PAPER_OBLIGATION_BUNDLE_SCHEMA = 1
ACCEPTING_PAPER_OBLIGATION_BUNDLE_SCHEMA = 2
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class PaperObligationBundleError(ValueError):
    """A complete paper bundle is malformed or omits required provenance."""


def _sha256(value: object, field: str) -> str:
    text = str(value or "").strip().lower()
    if not SHA256_RE.fullmatch(text):
        raise PaperObligationBundleError(f"{field} is not SHA-256")
    return text


@dataclass(frozen=True)
class PaperObligationBundle:
    schema: int
    acceptance_credential: bool
    paper_index_sha256: str
    graph_sha256: str
    issuance_sha256s_by_leaf: Mapping[str, tuple[str, ...]]
    terminal_verification_sha256: str | None
    bundle_sha256: str

    def projection(self) -> dict[str, Any]:
        result = {
            "schema": self.schema,
            "acceptance_credential": self.acceptance_credential,
            "complete_paper_surface": True,
            "complete_attestation_set": True,
            "paper_index_sha256": self.paper_index_sha256,
            "graph_sha256": self.graph_sha256,
            "issuance_sha256s_by_leaf": {
                leaf: list(issuances)
                for leaf, issuances in sorted(self.issuance_sha256s_by_leaf.items())
            },
            "bundle_sha256": self.bundle_sha256,
        }
        if self.terminal_verification_sha256 is not None:
            result["terminal_verification_sha256"] = (
                self.terminal_verification_sha256
            )
        return result


def _material(
    *,
    schema: int,
    acceptance_credential: bool,
    paper_index_sha256: str,
    graph_sha256: str,
    issuance_sha256s_by_leaf: Mapping[str, tuple[str, ...]],
    terminal_verification_sha256: str | None,
) -> dict[str, Any]:
    material = {
        "schema": schema,
        "acceptance_credential": acceptance_credential,
        "complete_paper_surface": True,
        "complete_attestation_set": True,
        "paper_index_sha256": _sha256(paper_index_sha256, "paper index"),
        "graph_sha256": _sha256(graph_sha256, "obligation graph"),
        "issuance_sha256s_by_leaf": {
            _sha256(leaf, "issued leaf"): list(issuances)
            for leaf, issuances in sorted(issuance_sha256s_by_leaf.items())
        },
    }
    if terminal_verification_sha256 is not None:
        material["terminal_verification_sha256"] = _sha256(
            terminal_verification_sha256, "terminal verification"
        )
    return material


def paper_obligation_terminal_verification_sha256(
    paper_index: PaperObligationIndex,
    graph: ObligationEvidenceGraph,
    *,
    final_holistic_audit_surface_sha256: str | None = None,
    source_assurance_sha256: str | None = None,
) -> str:
    """Return the stable evidence-record identity for terminal verification."""

    assurance_fields = (
        final_holistic_audit_surface_sha256,
        source_assurance_sha256,
    )
    if any(value is None for value in assurance_fields) and any(
        value is not None for value in assurance_fields
    ):
        raise PaperObligationBundleError(
            "terminal verification requires every semantic assurance identity"
        )
    if final_holistic_audit_surface_sha256 is not None:
        return portable_evidence_sha256(
            {
                "schema": 2,
                "contract": (
                    "complete_current_control_and_holistic_semantic_verification_"
                    "of_one_paper_obligation_graph"
                ),
                "paper_index_sha256": paper_index.index_sha256,
                "graph_sha256": graph.graph_sha256,
                "final_holistic_audit_surface_sha256": _sha256(
                    final_holistic_audit_surface_sha256,
                    "final holistic audit surface",
                ),
                "source_assurance_sha256": _sha256(
                    source_assurance_sha256, "source assurance"
                ),
            }
        )
    return portable_evidence_sha256(
        {
            "schema": 1,
            "contract": (
                "complete_current_control_verification_of_one_paper_obligation_graph"
            ),
            "paper_index_sha256": paper_index.index_sha256,
            "graph_sha256": graph.graph_sha256,
        }
    )


def _construct_paper_obligation_bundle(
    paper_index: PaperObligationIndex,
    graph: ObligationEvidenceGraph,
    issuances: Iterable[ObligationEvidenceIssuance | Mapping[str, Any]],
    *,
    preflight: ObligationStructuralPreflight | None,
    accepting: bool,
) -> PaperObligationBundle:
    try:
        index = validate_paper_obligation_index(
            paper_index.projection(), graph=graph, require_complete=True
            if preflight is not None
            else False,
            preflight=preflight,
        )
    except PaperObligationIndexError as exc:
        raise PaperObligationBundleError(str(exc)) from exc
    grouped: dict[str, set[str]] = {}
    selected_issuances: dict[str, ObligationEvidenceIssuance] = {}
    for raw in issuances:
        try:
            issuance = validate_obligation_evidence_issuance(
                raw.projection() if isinstance(raw, ObligationEvidenceIssuance) else raw
            )
        except ObligationEvidenceIssuanceError as exc:
            raise PaperObligationBundleError(str(exc)) from exc
        if issuance.leaf_sha256 not in graph.leaves:
            raise PaperObligationBundleError(
                "issuance names a leaf outside the complete paper graph"
            )
        grouped.setdefault(issuance.leaf_sha256, set()).add(
            issuance.issuance_sha256
        )
        selected_issuances[issuance.issuance_sha256] = issuance
    missing = sorted(set(graph.leaves) - set(grouped))
    if missing:
        raise PaperObligationBundleError(
            "complete paper bundle has unattested leaves: " + ", ".join(missing)
        )
    normalized = MappingProxyType(
        {leaf: tuple(sorted(values)) for leaf, values in sorted(grouped.items())}
    )
    terminal_verification_sha256 = None
    schema = PAPER_OBLIGATION_BUNDLE_SCHEMA
    if accepting:
        if not index.complete_paper_surface:
            raise PaperObligationBundleError(
                "accepting paper bundle requires a complete paper surface"
            )
        schema = ACCEPTING_PAPER_OBLIGATION_BUNDLE_SCHEMA
        terminal_verification_sha256 = (
            paper_obligation_terminal_verification_sha256(index, graph)
        )
        for leaf_sha256, issuance_ids in normalized.items():
            if len(issuance_ids) != 1:
                raise PaperObligationBundleError(
                    "accepting paper bundle requires one terminal issuance per leaf"
                )
            issuance = selected_issuances[issuance_ids[0]]
            if (
                issuance.assurance_contract_sha256
                != TERMINAL_PAPER_CLOSURE_ASSURANCE_SHA256
                or issuance.evidence_record_sha256
                != terminal_verification_sha256
            ):
                raise PaperObligationBundleError(
                    f"accepting paper bundle leaf {leaf_sha256} lacks its exact terminal verification issuance"
                )
    material = _material(
        schema=schema,
        acceptance_credential=accepting,
        paper_index_sha256=index.index_sha256,
        graph_sha256=graph.graph_sha256,
        issuance_sha256s_by_leaf=normalized,
        terminal_verification_sha256=terminal_verification_sha256,
    )
    return PaperObligationBundle(
        schema=schema,
        acceptance_credential=accepting,
        paper_index_sha256=material["paper_index_sha256"],
        graph_sha256=material["graph_sha256"],
        issuance_sha256s_by_leaf=normalized,
        terminal_verification_sha256=terminal_verification_sha256,
        bundle_sha256=portable_evidence_sha256(material),
    )


def build_paper_obligation_bundle(
    paper_index: PaperObligationIndex,
    graph: ObligationEvidenceGraph,
    issuances: Iterable[ObligationEvidenceIssuance | Mapping[str, Any]],
    *,
    preflight: ObligationStructuralPreflight,
) -> PaperObligationBundle:
    """Build only after current preflight proves complete route coverage."""

    return _construct_paper_obligation_bundle(
        paper_index,
        graph,
        issuances,
        preflight=preflight,
        accepting=False,
    )


def build_accepting_paper_obligation_bundle(
    paper_index: PaperObligationIndex,
    graph: ObligationEvidenceGraph,
    issuances: Iterable[ObligationEvidenceIssuance | Mapping[str, Any]],
    *,
    preflight: ObligationStructuralPreflight,
) -> PaperObligationBundle:
    """Build the sole accepting bundle after terminal current-control review."""

    return _construct_paper_obligation_bundle(
        paper_index,
        graph,
        issuances,
        preflight=preflight,
        accepting=True,
    )


def validate_paper_obligation_bundle(
    value: object,
    *,
    paper_index: PaperObligationIndex,
    graph: ObligationEvidenceGraph,
    issuances: Mapping[str, ObligationEvidenceIssuance | Mapping[str, Any]],
    preflight: ObligationStructuralPreflight | None = None,
) -> PaperObligationBundle:
    if not isinstance(value, Mapping):
        raise PaperObligationBundleError("paper obligation bundle is not an object")
    base_required = {
        "schema",
        "acceptance_credential",
        "complete_paper_surface",
        "complete_attestation_set",
        "paper_index_sha256",
        "graph_sha256",
        "issuance_sha256s_by_leaf",
        "bundle_sha256",
    }
    schema = value.get("schema")
    accepting = schema == ACCEPTING_PAPER_OBLIGATION_BUNDLE_SCHEMA
    required = base_required | ({"terminal_verification_sha256"} if accepting else set())
    if (
        set(value) != required
        or schema not in {
            PAPER_OBLIGATION_BUNDLE_SCHEMA,
            ACCEPTING_PAPER_OBLIGATION_BUNDLE_SCHEMA,
        }
        or value.get("acceptance_credential") is not accepting
        or value.get("complete_paper_surface") is not True
        or value.get("complete_attestation_set") is not True
        or not isinstance(value.get("issuance_sha256s_by_leaf"), Mapping)
    ):
        raise PaperObligationBundleError("paper obligation bundle fields are malformed")
    selected: list[ObligationEvidenceIssuance | Mapping[str, Any]] = []
    normalized_mapping: dict[str, tuple[str, ...]] = {}
    for raw_leaf, raw_ids in value["issuance_sha256s_by_leaf"].items():
        leaf = _sha256(raw_leaf, "issued leaf")
        if not isinstance(raw_ids, list) or not raw_ids:
            raise PaperObligationBundleError("bundle leaf has no issuance list")
        ids = tuple(sorted(_sha256(item, "issuance") for item in raw_ids))
        if len(set(ids)) != len(ids):
            raise PaperObligationBundleError("bundle duplicates an issuance")
        normalized_mapping[leaf] = ids
        for digest in ids:
            try:
                selected.append(issuances[digest])
            except KeyError as exc:
                raise PaperObligationBundleError(
                    f"bundle issuance {digest} is unavailable"
                ) from exc
    rebuilt = _construct_paper_obligation_bundle(
        paper_index,
        graph,
        selected,
        preflight=preflight,
        accepting=accepting,
    )
    if rebuilt.projection() != dict(value):
        raise PaperObligationBundleError(
            "paper obligation bundle disagrees with its graph/index/issuances"
        )
    return rebuilt
