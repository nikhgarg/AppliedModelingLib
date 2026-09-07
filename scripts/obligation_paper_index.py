#!/usr/bin/env python3
"""Complete paper-obligation indexes over immutable evidence graphs.

An arbitrary subgraph must never be mistaken for a complete paper closeout.
This index binds the graph to the cheap source-inventory/route-schema preflight
that enumerated the whole formalized paper surface and partitions every leaf by
obligation family. Partial migration indexes are useful for resumability but
are structurally barred from terminal verification.
"""

from __future__ import annotations

import re
from collections.abc import Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any

try:
    from scripts.obligation_evidence_contracts import (
        LEGACY_ARTIFACT_BOUND_SOURCE_ATOM_CONTRACT,
        REGISTERED_OBLIGATION_CONTRACT_SHA256S,
        SOURCE_ATOM_CONTRACT,
        lean_declaration_contract_for_payload_fields,
    )
    from scripts.obligation_evidence_graph import (
        ObligationEvidenceGraph,
        ObligationEvidenceLeaf,
        ObligationKind,
        build_obligation_graph,
        validate_obligation_graph,
    )
    from scripts.obligation_preflight import ObligationStructuralPreflight
    from scripts.portable_evidence_identity import portable_evidence_sha256
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from obligation_evidence_contracts import (
        LEGACY_ARTIFACT_BOUND_SOURCE_ATOM_CONTRACT,
        REGISTERED_OBLIGATION_CONTRACT_SHA256S,
        SOURCE_ATOM_CONTRACT,
        lean_declaration_contract_for_payload_fields,
    )
    from obligation_evidence_graph import (
        ObligationEvidenceGraph,
        ObligationEvidenceLeaf,
        ObligationKind,
        build_obligation_graph,
        validate_obligation_graph,
    )
    from obligation_preflight import ObligationStructuralPreflight
    from portable_evidence_identity import portable_evidence_sha256


LEGACY_PAPER_OBLIGATION_INDEX_SCHEMA = 1
PAPER_OBLIGATION_INDEX_SCHEMA = 2
PAPER_OBLIGATION_INDEX_IDENTITY_SCOPE = "semantic_leaf_bindings"
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
REQUIRED_COMPLETE_KINDS = frozenset(
    kind for kind in ObligationKind if kind is not ObligationKind.PAPER_CLOSURE
)
ROUTE_ROLE_KINDS = MappingProxyType(
    {
        "source_atom": ObligationKind.SOURCE_ATOM,
        "semantic_review": ObligationKind.LEAN_DECLARATION,
        "spec": ObligationKind.LEAN_DECLARATION,
        "proof_endpoint": ObligationKind.LEAN_DECLARATION,
        "source_lean_judgment": ObligationKind.SOURCE_LEAN_JUDGMENT,
        "proof_realization": ObligationKind.PROOF_REALIZATION,
    }
)
PREREQUISITE_ROLE_KINDS = MappingProxyType(
    {
        "source_atom": ObligationKind.SOURCE_ATOM,
        "lean_declaration": ObligationKind.LEAN_DECLARATION,
        "source_lean_judgment": ObligationKind.SOURCE_LEAN_JUDGMENT,
    }
)


class PaperObligationIndexError(ValueError):
    """A paper index is malformed, incomplete, or disagrees with its graph."""


def _sha256(value: object, field: str) -> str:
    text = str(value or "").strip().lower()
    if not SHA256_RE.fullmatch(text):
        raise PaperObligationIndexError(f"{field} is not SHA-256")
    return text


def _kind_partition(value: object) -> Mapping[ObligationKind, tuple[str, ...]]:
    if not isinstance(value, Mapping):
        raise PaperObligationIndexError("leaf kind partition is not an object")
    result: dict[ObligationKind, tuple[str, ...]] = {}
    for raw_kind, raw_digests in value.items():
        try:
            kind = ObligationKind(str(raw_kind))
        except ValueError as exc:
            raise PaperObligationIndexError(
                "leaf kind partition names an unsupported family"
            ) from exc
        if not isinstance(raw_digests, list):
            raise PaperObligationIndexError("leaf kind partition values must be lists")
        digests = tuple(sorted(_sha256(item, "partition leaf") for item in raw_digests))
        if len(set(digests)) != len(digests):
            raise PaperObligationIndexError("leaf kind partition has duplicates")
        result[kind] = digests
    return MappingProxyType(result)


def _route_leaf_bindings(
    value: object,
) -> Mapping[str, Mapping[str, tuple[str, ...]]]:
    if not isinstance(value, Mapping):
        raise PaperObligationIndexError("route leaf bindings are not an object")
    result: dict[str, Mapping[str, tuple[str, ...]]] = {}
    for raw_source_item_id, raw_roles in value.items():
        source_item_id = str(raw_source_item_id).strip()
        if not source_item_id or not isinstance(raw_roles, Mapping):
            raise PaperObligationIndexError("route leaf binding is malformed")
        roles: dict[str, tuple[str, ...]] = {}
        for raw_role, raw_digests in raw_roles.items():
            role = str(raw_role).strip()
            if role not in ROUTE_ROLE_KINDS or not isinstance(raw_digests, list):
                raise PaperObligationIndexError(
                    "route leaf binding names an unsupported role"
                )
            digests = tuple(sorted(_sha256(item, "route leaf") for item in raw_digests))
            if not digests or len(set(digests)) != len(digests):
                raise PaperObligationIndexError(
                    "route leaf binding is empty or duplicates a leaf"
                )
            roles[role] = digests
        result[source_item_id] = MappingProxyType(roles)
    return MappingProxyType(result)


def _prerequisite_leaf_bindings(
    value: object,
) -> Mapping[str, Mapping[str, tuple[str, ...]]]:
    if not isinstance(value, Mapping):
        raise PaperObligationIndexError(
            "semantic-prerequisite leaf bindings are not an object"
        )
    result: dict[str, Mapping[str, tuple[str, ...]]] = {}
    for raw_declaration, raw_roles in value.items():
        declaration = str(raw_declaration).strip()
        if not declaration or not isinstance(raw_roles, Mapping):
            raise PaperObligationIndexError(
                "semantic-prerequisite leaf binding is malformed"
            )
        roles: dict[str, tuple[str, ...]] = {}
        for raw_role, raw_digests in raw_roles.items():
            role = str(raw_role).strip()
            if role not in PREREQUISITE_ROLE_KINDS or not isinstance(raw_digests, list):
                raise PaperObligationIndexError(
                    "semantic-prerequisite binding names an unsupported role"
                )
            digests = tuple(
                sorted(
                    _sha256(item, "semantic-prerequisite leaf") for item in raw_digests
                )
            )
            if not digests or len(set(digests)) != len(digests):
                raise PaperObligationIndexError(
                    "semantic-prerequisite binding is empty or duplicates a leaf"
                )
            roles[role] = digests
        result[declaration] = MappingProxyType(roles)
    return MappingProxyType(result)


@dataclass(frozen=True)
class PaperObligationIndex:
    schema: int
    complete_paper_surface: bool
    source_inventory_sha256: str
    route_schema_sha256: str
    structural_preflight_sha256: str
    graph_sha256: str
    leaf_sha256s_by_kind: Mapping[ObligationKind, tuple[str, ...]]
    route_leaf_sha256s_by_source_item: Mapping[str, Mapping[str, tuple[str, ...]]]
    prerequisite_leaf_sha256s_by_declaration: Mapping[
        str, Mapping[str, tuple[str, ...]]
    ]
    index_sha256: str

    def projection(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "acceptance_credential": False,
            **(
                {"identity_scope": PAPER_OBLIGATION_INDEX_IDENTITY_SCOPE}
                if self.schema == PAPER_OBLIGATION_INDEX_SCHEMA
                else {}
            ),
            "complete_paper_surface": self.complete_paper_surface,
            "source_inventory_sha256": self.source_inventory_sha256,
            "route_schema_sha256": self.route_schema_sha256,
            "structural_preflight_sha256": self.structural_preflight_sha256,
            "graph_sha256": self.graph_sha256,
            "leaf_sha256s_by_kind": {
                kind.value: list(digests)
                for kind, digests in sorted(
                    self.leaf_sha256s_by_kind.items(), key=lambda item: item[0].value
                )
            },
            "route_leaf_sha256s_by_source_item": {
                source_item_id: {
                    role: list(digests)
                    for role, digests in sorted(role_bindings.items())
                }
                for source_item_id, role_bindings in sorted(
                    self.route_leaf_sha256s_by_source_item.items()
                )
            },
            "prerequisite_leaf_sha256s_by_declaration": {
                declaration: {
                    role: list(digests)
                    for role, digests in sorted(role_bindings.items())
                }
                for declaration, role_bindings in sorted(
                    self.prerequisite_leaf_sha256s_by_declaration.items()
                )
            },
            "index_sha256": self.index_sha256,
        }


def prerequisite_source_judgments_by_source_item(
    index: PaperObligationIndex,
    preflight: ObligationStructuralPreflight,
    *,
    authenticated_source_items_by_declaration: Mapping[str, str] | None = None,
) -> Mapping[str, tuple[str, ...]]:
    """Route prerequisite judgments through graph-owned exact source atoms.

    The issuance-time preflight may additionally name one source-item owner for
    each declaration.  That editable navigation map is checked when present,
    but an accepted graph does not need to retain its predecessor worksheet:
    every prerequisite judgment already depends on exact source-atom leaves,
    and the complete paper index binds those same leaves to source routes.

    Two source items may intentionally expose the same semantic source atoms.
    An issuance-authenticated row can retain the more specific accepted owner;
    otherwise the judgment is conservatively attached to both routes. Terminal
    source-byte validation still requires each route's full reviewed bundle to
    agree, so shared atoms cannot hide different surrounding source semantics.
    """

    preflight.require_current()
    prerequisites = index.prerequisite_leaf_sha256s_by_declaration
    owners = preflight.prerequisite_source_item_by_declaration
    authenticated_owners = (
        {}
        if authenticated_source_items_by_declaration is None
        else authenticated_source_items_by_declaration
    )
    routes = index.route_leaf_sha256s_by_source_item
    if owners and set(prerequisites) != set(owners):
        raise PaperObligationIndexError(
            "semantic prerequisites differ from typed source-item ownership"
        )
    if not isinstance(authenticated_owners, Mapping) or any(
        not isinstance(declaration, str)
        or not declaration
        or declaration != declaration.strip()
        or not isinstance(source_item_id, str)
        or not source_item_id
        or source_item_id != source_item_id.strip()
        for declaration, source_item_id in authenticated_owners.items()
    ):
        raise PaperObligationIndexError(
            "authenticated prerequisite source-item ownership is malformed"
        )
    if not set(authenticated_owners).issubset(prerequisites):
        raise PaperObligationIndexError(
            "authenticated prerequisite source-item ownership names an unknown "
            "declaration"
        )
    if owners and any(
        owners[declaration] != source_item_id
        for declaration, source_item_id in authenticated_owners.items()
    ):
        raise PaperObligationIndexError(
            "authenticated prerequisite source-item ownership conflicts with "
            "typed ownership"
        )
    grouped: dict[str, list[str]] = {}
    for declaration, roles in prerequisites.items():
        if not isinstance(roles, Mapping):
            raise PaperObligationIndexError(
                f"semantic prerequisite {declaration} has no typed source route"
            )
        source_atoms = tuple(roles.get("source_atom", ()))
        candidates = tuple(
            source_item_id
            for source_item_id, source_roles in sorted(routes.items())
            if isinstance(source_roles, Mapping)
            and tuple(source_roles.get("source_atom", ())) == source_atoms
        )
        if not candidates:
            raise PaperObligationIndexError(
                f"semantic prerequisite {declaration} has no graph-owned source route"
            )
        owner = authenticated_owners.get(declaration)
        if owner is None and owners:
            owner = owners[declaration]
        if owner is not None:
            if owner not in candidates:
                raise PaperObligationIndexError(
                    f"semantic prerequisite {declaration} binds a different source route"
                )
            candidates = (owner,)
        judgments = tuple(roles.get("source_lean_judgment", ()))
        if len(judgments) != 1:
            raise PaperObligationIndexError(
                f"semantic prerequisite {declaration} has no unique source judgment"
            )
        for source_item_id in candidates:
            grouped.setdefault(source_item_id, []).append(str(judgments[0]))
    return MappingProxyType(
        {
            source_item_id: tuple(sorted(judgments))
            for source_item_id, judgments in sorted(grouped.items())
        }
    )


def _material(
    *,
    schema: int,
    complete_paper_surface: bool,
    source_inventory_sha256: str,
    route_schema_sha256: str,
    structural_preflight_sha256: str,
    graph_sha256: str,
    leaf_sha256s_by_kind: Mapping[ObligationKind, tuple[str, ...]],
    route_leaf_sha256s_by_source_item: Mapping[str, Mapping[str, tuple[str, ...]]],
    prerequisite_leaf_sha256s_by_declaration: Mapping[
        str, Mapping[str, tuple[str, ...]]
    ],
) -> dict[str, Any]:
    return {
        "schema": schema,
        "acceptance_credential": False,
        **(
            {"identity_scope": PAPER_OBLIGATION_INDEX_IDENTITY_SCOPE}
            if schema == PAPER_OBLIGATION_INDEX_SCHEMA
            else {}
        ),
        "complete_paper_surface": complete_paper_surface,
        "source_inventory_sha256": _sha256(source_inventory_sha256, "source inventory"),
        "route_schema_sha256": _sha256(route_schema_sha256, "route schema"),
        "structural_preflight_sha256": _sha256(
            structural_preflight_sha256, "structural preflight"
        ),
        "graph_sha256": _sha256(graph_sha256, "obligation graph"),
        "leaf_sha256s_by_kind": {
            kind.value: list(digests)
            for kind, digests in sorted(
                leaf_sha256s_by_kind.items(), key=lambda item: item[0].value
            )
        },
        "route_leaf_sha256s_by_source_item": {
            source_item_id: {
                role: list(digests) for role, digests in sorted(role_bindings.items())
            }
            for source_item_id, role_bindings in sorted(
                route_leaf_sha256s_by_source_item.items()
            )
        },
        "prerequisite_leaf_sha256s_by_declaration": {
            declaration: {
                role: list(digests) for role, digests in sorted(role_bindings.items())
            }
            for declaration, role_bindings in sorted(
                prerequisite_leaf_sha256s_by_declaration.items()
            )
        },
    }


def _semantic_binding_rows(
    bindings: Mapping[str, Mapping[str, tuple[str, ...]]],
) -> list[dict[str, list[str]]]:
    """Project a navigation map to its duplicate-preserving semantic rows."""

    rows = [
        {
            role: list(digests)
            for role, digests in sorted(role_bindings.items())
        }
        for role_bindings in bindings.values()
    ]
    return sorted(
        rows,
        key=lambda row: portable_evidence_sha256(row),
    )


def _identity_material(
    material: Mapping[str, Any],
    *,
    route_bindings: Mapping[str, Mapping[str, tuple[str, ...]]],
    prerequisite_bindings: Mapping[str, Mapping[str, tuple[str, ...]]],
) -> dict[str, Any]:
    """Return the schema-owned identity, excluding editable navigation."""

    if material["schema"] == LEGACY_PAPER_OBLIGATION_INDEX_SCHEMA:
        return dict(material)
    return {
        "schema": PAPER_OBLIGATION_INDEX_SCHEMA,
        "acceptance_credential": False,
        "identity_scope": PAPER_OBLIGATION_INDEX_IDENTITY_SCOPE,
        "complete_paper_surface": material["complete_paper_surface"],
        "graph_sha256": material["graph_sha256"],
        "leaf_sha256s_by_kind": material["leaf_sha256s_by_kind"],
        "route_leaf_binding_rows": _semantic_binding_rows(route_bindings),
        "prerequisite_leaf_binding_rows": _semantic_binding_rows(
            prerequisite_bindings
        ),
    }


def _validate_route_bindings(
    graph: ObligationEvidenceGraph,
    bindings: Mapping[str, Mapping[str, tuple[str, ...]]],
    *,
    expected_counts: Mapping[str, Mapping[str, int]] | None,
    expected_source_quotes: Mapping[str, tuple[str, ...]] | None,
    expected_source_artifact_sha256: str | None,
) -> None:
    for source_item_id, role_bindings in bindings.items():
        for role, digests in role_bindings.items():
            expected_kind = ROUTE_ROLE_KINDS[role]
            for digest in digests:
                try:
                    leaf = graph.leaves[digest]
                except KeyError as exc:
                    raise PaperObligationIndexError(
                        f"route {source_item_id} names a leaf outside the graph"
                    ) from exc
                if leaf.kind is not expected_kind:
                    raise PaperObligationIndexError(
                        f"route {source_item_id} role {role} names the wrong leaf kind"
                    )
        if "source_lean_judgment" in role_bindings:
            judgment = graph.leaves[role_bindings["source_lean_judgment"][0]]
            expected_dependencies = set(role_bindings.get("source_atom", ())) | set(
                role_bindings.get("semantic_review", ())
            )
            if (
                len(role_bindings["source_lean_judgment"]) != 1
                or set(judgment.depends_on) != expected_dependencies
            ):
                raise PaperObligationIndexError(
                    f"route {source_item_id} source judgment binds different source/Lean leaves"
                )
        if "proof_realization" in role_bindings:
            realization = graph.leaves[role_bindings["proof_realization"][0]]
            expected_dependencies = set(role_bindings.get("spec", ())) | set(
                role_bindings.get("proof_endpoint", ())
            )
            if (
                len(role_bindings["proof_realization"]) != 1
                or set(realization.depends_on) != expected_dependencies
            ):
                raise PaperObligationIndexError(
                    f"route {source_item_id} realization binds different Spec/endpoint leaves"
                )
    if expected_counts is None:
        return
    if set(bindings) != set(expected_counts):
        missing = sorted(set(expected_counts) - set(bindings))
        extra = sorted(set(bindings) - set(expected_counts))
        raise PaperObligationIndexError(
            "route leaf bindings disagree with the preflight source inventory"
            + (f"; missing: {', '.join(missing)}" if missing else "")
            + (f"; unexpected: {', '.join(extra)}" if extra else "")
        )
    for source_item_id, role_counts in expected_counts.items():
        actual = bindings[source_item_id]
        if set(actual) != set(role_counts) or any(
            len(actual[role]) != count for role, count in role_counts.items()
        ):
            raise PaperObligationIndexError(
                f"route {source_item_id} leaf roles disagree with structural preflight"
            )
        if expected_source_quotes is None:
            raise PaperObligationIndexError(
                "complete route binding validation has no source-quote inventory"
            )
        actual_quotes = tuple(
            sorted(
                str(graph.leaves[digest].semantic_payload["source_quote_sha256"])
                for digest in actual["source_atom"]
            )
        )
        if actual_quotes != tuple(expected_source_quotes[source_item_id]):
            raise PaperObligationIndexError(
                f"route {source_item_id} binds different exact source quotes"
            )
        if expected_source_artifact_sha256 is None:
            raise PaperObligationIndexError(
                "complete route binding validation has no source-artifact identity"
            )
        # Historical source atoms repeated the whole source-corpus digest in
        # every leaf.  Current atoms leave that corpus identity in the
        # preflight/index, which already binds it once for the complete route
        # surface.  When a historical atom is loaded, retain its stricter exact
        # equality check rather than silently normalizing it.
        for digest in actual["source_atom"]:
            recorded_artifact = graph.leaves[digest].semantic_payload.get(
                "source_artifact_sha256"
            )
            if (
                recorded_artifact is not None
                and recorded_artifact != expected_source_artifact_sha256
            ):
                raise PaperObligationIndexError(
                    f"route {source_item_id} binds a different source artifact"
                )
    bound_source_atoms = {
        digest
        for role_bindings in bindings.values()
        for digest in role_bindings.get("source_atom", ())
    }
    graph_source_atoms = {
        digest
        for digest, leaf in graph.leaves.items()
        if leaf.kind is ObligationKind.SOURCE_ATOM
    }
    if bound_source_atoms != graph_source_atoms:
        raise PaperObligationIndexError(
            "complete route bindings do not cover the graph source-atom surface"
        )
    bound_realizations = {
        digest
        for role_bindings in bindings.values()
        for digest in role_bindings.get("proof_realization", ())
    }
    graph_realizations = {
        digest
        for digest, leaf in graph.leaves.items()
        if leaf.kind is ObligationKind.PROOF_REALIZATION
    }
    if bound_realizations != graph_realizations:
        raise PaperObligationIndexError(
            "complete route bindings do not cover the graph realization surface"
        )


def _validate_prerequisite_bindings(
    graph: ObligationEvidenceGraph,
    bindings: Mapping[str, Mapping[str, tuple[str, ...]]],
    *,
    route_bindings: Mapping[str, Mapping[str, tuple[str, ...]]],
    expected_source_item_by_declaration: Mapping[str, str] | None,
    require_complete_surface: bool,
) -> None:
    required_roles = set(PREREQUISITE_ROLE_KINDS)
    for declaration, roles in bindings.items():
        if set(roles) != required_roles or any(
            len(values) != 1 for role, values in roles.items() if role != "source_atom"
        ):
            raise PaperObligationIndexError(
                f"semantic prerequisite {declaration} has incomplete leaf roles"
            )
        for role, digests in roles.items():
            expected_kind = PREREQUISITE_ROLE_KINDS[role]
            for digest in digests:
                try:
                    leaf = graph.leaves[digest]
                except KeyError as exc:
                    raise PaperObligationIndexError(
                        f"semantic prerequisite {declaration} names a leaf outside the graph"
                    ) from exc
                if leaf.kind is not expected_kind:
                    raise PaperObligationIndexError(
                        f"semantic prerequisite {declaration} role {role} names the wrong leaf kind"
                    )
        lean_digest = roles["lean_declaration"][0]
        lean_leaf = graph.leaves[lean_digest]
        if (
            lean_leaf.semantic_payload.get("semantic_target_kind")
            != "semantic_prerequisite"
        ):
            raise PaperObligationIndexError(
                f"semantic prerequisite {declaration} does not bind a prerequisite Lean leaf"
            )
        judgment = graph.leaves[roles["source_lean_judgment"][0]]
        if set(judgment.depends_on) != set(roles["source_atom"]) | {lean_digest}:
            raise PaperObligationIndexError(
                f"semantic prerequisite {declaration} judgment binds different source/Lean leaves"
            )
        if not any(
            tuple(source_roles.get("source_atom", ()))
            == tuple(roles["source_atom"])
            for source_roles in route_bindings.values()
        ):
            raise PaperObligationIndexError(
                f"semantic prerequisite {declaration} has no graph-owned source route"
            )
    if expected_source_item_by_declaration is not None:
        if set(bindings) != set(expected_source_item_by_declaration):
            missing = sorted(set(expected_source_item_by_declaration) - set(bindings))
            extra = sorted(set(bindings) - set(expected_source_item_by_declaration))
            raise PaperObligationIndexError(
                "semantic-prerequisite bindings disagree with preflight"
                + (f"; missing: {', '.join(missing)}" if missing else "")
                + (f"; unexpected: {', '.join(extra)}" if extra else "")
            )
        for declaration, source_item_id in expected_source_item_by_declaration.items():
            try:
                expected_source_atoms = route_bindings[source_item_id]["source_atom"]
            except KeyError as exc:
                raise PaperObligationIndexError(
                    f"semantic prerequisite {declaration} has no source-route atoms"
                ) from exc
            if bindings[declaration]["source_atom"] != expected_source_atoms:
                raise PaperObligationIndexError(
                    f"semantic prerequisite {declaration} binds different source atoms"
                )
    if not require_complete_surface:
        return
    bound_prerequisite_lean = {
        roles["lean_declaration"][0] for roles in bindings.values()
    }
    graph_prerequisite_lean = {
        digest
        for digest, leaf in graph.leaves.items()
        if leaf.kind is ObligationKind.LEAN_DECLARATION
        and leaf.semantic_payload.get("semantic_target_kind") == "semantic_prerequisite"
    }
    if bound_prerequisite_lean != graph_prerequisite_lean:
        raise PaperObligationIndexError(
            "semantic-prerequisite bindings do not cover the graph prerequisite surface"
        )
    bound_judgments = {
        digest
        for roles in route_bindings.values()
        for digest in roles.get("source_lean_judgment", ())
    } | {roles["source_lean_judgment"][0] for roles in bindings.values()}
    graph_judgments = {
        digest
        for digest, leaf in graph.leaves.items()
        if leaf.kind is ObligationKind.SOURCE_LEAN_JUDGMENT
    }
    if bound_judgments != graph_judgments:
        raise PaperObligationIndexError(
            "route and semantic-prerequisite bindings do not cover all source judgments"
        )


def _source_quote_tuple(
    graph: ObligationEvidenceGraph,
    source_atom_sha256s: tuple[str, ...],
) -> tuple[str, ...]:
    return tuple(
        sorted(
            str(graph.leaves[digest].semantic_payload["source_quote_sha256"])
            for digest in source_atom_sha256s
        )
    )


def _semantic_route_descriptor(
    graph: ObligationEvidenceGraph,
    roles: Mapping[str, tuple[str, ...]],
) -> tuple[tuple[str, ...], tuple[tuple[str, int], ...]]:
    return (
        _source_quote_tuple(graph, tuple(roles.get("source_atom", ()))),
        tuple(sorted((role, len(digests)) for role, digests in roles.items())),
    )


def _validate_navigation_free_current_surface(
    graph: ObligationEvidenceGraph,
    route_bindings: Mapping[str, Mapping[str, tuple[str, ...]]],
    prerequisite_bindings: Mapping[str, Mapping[str, tuple[str, ...]]],
    preflight: ObligationStructuralPreflight,
) -> None:
    """Match current navigation to recorded semantics without names or keys.

    Exact source-item identifiers and declaration spellings are checked when a
    new index is issued.  Later verification instead compares duplicate-
    preserving semantic descriptors: exact source quotes, obligation roles,
    and graph leaf coverage.  Final holistic verification independently binds
    the current source-to-Spec and prerequisite semantic identities.
    """

    recorded_routes = sorted(
        _semantic_route_descriptor(graph, roles)
        for roles in route_bindings.values()
    )
    current_routes = sorted(
        (
            tuple(preflight.route_source_quote_sha256s[source_item_id]),
            tuple(sorted(role_counts.items())),
        )
        for source_item_id, role_counts in preflight.route_obligation_counts.items()
    )
    if recorded_routes != current_routes:
        raise PaperObligationIndexError(
            "recorded semantic route bindings disagree with the current source surface"
        )

    # Fresh issuance has already required a complete one-to-one join between
    # the current prerequisite ledgers and the Lean-owned denominator.  After
    # issuance, ``_validate_prerequisite_bindings`` above proves that every
    # immutable prerequisite judgment uses exactly the source atoms of a
    # graph-owned route.  The route comparison in this function then binds
    # those recorded routes to the current semantic source surface.
    #
    # Do not compare against
    # ``preflight.prerequisite_source_item_by_declaration`` here.  A terminal
    # navigation-free preflight intentionally does not read the editable
    # issuance ledgers, so that map is empty by construction.  Treating it as
    # an authoritative empty denominator would reject every nonempty accepted
    # prerequisite graph while adding no semantic check.
    current_route_sources = {
        tuple(preflight.route_source_quote_sha256s[source_item_id])
        for source_item_id in preflight.route_obligation_counts
    }
    for roles in prerequisite_bindings.values():
        recorded_source = _source_quote_tuple(
            graph, tuple(roles.get("source_atom", ()))
        )
        if recorded_source not in current_route_sources:
            raise PaperObligationIndexError(
                "recorded prerequisite binding has no current semantic source route"
            )


def current_reviewed_source_item_ids(
    index: PaperObligationIndex,
    graph: ObligationEvidenceGraph,
    preflight: ObligationStructuralPreflight,
    *,
    source_map: Mapping[str, Any],
) -> frozenset[str]:
    """Resolve authenticated reviewed routes to current navigation labels.

    Selection remains graph-owned: direct judgments and exact prerequisite
    source-atom joins choose recorded routes. The existing pure atom projector
    resolves current routes without navigation labels or quote-only ambiguity.
    Both descriptor comparisons preserve multiplicity; drift fails closed.
    """

    preflight.require_current()
    if not index.complete_paper_surface:
        raise PaperObligationIndexError("reviewed source selection needs a complete index")
    routes = index.route_leaf_sha256s_by_source_item
    prerequisites = index.prerequisite_leaf_sha256s_by_declaration
    _validate_navigation_free_current_surface(graph, routes, prerequisites, preflight)
    from scripts.obligation_evidence_projection import (
        ObligationEvidenceProjectionError,
        _source_atom_leaves,
    )

    items = source_map.get("items")
    if not isinstance(items, Mapping):
        raise PaperObligationIndexError("reviewed source selection has no current items")
    prerequisite_atoms = {
        tuple(roles["source_atom"]) for roles in prerequisites.values()
    }
    recorded_descriptors = []
    reviewed_descriptors = set()
    for roles in routes.values():
        reviewed = bool(roles.get("source_lean_judgment")) or (
            tuple(roles.get("source_atom", ())) in prerequisite_atoms
        )
        descriptor = (
            tuple(roles.get("source_atom", ())),
            tuple(sorted((role, len(digests)) for role, digests in roles.items())),
        )
        recorded_descriptors.append(descriptor)
        if reviewed:
            reviewed_descriptors.add(descriptor)
    current_descriptors = {}
    for source_item_id, counts in preflight.route_obligation_counts.items():
        item = items.get(source_item_id)
        if not isinstance(item, Mapping):
            raise PaperObligationIndexError("current reviewed source item is missing")
        try:
            atoms = _source_atom_leaves(
                item=item, source_artifact_sha256=preflight.source_artifact_sha256,
            )
        except ObligationEvidenceProjectionError as exc:
            raise PaperObligationIndexError(str(exc)) from exc
        current_descriptors[source_item_id] = (
            tuple(sorted(leaf.leaf_sha256 for leaf in atoms)),
            tuple(sorted(counts.items())),
        )
    if sorted(current_descriptors.values()) != sorted(recorded_descriptors):
        raise PaperObligationIndexError(
            "recorded source atoms disagree with the current reviewed source surface"
        )
    return frozenset(
        source_item_id
        for source_item_id, descriptor in current_descriptors.items()
        if descriptor in reviewed_descriptors
    )


def _construct_paper_obligation_index(
    graph: ObligationEvidenceGraph,
    *,
    schema: int,
    source_inventory_sha256: str,
    route_schema_sha256: str,
    structural_preflight_sha256: str,
    complete_paper_surface: bool,
    route_leaf_sha256s_by_source_item: Mapping[str, Mapping[str, tuple[str, ...]]],
    prerequisite_leaf_sha256s_by_declaration: Mapping[
        str, Mapping[str, tuple[str, ...]]
    ],
    expected_route_obligation_counts: Mapping[str, Mapping[str, int]] | None,
    expected_route_source_quotes: Mapping[str, tuple[str, ...]] | None,
    expected_source_artifact_sha256: str | None,
    expected_prerequisite_source_item_by_declaration: Mapping[str, str] | None,
) -> PaperObligationIndex:
    graph = validate_obligation_graph(
        graph.projection(),
        leaves={digest: leaf.projection() for digest, leaf in graph.leaves.items()},
    )
    for digest, leaf in graph.leaves.items():
        registered_contracts = REGISTERED_OBLIGATION_CONTRACT_SHA256S[leaf.kind.value]
        if leaf.contract_sha256 not in registered_contracts:
            raise PaperObligationIndexError(
                f"leaf {digest} uses an unregistered {leaf.kind.value} obligation contract"
            )
        if leaf.kind is ObligationKind.SOURCE_ATOM:
            artifact_bound = "source_artifact_sha256" in leaf.semantic_payload
            expected_source_contract = (
                LEGACY_ARTIFACT_BOUND_SOURCE_ATOM_CONTRACT.contract_sha256
                if artifact_bound
                else SOURCE_ATOM_CONTRACT.contract_sha256
            )
            if leaf.contract_sha256 != expected_source_contract:
                raise PaperObligationIndexError(
                    f"leaf {digest} source-atom payload disagrees with its registered contract"
                )
        if leaf.kind is ObligationKind.LEAN_DECLARATION:
            expected_lean_contract = lean_declaration_contract_for_payload_fields(
                leaf.semantic_payload
            )
            if expected_lean_contract is None:  # The leaf parser should reject first.
                raise PaperObligationIndexError(
                    f"leaf {digest} has an unsupported Lean-declaration payload"
                )
            if leaf.contract_sha256 != expected_lean_contract.contract_sha256:
                raise PaperObligationIndexError(
                    f"leaf {digest} Lean payload disagrees with its registered contract"
                )
    partition: dict[ObligationKind, tuple[str, ...]] = {}
    for kind in ObligationKind:
        members = tuple(
            sorted(digest for digest, leaf in graph.leaves.items() if leaf.kind is kind)
        )
        if members:
            partition[kind] = members
    if complete_paper_surface and set(partition) != REQUIRED_COMPLETE_KINDS:
        missing = sorted(
            kind.value for kind in REQUIRED_COMPLETE_KINDS - set(partition)
        )
        raise PaperObligationIndexError(
            "complete paper index omits obligation families: " + ", ".join(missing)
        )
    _validate_route_bindings(
        graph,
        route_leaf_sha256s_by_source_item,
        expected_counts=expected_route_obligation_counts,
        expected_source_quotes=expected_route_source_quotes,
        expected_source_artifact_sha256=expected_source_artifact_sha256,
    )
    _validate_prerequisite_bindings(
        graph,
        prerequisite_leaf_sha256s_by_declaration,
        route_bindings=route_leaf_sha256s_by_source_item,
        expected_source_item_by_declaration=(
            expected_prerequisite_source_item_by_declaration
        ),
        require_complete_surface=complete_paper_surface,
    )
    material = _material(
        schema=schema,
        complete_paper_surface=bool(complete_paper_surface),
        source_inventory_sha256=source_inventory_sha256,
        route_schema_sha256=route_schema_sha256,
        structural_preflight_sha256=structural_preflight_sha256,
        graph_sha256=graph.graph_sha256,
        leaf_sha256s_by_kind=partition,
        route_leaf_sha256s_by_source_item=route_leaf_sha256s_by_source_item,
        prerequisite_leaf_sha256s_by_declaration=(
            prerequisite_leaf_sha256s_by_declaration
        ),
    )
    return PaperObligationIndex(
        schema=schema,
        complete_paper_surface=material["complete_paper_surface"],
        source_inventory_sha256=material["source_inventory_sha256"],
        route_schema_sha256=material["route_schema_sha256"],
        structural_preflight_sha256=material["structural_preflight_sha256"],
        graph_sha256=material["graph_sha256"],
        leaf_sha256s_by_kind=MappingProxyType(partition),
        route_leaf_sha256s_by_source_item=MappingProxyType(
            {
                source_item_id: MappingProxyType(dict(role_bindings))
                for source_item_id, role_bindings in sorted(
                    route_leaf_sha256s_by_source_item.items()
                )
            }
        ),
        prerequisite_leaf_sha256s_by_declaration=MappingProxyType(
            {
                declaration: MappingProxyType(dict(role_bindings))
                for declaration, role_bindings in sorted(
                    prerequisite_leaf_sha256s_by_declaration.items()
                )
            }
        ),
        index_sha256=portable_evidence_sha256(
            _identity_material(
                material,
                route_bindings=route_leaf_sha256s_by_source_item,
                prerequisite_bindings=prerequisite_leaf_sha256s_by_declaration,
            )
        ),
    )


def build_paper_obligation_index(
    graph: ObligationEvidenceGraph,
    *,
    source_inventory_sha256: str,
    route_schema_sha256: str,
    structural_preflight_sha256: str,
    complete_paper_surface: bool,
    route_leaf_sha256s_by_source_item: Mapping[str, Mapping[str, tuple[str, ...]]]
    | None = None,
    prerequisite_leaf_sha256s_by_declaration: Mapping[
        str, Mapping[str, tuple[str, ...]]
    ]
    | None = None,
) -> PaperObligationIndex:
    """Build a partial migration index; complete indexes require a preflight."""

    if complete_paper_surface:
        raise PaperObligationIndexError(
            "complete paper indexes must be built from a current structural preflight"
        )
    normalized = _route_leaf_bindings(
        {
            source_item_id: {
                role: list(digests) for role, digests in role_bindings.items()
            }
            for source_item_id, role_bindings in (
                route_leaf_sha256s_by_source_item or {}
            ).items()
        }
    )
    normalized_prerequisites = _prerequisite_leaf_bindings(
        {
            declaration: {
                role: list(digests) for role, digests in role_bindings.items()
            }
            for declaration, role_bindings in (
                prerequisite_leaf_sha256s_by_declaration or {}
            ).items()
        }
    )
    return _construct_paper_obligation_index(
        graph,
        schema=PAPER_OBLIGATION_INDEX_SCHEMA,
        source_inventory_sha256=source_inventory_sha256,
        route_schema_sha256=route_schema_sha256,
        structural_preflight_sha256=structural_preflight_sha256,
        complete_paper_surface=False,
        route_leaf_sha256s_by_source_item=normalized,
        prerequisite_leaf_sha256s_by_declaration=normalized_prerequisites,
        expected_route_obligation_counts=None,
        expected_route_source_quotes=None,
        expected_source_artifact_sha256=None,
        expected_prerequisite_source_item_by_declaration=None,
    )


def build_paper_obligation_index_from_preflight(
    graph: ObligationEvidenceGraph,
    preflight: ObligationStructuralPreflight,
    *,
    complete_paper_surface: bool,
    route_leaf_sha256s_by_source_item: Mapping[str, Mapping[str, tuple[str, ...]]]
    | None = None,
    prerequisite_leaf_sha256s_by_declaration: Mapping[
        str, Mapping[str, tuple[str, ...]]
    ]
    | None = None,
) -> PaperObligationIndex:
    """Bind a graph only to a successfully enumerated shared preflight."""

    if not isinstance(preflight, ObligationStructuralPreflight):
        raise PaperObligationIndexError(
            "paper obligation index requires the nominal structural preflight"
        )
    preflight.require_current()
    normalized = _route_leaf_bindings(
        {
            source_item_id: {
                role: list(digests) for role, digests in role_bindings.items()
            }
            for source_item_id, role_bindings in (
                route_leaf_sha256s_by_source_item or {}
            ).items()
        }
    )
    normalized_prerequisites = _prerequisite_leaf_bindings(
        {
            declaration: {
                role: list(digests) for role, digests in role_bindings.items()
            }
            for declaration, role_bindings in (
                prerequisite_leaf_sha256s_by_declaration or {}
            ).items()
        }
    )
    return _construct_paper_obligation_index(
        graph,
        schema=PAPER_OBLIGATION_INDEX_SCHEMA,
        source_inventory_sha256=preflight.source_inventory_sha256,
        route_schema_sha256=preflight.route_schema_sha256,
        structural_preflight_sha256=preflight.structural_preflight_sha256,
        complete_paper_surface=complete_paper_surface,
        route_leaf_sha256s_by_source_item=normalized,
        prerequisite_leaf_sha256s_by_declaration=normalized_prerequisites,
        expected_route_obligation_counts=(
            preflight.route_obligation_counts if complete_paper_surface else None
        ),
        expected_route_source_quotes=(
            preflight.route_source_quote_sha256s if complete_paper_surface else None
        ),
        expected_source_artifact_sha256=(
            preflight.source_artifact_sha256 if complete_paper_surface else None
        ),
        expected_prerequisite_source_item_by_declaration=(
            preflight.prerequisite_source_item_by_declaration
            if complete_paper_surface
            and preflight.prerequisite_source_item_by_declaration
            else None
        ),
    )


def assemble_complete_paper_obligation_graph(
    *,
    leaves: Mapping[str, ObligationEvidenceLeaf | Mapping[str, Any]],
    preflight: ObligationStructuralPreflight,
    source_atom_leaf_sha256s_by_source_item: Mapping[str, tuple[str, ...]],
    semantic_role_leaf_sha256s_by_source_item: Mapping[
        str, Mapping[str, tuple[str, ...]]
    ],
    build_leaf_sha256: str,
    prerequisite_role_leaf_sha256s_by_declaration: Mapping[
        str, Mapping[str, tuple[str, ...]]
    ]
    | None = None,
    additional_root_leaf_sha256s: tuple[str, ...] = (),
) -> tuple[ObligationEvidenceGraph, PaperObligationIndex]:
    """Assemble one route-complete graph without inferring any evidence leaf.

    Producers and migration adapters must supply exact leaf identities. This
    function only joins those typed results to the preflight-owned route
    inventory, chooses terminal roots, and invokes the strict complete-index
    validator.
    """

    if not isinstance(preflight, ObligationStructuralPreflight):
        raise PaperObligationIndexError(
            "complete paper assembly requires the nominal structural preflight"
        )
    preflight.require_current()
    route_ids = set(preflight.route_obligation_counts)
    if set(source_atom_leaf_sha256s_by_source_item) != route_ids:
        raise PaperObligationIndexError(
            "complete paper assembly source routes disagree with preflight"
        )
    unexpected_semantic = sorted(
        set(semantic_role_leaf_sha256s_by_source_item) - route_ids
    )
    if unexpected_semantic:
        raise PaperObligationIndexError(
            "complete paper assembly has semantic roles for unknown routes: "
            + ", ".join(unexpected_semantic)
        )
    bindings: dict[str, Mapping[str, tuple[str, ...]]] = {}
    roots: set[str] = set(additional_root_leaf_sha256s)
    for source_item_id in sorted(route_ids):
        roles: dict[str, tuple[str, ...]] = {
            "source_atom": tuple(
                sorted(source_atom_leaf_sha256s_by_source_item[source_item_id])
            )
        }
        roles.update(
            {
                role: tuple(sorted(digests))
                for role, digests in semantic_role_leaf_sha256s_by_source_item.get(
                    source_item_id, {}
                ).items()
            }
        )
        expected_roles = preflight.route_obligation_counts[source_item_id]
        if set(roles) != set(expected_roles) or any(
            len(roles[role]) != count for role, count in expected_roles.items()
        ):
            raise PaperObligationIndexError(
                f"complete paper assembly route {source_item_id} is incomplete"
            )
        bindings[source_item_id] = MappingProxyType(roles)
        if "source_lean_judgment" in roles:
            roots.update(roles["source_lean_judgment"])
            roots.update(roles["proof_realization"])
        else:
            roots.update(roles["source_atom"])
    prerequisite_bindings = _prerequisite_leaf_bindings(
        {
            declaration: {
                role: list(digests) for role, digests in role_bindings.items()
            }
            for declaration, role_bindings in (
                prerequisite_role_leaf_sha256s_by_declaration or {}
            ).items()
        }
    )
    roots.update(
        roles["source_lean_judgment"][0] for roles in prerequisite_bindings.values()
    )
    build_digest = _sha256(build_leaf_sha256, "build leaf")
    roots.add(build_digest)
    graph = build_obligation_graph(
        leaves.values(),
        root_leaf_sha256s=sorted(roots),
    )
    try:
        build_leaf = graph.leaves[build_digest]
    except KeyError as exc:
        raise PaperObligationIndexError(
            "complete paper assembly is missing its build leaf"
        ) from exc
    if build_leaf.kind is not ObligationKind.BUILD:
        raise PaperObligationIndexError(
            "complete paper assembly build root is not build evidence"
        )
    index = build_paper_obligation_index_from_preflight(
        graph,
        preflight,
        complete_paper_surface=True,
        route_leaf_sha256s_by_source_item=bindings,
        prerequisite_leaf_sha256s_by_declaration=prerequisite_bindings,
    )
    return graph, index


def validate_paper_obligation_index(
    value: object,
    *,
    graph: ObligationEvidenceGraph,
    require_complete: bool,
    preflight: ObligationStructuralPreflight | None = None,
    require_current_aggregate_identity: bool = True,
) -> PaperObligationIndex:
    if not isinstance(value, Mapping):
        raise PaperObligationIndexError("paper obligation index is not an object")
    schema = value.get("schema")
    required = {
        "schema",
        "acceptance_credential",
        "complete_paper_surface",
        "source_inventory_sha256",
        "route_schema_sha256",
        "structural_preflight_sha256",
        "graph_sha256",
        "leaf_sha256s_by_kind",
        "route_leaf_sha256s_by_source_item",
        "prerequisite_leaf_sha256s_by_declaration",
        "index_sha256",
    }
    if schema == PAPER_OBLIGATION_INDEX_SCHEMA:
        required.add("identity_scope")
    if (
        set(value) != required
        or schema
        not in {
            LEGACY_PAPER_OBLIGATION_INDEX_SCHEMA,
            PAPER_OBLIGATION_INDEX_SCHEMA,
        }
        or value.get("acceptance_credential") is not False
        or not isinstance(value.get("complete_paper_surface"), bool)
        or (
            schema == PAPER_OBLIGATION_INDEX_SCHEMA
            and value.get("identity_scope")
            != PAPER_OBLIGATION_INDEX_IDENTITY_SCOPE
        )
    ):
        raise PaperObligationIndexError("paper obligation index fields are malformed")
    if require_complete and value.get("complete_paper_surface") is not True:
        raise PaperObligationIndexError(
            "partial migration graph cannot be terminal paper evidence"
        )
    partition = _kind_partition(value.get("leaf_sha256s_by_kind"))
    route_bindings = _route_leaf_bindings(
        value.get("route_leaf_sha256s_by_source_item")
    )
    prerequisite_bindings = _prerequisite_leaf_bindings(
        value.get("prerequisite_leaf_sha256s_by_declaration")
    )
    if preflight is not None:
        if not isinstance(preflight, ObligationStructuralPreflight):
            raise PaperObligationIndexError(
                "paper obligation index requires the nominal structural preflight"
            )
        preflight.require_current()
    material = _material(
        schema=schema,
        complete_paper_surface=value["complete_paper_surface"],
        source_inventory_sha256=value.get("source_inventory_sha256"),
        route_schema_sha256=value.get("route_schema_sha256"),
        structural_preflight_sha256=value.get("structural_preflight_sha256"),
        graph_sha256=value.get("graph_sha256"),
        leaf_sha256s_by_kind=partition,
        route_leaf_sha256s_by_source_item=route_bindings,
        prerequisite_leaf_sha256s_by_declaration=prerequisite_bindings,
    )
    supplied = _sha256(value.get("index_sha256"), "paper index")
    if supplied != portable_evidence_sha256(
        _identity_material(
            material,
            route_bindings=route_bindings,
            prerequisite_bindings=prerequisite_bindings,
        )
    ):
        raise PaperObligationIndexError("paper obligation index identity is corrupt")
    exact_navigation = require_current_aggregate_identity
    rebuilt = _construct_paper_obligation_index(
        graph,
        schema=schema,
        source_inventory_sha256=material["source_inventory_sha256"],
        route_schema_sha256=material["route_schema_sha256"],
        structural_preflight_sha256=material["structural_preflight_sha256"],
        complete_paper_surface=material["complete_paper_surface"],
        route_leaf_sha256s_by_source_item=route_bindings,
        prerequisite_leaf_sha256s_by_declaration=prerequisite_bindings,
        expected_route_obligation_counts=(
            preflight.route_obligation_counts
            if preflight is not None and exact_navigation
            else None
        ),
        expected_route_source_quotes=(
            preflight.route_source_quote_sha256s
            if preflight is not None and exact_navigation
            else None
        ),
        expected_source_artifact_sha256=(
            preflight.source_artifact_sha256
            if preflight is not None and exact_navigation
            else None
        ),
        expected_prerequisite_source_item_by_declaration=(
            preflight.prerequisite_source_item_by_declaration
            if preflight is not None
            and exact_navigation
            and preflight.prerequisite_source_item_by_declaration
            else None
        ),
    )
    if rebuilt.projection() != dict(value):
        raise PaperObligationIndexError(
            "paper obligation index disagrees with its complete graph partition"
        )
    if require_complete and preflight is not None and not exact_navigation:
        _validate_navigation_free_current_surface(
            graph,
            route_bindings,
            prerequisite_bindings,
            preflight,
        )
    if require_complete and exact_navigation:
        if preflight is None:
            raise PaperObligationIndexError(
                "terminal paper evidence requires the current structural preflight"
            )
        for field in (
            "source_inventory_sha256",
            "route_schema_sha256",
            "structural_preflight_sha256",
        ):
            if getattr(rebuilt, field) != getattr(preflight, field):
                raise PaperObligationIndexError(
                    f"paper obligation index disagrees with current {field}"
                )
    return rebuilt


def paper_obligation_index_aggregate_mismatches(
    index: PaperObligationIndex,
    preflight: ObligationStructuralPreflight,
) -> tuple[str, ...]:
    """Report engine-projected aggregate drift without deciding currentness.

    The three aggregate hashes authenticate the projection serialized when the
    immutable paper index was issued.  They are useful provenance, but an
    engine can change a nonsemantic projection label without changing any
    source atom, reviewed Lean target, proof route, prerequisite, or build
    input.  Acceptance instead validates the current route/source structure
    and the exact Lean import closure; this helper remains diagnostic only.
    """

    if not isinstance(index, PaperObligationIndex) or not isinstance(
        preflight, ObligationStructuralPreflight
    ):
        raise PaperObligationIndexError(
            "aggregate comparison requires a paper index and structural preflight"
        )
    preflight.require_current()
    return tuple(
        field
        for field in (
            "source_inventory_sha256",
            "route_schema_sha256",
            "structural_preflight_sha256",
        )
        if getattr(index, field) != getattr(preflight, field)
    )
