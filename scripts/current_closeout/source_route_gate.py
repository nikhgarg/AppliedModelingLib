#!/usr/bin/env python3
"""Validate current source-route projections against Lean-owned identities.

The typed source ledger owns semantic routes.  Lean owns declaration identity,
kind, and source ownership.  This gate joins those two authorities and checks
that retained navigation fields, source-atom routes, and quarantined defect
evidence cannot point somewhere else.  It performs no Lean parsing, source
discovery, semantic judgment, or historical receipt compatibility.
"""

from __future__ import annotations

from collections.abc import Mapping

from scripts.current_closeout.declarations import (
    LeanDeclaration,
    declaration_index_from_inventory,
    declaration_index_from_source_records,
    declaration_key,
    resolve_declaration_name,
    typed_qualified_declaration_identity,
)
from scripts.obligation_routes import (
    EvidenceRoute,
    EvidenceRouteSet,
    ObligationRouteError,
    RouteKind,
)

_PROOF_KINDS = frozenset({"theorem", "lemma"})
_OBSOLETE_CURRENT_ROUTE_FIELDS = frozenset(
    {
        "semantic_bridge_declarations",
        "definition_equivalence_declarations",
        "source_equivalence_declarations",
    }
)


def _is_current_material_route(route: EvidenceRoute) -> bool:
    """Whether this row is represented by the retained current Lean graph.

    A source map deliberately retains historical navigation and deep-review
    context alongside the selected source-to-Lean obligations.  Those retained
    rows remain subject to source-inventory, byte-anchor, and scope checks, but
    they are not a second declaration-discovery authority.  Current Lean-name
    validation must therefore follow the same typed projection used to acquire
    the graph: result Specs, direct source-semantic declarations, and an
    explicitly quarantined defect witness.
    """

    return route.route_kind in {
        RouteKind.RESULT_SEMANTIC,
        RouteKind.SOURCE_SEMANTIC_DECLARATION,
    } or route.inventory_role == "quarantined_source_defect"


def _string_list(value: object, *, field: str) -> tuple[tuple[str, ...], str]:
    if value is None:
        return (), ""
    if not isinstance(value, list) or any(
        not isinstance(item, str) or not item.strip() for item in value
    ):
        return (), f"{field} must be a list of nonempty strings"
    normalized = tuple(item.strip() for item in value)
    if len(normalized) != len(set(normalized)):
        return normalized, f"{field} contains duplicate declarations"
    return normalized, ""


def _combined_resolution(
    paper_declarations: dict[str, list[LeanDeclaration]],
    library_declarations: dict[str, list[LeanDeclaration]],
    name: str,
) -> list[LeanDeclaration]:
    candidates = [
        *resolve_declaration_name(paper_declarations, name),
        *resolve_declaration_name(library_declarations, name),
    ]
    seen: set[tuple[object, ...]] = set()
    result: list[LeanDeclaration] = []
    for declaration in candidates:
        key = declaration_key(declaration)
        if key in seen:
            continue
        seen.add(key)
        result.append(declaration)
    return result


def _qualified_set(declarations: list[LeanDeclaration]) -> set[str]:
    return {
        qualified
        for declaration in declarations
        for qualified in [typed_qualified_declaration_identity(declaration)]
        if qualified
    }


def _atom_route_errors(
    route: EvidenceRoute,
    raw_item: Mapping[str, object],
) -> list[str]:
    raw_atoms = raw_item.get("source_claim_atoms")
    if not isinstance(raw_atoms, list):
        return []
    allowed = (
        {route.evidence_declaration}
        if route.route_kind is RouteKind.RESULT_SEMANTIC
        else set(route.semantic_declarations)
        if route.route_kind is RouteKind.SOURCE_SEMANTIC_DECLARATION
        else set()
    )
    if not allowed:
        return []
    errors: list[str] = []
    for index, raw_atom in enumerate(raw_atoms):
        if not isinstance(raw_atom, Mapping):
            continue
        selected = str(raw_atom.get("reviewed_lean_route") or "").strip()
        if selected not in allowed:
            errors.append(
                f"{route.source_item_id}.source_claim_atoms[{index}]."
                "reviewed_lean_route does not equal the typed semantic route"
            )
    return errors


def _navigation_route_errors(
    route: EvidenceRoute,
    raw_item: Mapping[str, object],
    *,
    paper_declarations: dict[str, list[LeanDeclaration]],
    library_declarations: dict[str, list[LeanDeclaration]],
) -> list[str]:
    """Validate only navigation that names a current typed route.

    A schema-2 result may retain ``checked_strengthening_declarations`` in
    ``support_lean_declarations``.  They document a separately proved stronger
    fact, but are neither source claims nor semantic-prerequisite roots and
    need not be reachable from the one selected source-to-Spec route.  Lean
    still owns their use when a proof imports them; treating that historical
    support list as a second graph root would both duplicate review work and
    make an unrelated helper rename block the literal source result.
    """

    errors: list[str] = []
    resolved_by_field: dict[str, set[str]] = {}
    fields = ["lean_declarations"]
    if route.route_kind is RouteKind.RESULT_SEMANTIC:
        # A legacy presentation can still give the exact endpoint in a
        # separate proof navigation field.  It remains part of the typed
        # result route, unlike optional support/strengthening history.
        fields.append("proof_lean_declarations")
    for field in fields:
        names, shape_error = _string_list(raw_item.get(field), field=field)
        if shape_error:
            errors.append(f"{route.source_item_id}.{shape_error}")
            continue
        resolved_by_field[field] = set()
        for name in names:
            resolved = _combined_resolution(
                paper_declarations, library_declarations, name
            )
            if len(resolved) != 1:
                errors.append(
                    f"{route.source_item_id}.{field} declaration `{name}` does "
                    "not resolve to one Lean-owned declaration"
                )
                continue
            resolved_by_field[field].update(_qualified_set(resolved))

    if route.route_kind is RouteKind.RESULT_SEMANTIC:
        primary = resolved_by_field.get("lean_declarations", set())
        explicit_proof = resolved_by_field.get("proof_lean_declarations", set())
        if (primary or explicit_proof) and route.evidence_declaration not in (
            primary | explicit_proof
        ):
            errors.append(
                f"{route.source_item_id} navigation declarations omit the typed "
                f"proof endpoint `{route.evidence_declaration}`"
            )
    elif route.route_kind is RouteKind.SOURCE_SEMANTIC_DECLARATION:
        projected = resolved_by_field.get("lean_declarations", set())
        expected = set(route.semantic_declarations)
        if projected != expected:
            errors.append(
                f"{route.source_item_id}.lean_declarations do not equal the typed "
                "source-semantic declarations"
            )
    return errors


def _quarantined_defect_route_errors(
    route: EvidenceRoute,
    *,
    paper_declarations: dict[str, list[LeanDeclaration]],
) -> list[str]:
    if route.inventory_role != "quarantined_source_defect":
        return []
    for name in route.support_declarations:
        resolved = resolve_declaration_name(paper_declarations, name)
        if len(resolved) != 1 or resolved[0].kind not in _PROOF_KINDS:
            continue
        return []
    return [
        (
            f"{route.source_item_id} quarantined source defect lacks one "
            "quarantined Lean theorem/lemma evidence route"
        )
    ]


def current_v11_source_route_errors(
    *,
    paper_id: str,
    status_payload: Mapping[str, object],
    source_map: Mapping[str, object],
    surface: object,
) -> tuple[str, ...]:
    """Return current route/projection errors from one retained Lean graph."""

    try:
        route_set = EvidenceRouteSet.from_source_map(source_map)
    except (ObligationRouteError, TypeError, ValueError) as exc:
        return (f"`{paper_id}` current typed source routes are invalid: {exc}",)
    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        return (f"`{paper_id}` current source-route inputs are malformed",)

    inventory = getattr(surface, "declaration_inventory", None)
    module_sources = getattr(surface, "module_sources", None)
    paper_declarations = (
        declaration_index_from_inventory(inventory, module_sources)
        if isinstance(module_sources, Mapping)
        else {}
    )
    library_declarations = declaration_index_from_source_records(
        getattr(surface, "library_source_declarations", {})
    )
    paper_targets = set(getattr(surface, "paper_semantic_targets", {}))
    library_targets = set(getattr(surface, "library_semantic_targets", {}))
    semantic_targets = paper_targets | library_targets
    errors: list[str] = []

    for route in route_set.routes:
        raw_item = raw_items.get(route.source_item_id)
        if not isinstance(raw_item, Mapping):
            errors.append(f"{route.source_item_id} source route has no item object")
            continue
        if not _is_current_material_route(route):
            # Deep/context rows may preserve older Lean navigation as useful
            # repair history.  They cannot add a current semantic obligation;
            # a material use must instead be promoted to one of the explicit
            # typed routes above, which then enters the Lean-owned graph.
            continue

        obsolete = sorted(_OBSOLETE_CURRENT_ROUTE_FIELDS.intersection(raw_item))
        if obsolete:
            errors.append(
                f"{route.source_item_id} retains obsolete current-route field(s): "
                + ", ".join(obsolete)
            )
        errors.extend(
            _navigation_route_errors(
                route,
                raw_item,
                paper_declarations=paper_declarations,
                library_declarations=library_declarations,
            )
        )
        errors.extend(_atom_route_errors(route, raw_item))
        if route.route_kind is RouteKind.SOURCE_SEMANTIC_DECLARATION:
            for declaration in route.semantic_declarations:
                resolved = _combined_resolution(
                    paper_declarations, library_declarations, declaration
                )
                if (
                    len(resolved) != 1
                    or declaration not in _qualified_set(resolved)
                    or declaration not in semantic_targets
                ):
                    errors.append(
                        f"{route.source_item_id} source-semantic declaration "
                        f"`{declaration}` lacks one Lean-classified semantic target"
                    )
        errors.extend(
            _quarantined_defect_route_errors(
                route,
                paper_declarations=paper_declarations,
            )
        )
    return tuple(errors)
