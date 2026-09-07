#!/usr/bin/env python3
"""Project and preflight current source-to-proof realization from a Lean graph.

The current declaration graph already owns the exact semantic target, proof
endpoint, recursive prerequisite closure, and axiom-closure checks used by a
strict closeout.  This module is the single deterministic transport boundary
that turns that authenticated graph into per-source-item realization
identities.  It neither invokes Lean nor performs semantic review.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Iterable, Mapping
from typing import Any

from scripts.lean_review_surface import (
    semantic_review_display_surface_from_inventory,
)
from scripts.obligation_routes import EvidenceRouteSet, ObligationRouteError
from scripts.source_claim_atom_schema import (
    graph_native_source_spec_realization_identity_sha256,
    source_claim_atoms_semantic_sha256,
)

SHA256_RE = re.compile(r"^[0-9a-f]{64}$")

V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE = "lean_owned_v11_claim_graph"
V11_LEAN_REVIEW_GRAPH_CARRIER_SCHEMA = 3


def _stable_sha256(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def _row_index(
    rows: object,
    *,
    key: str,
    label: str,
) -> tuple[dict[str, Mapping[str, Any]], list[str]]:
    if not isinstance(rows, list):
        return {}, [f"Lean graph {label} are malformed"]
    indexed: dict[str, Mapping[str, Any]] = {}
    errors: list[str] = []
    for raw in rows:
        if not isinstance(raw, Mapping):
            errors.append(f"Lean graph {label} contain a malformed row")
            continue
        name = str(raw.get(key) or "").strip()
        if not name or name in indexed:
            errors.append(f"Lean graph {label} contain an ambiguous `{key}`")
            continue
        indexed[name] = raw
    return indexed, errors


def _contract_index(
    rows: object,
) -> tuple[dict[tuple[str, str, str], Mapping[str, Any]], list[str]]:
    if not isinstance(rows, list):
        return {}, ["Lean graph semantic contracts are malformed"]
    indexed: dict[tuple[str, str, str], Mapping[str, Any]] = {}
    errors: list[str] = []
    required = {
        "specification",
        "evidence",
        "mode",
        "matches",
        "evidence_is_unsafe",
        "evidence_value_has_sorry",
        "evidence_axiom_closure_checked",
        "evidence_axiom_closure",
    }
    for raw in rows:
        if not isinstance(raw, Mapping) or set(raw) != required:
            errors.append("Lean graph semantic contracts contain a malformed row")
            continue
        key = (
            str(raw.get("specification") or "").strip(),
            str(raw.get("evidence") or "").strip(),
            str(raw.get("mode") or "").strip(),
        )
        closure = raw.get("evidence_axiom_closure")
        if (
            not all(key)
            or key in indexed
            or raw.get("matches") is not True
            or raw.get("evidence_is_unsafe") is not False
            or raw.get("evidence_value_has_sorry") is not False
            or raw.get("evidence_axiom_closure_checked") is not True
            or not isinstance(closure, list)
            or any(not isinstance(name, str) or not name.strip() for name in closure)
        ):
            errors.append("Lean graph did not authenticate one exact proof route")
            continue
        indexed[key] = raw
    return indexed, errors


def graph_native_realization_receipts_from_inventory(
    *,
    source_map: Mapping[str, Any],
    inventory: Mapping[str, Any],
    context_input_sha256: str,
    expected_paper_declarations: Iterable[str],
    expected_library_declarations: Iterable[str],
) -> tuple[dict[str, dict[str, str]], list[str]]:
    """Return one portable realization receipt for every typed result route.

    All declaration discovery and semantic expansion must already have been
    performed by Lean.  Python validates the serialized graph envelope,
    follows only Lean-emitted prerequisite edges, and hashes the resulting
    exact content projection.
    """

    context_digest = str(context_input_sha256 or "").strip().lower()
    if not SHA256_RE.fullmatch(context_digest):
        return {}, ["Lean graph context identity is invalid"]
    try:
        route_set = EvidenceRouteSet.from_source_map(source_map)
    except (ObligationRouteError, TypeError, ValueError) as exc:
        return {}, ["typed result routes are unavailable: " + str(exc)]
    result_routes = route_set.result_routes()
    expected_specs = tuple(sorted(route.spec_declaration for route in result_routes))
    paper_names = tuple(
        sorted({str(name).strip() for name in expected_paper_declarations if str(name).strip()})
    )
    library_names = tuple(
        sorted({str(name).strip() for name in expected_library_declarations if str(name).strip()})
    )
    try:
        surface = semantic_review_display_surface_from_inventory(
            inventory,
            expected_specifications=expected_specs,
            expected_paper_declarations=paper_names,
            expected_library_declarations=library_names,
        )
    except ValueError as exc:
        return {}, ["Lean graph semantic display surface is invalid: " + str(exc)]

    contracts, errors = _contract_index(inventory.get("semantic_contracts"))
    declarations, declaration_errors = _row_index(
        inventory.get("declarations"),
        key="declaration",
        label="declarations",
    )
    errors.extend(declaration_errors)
    source_items = source_map.get("items")
    if not isinstance(source_items, Mapping):
        errors.append("paper statement map has no item ledger")
        return {}, errors

    receipts: dict[str, dict[str, str]] = {}
    expected_contracts: set[tuple[str, str, str]] = set()
    for route in result_routes:
        item_id = route.source_item_id
        raw_item = source_items.get(item_id)
        if not isinstance(raw_item, Mapping):
            errors.append(f"{item_id}: source item is malformed")
            continue
        raw_contract = raw_item.get("semantic_contract")
        raw_atoms = raw_item.get("source_claim_atoms")
        if not isinstance(raw_contract, Mapping):
            errors.append(f"{item_id}: semantic contract is malformed")
            continue
        key = (
            route.spec_declaration,
            route.evidence_declaration,
            route.evidence_mode,
        )
        expected_contracts.add(key)
        contract_row = contracts.get(key)
        target = surface.specifications.get(route.spec_declaration)
        atoms_sha = source_claim_atoms_semantic_sha256(raw_atoms)
        if contract_row is None:
            errors.append(f"{item_id}: Lean graph omitted the exact proof route")
            continue
        if not isinstance(target, Mapping) or not atoms_sha:
            errors.append(f"{item_id}: Lean graph has no complete semantic target")
            continue

        pending_paper = {
            str(name).strip()
            for name in target.get("prerequisite_declarations", ())
            if str(name).strip()
        }
        pending_library = {
            str(name).strip()
            for name in target.get("library_declarations", ())
            if str(name).strip()
        }
        paper_rows: dict[str, Mapping[str, Any]] = {}
        library_rows: dict[str, Mapping[str, Any]] = {}
        closure_error = ""
        while pending_paper or pending_library:
            if pending_paper:
                name = min(pending_paper)
                pending_paper.remove(name)
                if name in paper_rows:
                    continue
                row = surface.paper_declarations.get(name)
                if not isinstance(row, Mapping):
                    closure_error = f"missing paper prerequisite `{name}`"
                    break
                paper_rows[name] = row
                pending_paper.update(
                    str(value).strip()
                    for value in row.get("direct_paper_declarations", ())
                    if str(value).strip() and str(value).strip() not in paper_rows
                )
                pending_library.update(
                    str(value).strip()
                    for value in row.get("direct_library_declarations", ())
                    if str(value).strip() and str(value).strip() not in library_rows
                )
                continue
            name = min(pending_library)
            pending_library.remove(name)
            if name in library_rows:
                continue
            row = surface.library_declarations.get(name)
            if not isinstance(row, Mapping):
                closure_error = f"missing library prerequisite `{name}`"
                break
            library_rows[name] = row
            pending_library.update(
                str(value).strip()
                for value in row.get("direct_library_declarations", ())
                if str(value).strip() and str(value).strip() not in library_rows
            )
        relevant_names = {
            route.spec_declaration,
            route.evidence_declaration,
            *paper_rows,
            *library_rows,
        }
        missing_nodes = sorted(relevant_names - set(declarations))
        if closure_error or missing_nodes:
            detail = closure_error or "missing declaration node(s): " + ", ".join(missing_nodes[:4])
            errors.append(f"{item_id}: Lean graph semantic closure is incomplete: {detail}")
            continue

        closure_projection = {
            "schema": 1,
            "semantic_target": dict(target),
            "semantic_contract": dict(contract_row),
            "paper_prerequisites": {
                name: dict(row) for name, row in sorted(paper_rows.items())
            },
            "library_prerequisites": {
                name: dict(row) for name, row in sorted(library_rows.items())
            },
            "declaration_nodes": {
                name: dict(declarations[name]) for name in sorted(relevant_names)
            },
        }
        closure_sha = _stable_sha256(closure_projection)
        surface_sha = str(target.get("display_sha256") or "").strip().lower()
        item_identity = graph_native_source_spec_realization_identity_sha256(
            raw_contract,
            source_atoms_sha256=atoms_sha,
            spec_closure_sha256=closure_sha,
            spec_surface_sha256=surface_sha,
            closure_environment_sha256=context_digest,
        )
        if not SHA256_RE.fullmatch(item_identity):
            errors.append(f"{item_id}: graph-native realization identity is unavailable")
            continue
        receipts[item_id] = {
            "authority": "v11_graph_native_v1",
            "source_item_key": item_id,
            "spec_declaration": route.spec_declaration,
            "evidence_declaration": route.evidence_declaration,
            "evidence_mode": route.evidence_mode,
            "semantic_shape": str(raw_contract.get("semantic_shape") or "").strip(),
            "source_atoms_sha256": atoms_sha,
            "item_identity_sha256": item_identity,
            "spec_closure_sha256": closure_sha,
            "spec_surface_sha256": surface_sha,
            "closure_environment_sha256": context_digest,
        }

    extra_contracts = sorted(set(contracts) - expected_contracts)
    if extra_contracts:
        errors.append("Lean graph contains an unrequested semantic proof route")
    if set(receipts) != {route.source_item_id for route in result_routes} and not errors:
        errors.append("Lean graph omitted one or more typed realization rows")
    return receipts, errors


def current_graph_realization_preflight(
    *,
    paper: str,
    source_map: Mapping[str, Any],
    graph_carrier: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Validate the graph-native realization surface used by a current plan.

    This is deliberately a non-accepting scheduling preflight.  It validates
    the complete internally authenticated carrier, derives the prerequisite
    denominator from Lean's typed inventory, and requires one exact realization
    receipt for every typed result route.  A missing or malformed graph is a
    repair obligation; it never falls back to a historical persisted worksheet
    and never offers an identity-rewrite transition.
    """

    def blocked(*errors: str) -> dict[str, Any]:
        return {
            "schema": 3,
            "required": True,
            "state": "blocked",
            "current": False,
            "graph_native_items": [],
            "errors": [str(error) for error in errors if str(error).strip()],
            "acceptance_credential": False,
        }

    if not isinstance(graph_carrier, Mapping):
        return blocked("current v11 realization graph is unavailable")
    required = {
        "schema",
        "acceptance_credential",
        "operational_scheduling_only",
        "paper",
        "source_semantic_lane",
        "context_input_sha256",
        "graph_request",
        "inventory",
        "inventory_sha256",
        "receipt_integrity_sha256",
    }
    material = {
        key: value
        for key, value in graph_carrier.items()
        if key != "receipt_integrity_sha256"
    }
    inventory = graph_carrier.get("inventory")
    if (
        set(graph_carrier) != required
        or graph_carrier.get("schema") != V11_LEAN_REVIEW_GRAPH_CARRIER_SCHEMA
        or graph_carrier.get("acceptance_credential") is not False
        or graph_carrier.get("operational_scheduling_only") is not True
        or str(graph_carrier.get("paper") or "") != paper
        or graph_carrier.get("source_semantic_lane")
        != V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
        or not isinstance(graph_carrier.get("graph_request"), Mapping)
        or not isinstance(inventory, Mapping)
        or graph_carrier.get("inventory_sha256") != _stable_sha256(inventory)
        or graph_carrier.get("receipt_integrity_sha256")
        != _stable_sha256(material)
    ):
        return blocked("current v11 realization graph carrier is malformed")

    try:
        route_set = EvidenceRouteSet.from_source_map(source_map)
    except (ObligationRouteError, TypeError, ValueError) as exc:
        return blocked("typed result routes are unavailable: " + str(exc))
    result_routes = route_set.result_routes()
    expected_specs = tuple(
        sorted({route.spec_declaration for route in result_routes})
    )
    graph_request = graph_carrier.get("graph_request")
    if (
        not isinstance(graph_request, Mapping)
        or graph_request.get("specification_names") != list(expected_specs)
    ):
        return blocked(
            "current v11 realization graph selected a different result surface"
        )
    paper_section = inventory.get("paper_prerequisite_displays")
    library_section = inventory.get("library_prerequisite_displays")

    def section_names(section: object, label: str) -> tuple[str, ...]:
        rows = section.get("items") if isinstance(section, Mapping) else None
        if not isinstance(rows, list):
            raise TypeError(f"Lean graph {label} are malformed")
        names = [
            str(row.get("declaration") or "").strip()
            for row in rows
            if isinstance(row, Mapping)
        ]
        if (
            len(names) != len(rows)
            or any(not name for name in names)
            or names != sorted(set(names))
        ):
            raise ValueError(f"Lean graph {label} are malformed")
        return tuple(names)

    try:
        expected_paper = section_names(paper_section, "paper prerequisites")
        expected_library = section_names(
            library_section, "library prerequisites"
        )
    except (TypeError, ValueError) as exc:
        return blocked(str(exc))

    receipts, errors = graph_native_realization_receipts_from_inventory(
        source_map=source_map,
        inventory=inventory,
        context_input_sha256=str(
            graph_carrier.get("context_input_sha256") or ""
        ),
        expected_paper_declarations=expected_paper,
        expected_library_declarations=expected_library,
    )
    expected_items = {route.source_item_id for route in result_routes}
    if errors or set(receipts) != expected_items:
        return blocked(
            *(
                errors
                or ["current v11 graph omitted one or more typed realization rows"]
            )
        )
    return {
        "schema": 3,
        "required": True,
        "state": "current_graph_authority",
        "current": True,
        "graph_native_items": sorted(expected_items),
        "errors": [],
        "acceptance_credential": False,
    }
