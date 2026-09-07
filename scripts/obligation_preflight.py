#!/usr/bin/env python3
"""Cheap complete structural preflight for a paper obligation surface.

This pass runs before Lean or semantic-review producers. It enumerates every
source item through the shared typed route model, validates the route/atom/
correspondence shapes needed downstream, and reports all structural errors in
one result. It does not decide source-to-Lean truth and cannot close a paper.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, Mapping

try:
    from scripts.obligation_routes import (
        EvidenceRoute,
        EvidenceRouteSet,
        DEFINITIONAL_CONTRACT_SOURCE_KINDS,
        ObligationRouteError,
        PROOF_CONTRACT_SOURCE_KINDS,
        RouteKind,
        SemanticReviewTargetKind,
        SOURCE_SEMANTIC_DECLARATION_KINDS,
        source_item_primary_anchor_sha256s,
    )
    from scripts.portable_evidence_identity import portable_evidence_sha256
    from scripts.source_claim_atom_schema import (
        EXACT_CLAUSE_IDENTITY_SCHEMA,
        IDENTITY_SCHEMA_FIELD,
        SOURCE_QUOTE_SHA256_FIELD,
        SUPPORTED_IDENTITY_SCHEMAS,
        VERBATIM_CLAUSE_FIELD,
        identity_schema as source_atom_identity_schema,
        obligation_source_component_sha256,
    )
    from scripts.obligation_resolution import (
        ObligationResolutionError,
        semantic_prerequisite_coordinates,
    )
    from scripts.source_core_projection import validation_errors as source_core_errors
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from obligation_routes import (
        EvidenceRoute,
        EvidenceRouteSet,
        DEFINITIONAL_CONTRACT_SOURCE_KINDS,
        ObligationRouteError,
        PROOF_CONTRACT_SOURCE_KINDS,
        RouteKind,
        SemanticReviewTargetKind,
        SOURCE_SEMANTIC_DECLARATION_KINDS,
        source_item_primary_anchor_sha256s,
    )
    from portable_evidence_identity import portable_evidence_sha256
    from source_claim_atom_schema import (
        EXACT_CLAUSE_IDENTITY_SCHEMA,
        IDENTITY_SCHEMA_FIELD,
        SOURCE_QUOTE_SHA256_FIELD,
        SUPPORTED_IDENTITY_SCHEMAS,
        VERBATIM_CLAUSE_FIELD,
        identity_schema as source_atom_identity_schema,
        obligation_source_component_sha256,
    )
    from obligation_resolution import (
        ObligationResolutionError,
        semantic_prerequisite_coordinates,
    )
    from source_core_projection import validation_errors as source_core_errors


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
REQUIRED_MAP_SCHEMAS = {
    "schema": 1,
    "semantic_contract_schema": 1,
}
CORRESPONDENCE_DIGEST_FIELDS = (
    "source_atoms_sha256",
    "spec_closure_sha256",
    "spec_surface_sha256",
    "closure_environment_sha256",
    "item_identity_sha256",
)

class ObligationPreflightError(ValueError):
    """The complete cheap paper-surface preflight did not pass."""


@dataclass(frozen=True)
class ObligationStructuralPreflight:
    paper: str
    route_set: EvidenceRouteSet | None
    source_artifact_sha256: str
    source_inventory_sha256: str
    route_schema_sha256: str
    structural_preflight_sha256: str
    source_spec_correspondence_required: bool
    errors: tuple[str, ...]
    counts: Mapping[str, int]
    route_obligation_counts: Mapping[str, Mapping[str, int]]
    route_source_quote_sha256s: Mapping[str, tuple[str, ...]]
    prerequisite_source_item_by_declaration: Mapping[str, str]

    @property
    def current(self) -> bool:
        return not self.errors and self.route_set is not None

    def require_current(self) -> "ObligationStructuralPreflight":
        if not self.current:
            raise ObligationPreflightError(
                "structural preflight failed: " + "; ".join(self.errors)
            )
        return self

    def projection(self) -> dict[str, Any]:
        return {
            "schema": 1,
            "acceptance_credential": False,
            "paper": self.paper,
            "current": self.current,
            "source_artifact_sha256": self.source_artifact_sha256,
            "source_inventory_sha256": self.source_inventory_sha256,
            "route_schema_sha256": self.route_schema_sha256,
            "structural_preflight_sha256": self.structural_preflight_sha256,
            "source_spec_correspondence_required": (
                self.source_spec_correspondence_required
            ),
            "errors": list(self.errors),
            "counts": dict(self.counts),
            "route_obligation_counts": {
                source_item_id: dict(role_counts)
                for source_item_id, role_counts in sorted(
                    self.route_obligation_counts.items()
                )
            },
            "route_source_quote_sha256s": {
                source_item_id: list(quote_sha256s)
                for source_item_id, quote_sha256s in sorted(
                    self.route_source_quote_sha256s.items()
                )
            },
            "prerequisite_source_item_by_declaration": dict(
                sorted(self.prerequisite_source_item_by_declaration.items())
            ),
        }


def _digest(value: object) -> str:
    return portable_evidence_sha256(value)


def _source_claim_atom_shape(
    item_id: str,
    raw: Mapping[str, Any],
    *,
    required: bool,
) -> tuple[list[str], tuple[str, ...]]:
    """Validate and project the exact quote identities of any source atoms.

    Source atoms are the canonical semantic decomposition whenever they are
    present, regardless of whether the route realizes a paper result, exposes
    a source definition/premise, or records proof support.  Keeping this rule
    route-independent makes the cheap preflight and final receipt projection
    agree by construction.
    """

    errors: list[str] = []
    atoms = raw.get("source_claim_atoms")
    if not isinstance(atoms, list) or not atoms:
        if required:
            errors.append(f"{item_id}: semantic route has no source_claim_atoms")
        return errors, ()
    quote_digests: list[str] = []
    source_component_digests: list[str] = []
    identity_schemas: set[int] = set()
    for index, atom in enumerate(atoms):
        if not isinstance(atom, Mapping):
            errors.append(f"{item_id}: source_claim_atoms[{index}] is not an object")
            continue
        required = {
            "id",
            "reviewed_lean_route",
            "semantic_claim",
            "source_locator",
            "source_quote_sha256",
        }
        allowed = required | {IDENTITY_SCHEMA_FIELD, VERBATIM_CLAUSE_FIELD}
        if not required.issubset(atom) or not set(atom).issubset(allowed):
            errors.append(
                f"{item_id}: source_claim_atoms[{index}] fields are malformed"
            )
        atom_schema = source_atom_identity_schema(atom)
        if atom_schema is None:
            errors.append(
                f"{item_id}: source_claim_atoms[{index}].{IDENTITY_SCHEMA_FIELD} "
                "is unsupported; expected one of "
                + ", ".join(
                    str(value) for value in sorted(SUPPORTED_IDENTITY_SCHEMAS)
                )
            )
        else:
            identity_schemas.add(atom_schema)
        quote = str(atom.get(SOURCE_QUOTE_SHA256_FIELD) or "").strip().lower()
        if not SHA256_RE.fullmatch(quote):
            errors.append(
                f"{item_id}: source_claim_atoms[{index}] has no exact quote digest"
            )
        else:
            quote_digests.append(quote)
        verbatim_clause = atom.get(VERBATIM_CLAUSE_FIELD)
        if atom_schema == EXACT_CLAUSE_IDENTITY_SCHEMA:
            if not isinstance(verbatim_clause, str) or not verbatim_clause.strip():
                errors.append(
                    f"{item_id}: source_claim_atoms[{index}].{VERBATIM_CLAUSE_FIELD} "
                    "is required for exact-clause atom identity"
                )
        elif verbatim_clause is not None:
            errors.append(
                f"{item_id}: source_claim_atoms[{index}].{VERBATIM_CLAUSE_FIELD} "
                f"requires {IDENTITY_SCHEMA_FIELD} {EXACT_CLAUSE_IDENTITY_SCHEMA}"
            )
        component_digest = obligation_source_component_sha256(atom)
        if component_digest:
            source_component_digests.append(component_digest)
        for field in ("id", "reviewed_lean_route", "semantic_claim", "source_locator"):
            if not isinstance(atom.get(field), str) or not str(atom[field]).strip():
                errors.append(
                    f"{item_id}: source_claim_atoms[{index}].{field} is empty"
                )
    if len(identity_schemas) > 1:
        errors.append(
            f"{item_id}: source_claim_atoms in one source item must use one "
            "identity schema"
        )
    if len(set(source_component_digests)) != len(source_component_digests):
        errors.append(
            f"{item_id}: source_claim_atoms contain duplicate exact source components"
        )
    return errors, tuple(sorted(quote_digests))


def _semantic_item_shape_errors(
    item_id: str,
    raw: Mapping[str, Any],
    *,
    require_source_spec_correspondence: bool,
) -> list[str]:
    errors, _quote_digests = _source_claim_atom_shape(
        item_id, raw, required=True
    )
    atoms = raw.get("source_claim_atoms")
    if not isinstance(atoms, list):
        atoms = []

    correspondence = raw.get("source_spec_correspondence")
    if correspondence is None and not require_source_spec_correspondence:
        return errors
    if not isinstance(correspondence, Mapping):
        errors.append(f"{item_id}: semantic route has no source_spec_correspondence")
        return errors
    required_correspondence = {
        "schema",
        *CORRESPONDENCE_DIGEST_FIELDS,
        "source_atom_bindings",
        "closure_node_dispositions",
    }
    if set(correspondence) != required_correspondence:
        errors.append(f"{item_id}: source_spec_correspondence fields are malformed")
    if correspondence.get("schema") != 1:
        errors.append(f"{item_id}: source_spec_correspondence schema is unsupported")
    for field in CORRESPONDENCE_DIGEST_FIELDS:
        if not SHA256_RE.fullmatch(
            str(correspondence.get(field) or "").strip().lower()
        ):
            errors.append(f"{item_id}: source_spec_correspondence.{field} is invalid")
    bindings = correspondence.get("source_atom_bindings")
    if not isinstance(bindings, list) or len(bindings) != len(atoms):
        errors.append(
            f"{item_id}: source_spec_correspondence atom bindings are incomplete"
        )
    dispositions = correspondence.get("closure_node_dispositions")
    if not isinstance(dispositions, list):
        errors.append(
            f"{item_id}: source_spec_correspondence closure dispositions are malformed"
        )
    return errors


def structural_obligation_preflight(
    source_map: object,
    *,
    paper: str,
    paper_prerequisites: object | None = None,
    library_semantic_review: object | None = None,
    require_theorem_endpoints: bool = False,
    require_source_spec_correspondence: bool = True,
    require_prerequisite_ledger_bindings: bool = True,
) -> ObligationStructuralPreflight:
    """Collect every cheap paper-surface error without invoking a producer.

    ``require_theorem_endpoints`` retains its historical API name but now
    selects role-typed admission for newly issued evidence. Source results use
    one proposition-shaped Spec and a distinct proof/refutation endpoint.
    Source definitions and source premises instead expose their one full Lean
    semantic declaration directly; neither acquires a theorem-shaped endpoint.
    Historical credentials remain directly verifiable under their recorded
    contract. ``require_source_spec_correspondence=False`` is reserved for the
    upstream raw-screening phase: it permits an absent correspondence record,
    but still rejects a malformed partial record and leaves final closure on
    the strict default that requires the issued correspondence.
    ``require_prerequisite_ledger_bindings=False`` is reserved for the still
    earlier Lean-graph preparation pass: source-semantic routes must already be
    well formed, but their paper/library classification and reviewer-ledger
    binding cannot exist until Lean has produced the graph. The strict default
    still requires every such route to bind an accepted prerequisite row.
    """

    errors: list[str] = []
    routes: list[EvidenceRoute] = []
    route_obligation_counts: dict[str, Mapping[str, int]] = {}
    route_source_quote_sha256s: dict[str, tuple[str, ...]] = {}
    prerequisite_source_item_by_declaration: dict[str, str] = {}
    if not isinstance(source_map, Mapping):
        errors.append("paper statement map is not an object")
        items: Mapping[str, Any] = {}
    else:
        items_raw = source_map.get("items")
        items = items_raw if isinstance(items_raw, Mapping) else {}
        if not isinstance(items_raw, Mapping):
            errors.append("paper statement map has no item ledger")
        if source_map.get("paper") != paper:
            errors.append("paper statement map belongs to another paper")
        for field, expected in REQUIRED_MAP_SCHEMAS.items():
            if source_map.get(field) != expected:
                errors.append(f"paper statement map {field} must equal {expected}")
        # A paper folder/root module and the namespace holding its source-facing
        # declarations need not share a spelling.  In particular, a library
        # namespace reorganization can retain the same paper root and exact
        # typed routes under a new qualified namespace.  The typed route and
        # Lean-owned graph validate declaration ownership; this navigation
        # field cannot safely impose a folder-name heuristic here.
        for optional_schema in (
            "source_claim_atoms_schema",
            "source_spec_correspondence_schema",
        ):
            if source_map.get(optional_schema) not in {None, 1}:
                errors.append(
                    f"paper statement map {optional_schema} is unsupported"
                )
        if source_map.get("semantic_route_schema") not in {None, 2}:
            errors.append("paper statement map semantic_route_schema is unsupported")
        if not SHA256_RE.fullmatch(
            str(source_map.get("source_artifact_sha256") or "").strip().lower()
        ):
            errors.append("source_artifact_sha256 is invalid")

    for item_id in sorted(items, key=str):
        raw = items[item_id]
        try:
            route = EvidenceRoute.from_source_item(
                str(item_id), raw
            )
        except ObligationRouteError as exc:
            errors.append(str(exc))
            continue
        routes.append(route)
        if not route.anchor_sha256s:
            errors.append(f"{item_id}: source route has no byte-pinned anchor")
        if route.route_kind is RouteKind.PENDING_SOURCE_ROUTE:
            errors.append(f"{item_id}: claim-bearing source item has no typed route")
        role_typed_admission = (
            isinstance(source_map, Mapping)
            and source_map.get("semantic_route_schema") == 2
        )
        if route.route_kind in {
            RouteKind.RESULT_SEMANTIC,
        }:
            if not isinstance(raw, Mapping):
                errors.append(f"{item_id}: semantic source item is malformed")
            else:
                errors.extend(
                    f"{item_id}: {error}" for error in source_core_errors(raw)
                )
                errors.extend(
                    _semantic_item_shape_errors(
                        str(item_id),
                        raw,
                        require_source_spec_correspondence=(
                            require_source_spec_correspondence
                        ),
                    )
                )
                atoms = raw.get("source_claim_atoms")
                if isinstance(atoms, list):
                    for atom_index, atom in enumerate(atoms):
                        if not isinstance(atom, Mapping):
                            continue
                        atom_endpoint = str(
                            atom.get("reviewed_lean_route") or ""
                        ).strip()
                        if atom_endpoint != route.evidence_declaration:
                            errors.append(
                                f"{item_id}: source_claim_atoms[{atom_index}] must "
                                "route to the typed proof endpoint "
                                f"{route.evidence_declaration}"
                            )
            if (
                require_theorem_endpoints
                and role_typed_admission
                and route.route_kind in {
                RouteKind.RESULT_SEMANTIC,
                }
            ):
                if route.source_kind not in (
                    PROOF_CONTRACT_SOURCE_KINDS - {"definition", "algorithm"}
                ):
                    errors.append(
                        f"{item_id}: a proposition-shaped proof contract is reserved "
                        "for a source assertion; route definitions, algorithms, "
                        "models, and premises to their full Lean semantic declaration. "
                        "Split a mixed presentation into a declaration item and its "
                        "separate asserted result; a reflexive Spec is not a "
                        "substitute for reviewing the definition"
                    )
                if route.evidence_mode == "definitionally_realizes" and (
                    route.source_kind not in DEFINITIONAL_CONTRACT_SOURCE_KINDS
                ):
                    errors.append(
                        f"{item_id}: fresh semantic contract may use "
                        "definitionally-realizes only for an explicitly selected "
                        "source definition or formula"
                    )
                elif route.evidence_mode not in {
                    "proves",
                    "refutes",
                    "definitionally_realizes",
                }:
                    errors.append(
                        f"{item_id}: fresh source-result contract must use a theorem "
                        "endpoint in `proves`, `refutes`, or an explicitly selected "
                        "definitionally-realizes mode"
                    )
                if (
                    route.semantic_review_target_kind
                    is not SemanticReviewTargetKind.SPEC_PROPOSITION
                ):
                    errors.append(
                        f"{item_id}: fresh semantic review target must be the paired "
                        "transparent `...Spec : Prop`, not a definition declaration"
                    )
                if route.spec_declaration == route.evidence_declaration:
                    errors.append(
                        f"{item_id}: fresh semantic contract requires distinct "
                        "Spec and theorem endpoint declarations"
                    )
            elif (
                require_theorem_endpoints
                and not role_typed_admission
                and route.route_kind in {
                    RouteKind.RESULT_SEMANTIC,
                }
            ):
                if route.evidence_mode == "definitionally_realizes" and (
                    route.source_kind not in DEFINITIONAL_CONTRACT_SOURCE_KINDS
                ):
                    errors.append(
                        f"{item_id}: fresh semantic contract may use "
                        "definitionally-realizes only for an explicitly selected "
                        "source definition or formula"
                    )
                elif route.evidence_mode not in {
                    "proves",
                    "refutes",
                    "definitionally_realizes",
                }:
                    errors.append(
                        f"{item_id}: fresh semantic contract must use a theorem "
                        "endpoint in `proves`, `refutes`, or an explicitly selected "
                        "definitionally-realizes mode"
                    )
                if (
                    route.semantic_review_target_kind
                    is not SemanticReviewTargetKind.SPEC_PROPOSITION
                ):
                    errors.append(
                        f"{item_id}: fresh semantic review target must be the paired "
                        "transparent `...Spec : Prop`, not a definition declaration"
                    )
                if route.spec_declaration == route.evidence_declaration:
                    errors.append(
                        f"{item_id}: fresh semantic contract requires distinct "
                        "Spec and theorem endpoint declarations"
                    )
        if route.route_kind is RouteKind.SOURCE_SCOPE_DISPOSITION and isinstance(
            raw, Mapping
        ):
            if not (
                str(raw.get("scope_disposition") or "").strip()
                or str(raw.get("source_scope_classification") or "").strip()
            ):
                errors.append(f"{item_id}: source-scope route has no typed disposition")
        try:
            source_quote_sha256s = source_item_primary_anchor_sha256s(raw)
        except ObligationRouteError as exc:
            errors.append(f"{item_id}: {exc}")
            source_quote_sha256s = ()
        if isinstance(raw, Mapping):
            atoms = raw.get("source_claim_atoms")
            if route.route_kind not in {
                RouteKind.RESULT_SEMANTIC,
            } and atoms is not None:
                atom_errors, atom_quote_sha256s = _source_claim_atom_shape(
                    str(item_id), raw, required=False
                )
                errors.extend(atom_errors)
            else:
                atom_quote_sha256s = tuple(
                    sorted(
                        str(atom.get("source_quote_sha256") or "")
                        .strip()
                        .lower()
                        for atom in atoms
                        if isinstance(atom, Mapping)
                        and SHA256_RE.fullmatch(
                            str(atom.get("source_quote_sha256") or "")
                            .strip()
                            .lower()
                        )
                    )
                ) if isinstance(atoms, list) else ()
            if atom_quote_sha256s:
                source_quote_sha256s = atom_quote_sha256s
        required_roles = {"source_atom": len(source_quote_sha256s)}
        if route.route_kind in {
            RouteKind.RESULT_SEMANTIC,
        }:
            required_roles.update(
                {
                    "semantic_review": 1,
                    "spec": 1,
                    "proof_endpoint": 1,
                    "source_lean_judgment": 1,
                    "proof_realization": 1,
                }
            )
        route_obligation_counts[route.source_item_id] = MappingProxyType(
            required_roles
        )
        route_source_quote_sha256s[route.source_item_id] = tuple(
            sorted(source_quote_sha256s)
        )

    by_id = {route.source_item_id: route for route in routes}
    for route in routes:
        if route.source_component_of and route.source_component_of not in by_id:
            errors.append(
                f"{route.source_item_id}: source_component_of names a missing parent"
            )

    if require_prerequisite_ledger_bindings and (
        (paper_prerequisites is None) != (library_semantic_review is None)
    ):
        errors.append(
            "paper and library semantic-prerequisite ledgers must be supplied together"
        )
    elif (
        require_prerequisite_ledger_bindings
        and paper_prerequisites is not None
        and library_semantic_review is not None
    ):
        try:
            prerequisite_coordinates = semantic_prerequisite_coordinates(
                paper_prerequisites=paper_prerequisites,
                library_semantic_review=library_semantic_review,
            )
        except ObligationResolutionError as exc:
            errors.append(str(exc))
            prerequisite_coordinates = {}
        for declaration, coordinate in sorted(prerequisite_coordinates.items()):
            source_item_id = coordinate.source_item_id
            if source_item_id not in by_id:
                errors.append(
                    f"{declaration}: semantic prerequisite names missing source item {source_item_id}"
                )
                continue
            if not route_source_quote_sha256s.get(source_item_id):
                errors.append(
                    f"{declaration}: semantic prerequisite source item has no exact quote"
                )
                continue
            prerequisite_source_item_by_declaration[declaration] = source_item_id

    if (
        isinstance(source_map, Mapping)
        and source_map.get("semantic_route_schema") == 2
    ):
        prerequisite_source_items = set(
            prerequisite_source_item_by_declaration.values()
        )
        for route in routes:
            if route.route_kind is RouteKind.SOURCE_ASSUMPTION:
                errors.append(
                    f"{route.source_item_id}: role-typed admission requires "
                    "inventory_role `source_semantic_declaration`; the historical "
                    "source-premise route is not a fresh semantic declaration"
                )
                continue
            if route.route_kind is not RouteKind.SOURCE_SEMANTIC_DECLARATION:
                continue
            declared_semantic_roots = route.semantic_declarations
            if route.source_kind not in SOURCE_SEMANTIC_DECLARATION_KINDS:
                errors.append(
                    f"{route.source_item_id}: source semantic-prerequisite route is "
                    "incompatible with source_kind "
                    f"`{route.source_kind or 'missing'}`"
                )
            if not declared_semantic_roots:
                errors.append(
                    f"{route.source_item_id}: source semantic declaration route "
                    "needs a nonempty lean_declarations list"
                )
            if require_prerequisite_ledger_bindings:
                if paper_prerequisites is None or library_semantic_review is None:
                    errors.append(
                        f"{route.source_item_id}: role-typed source semantic declaration "
                        "requires the paper/library semantic-prerequisite ledgers"
                    )
                elif route.source_item_id not in prerequisite_source_items:
                    errors.append(
                        f"{route.source_item_id}: source definition or premise is not bound "
                        "to any actual Lean semantic prerequisite"
                    )
                else:
                    for declaration in declared_semantic_roots:
                        if (
                            prerequisite_source_item_by_declaration.get(declaration)
                            != route.source_item_id
                        ):
                            errors.append(
                                f"{route.source_item_id}: declared semantic root "
                                f"{declaration} is not bound to this source item in the "
                                "paper/library prerequisite ledger"
                            )

    for coordinate, label in (
        (lambda route: route.spec_declaration, "Spec declaration"),
        (lambda route: route.evidence_declaration, "proof endpoint"),
        (lambda route: route.semantic_review_declaration, "review target"),
    ):
        seen: dict[str, str] = {}
        for route in routes:
            if route.route_kind not in {
                RouteKind.RESULT_SEMANTIC,
            }:
                continue
            value = coordinate(route)
            previous = seen.get(value)
            if previous is not None:
                errors.append(
                    f"{route.source_item_id}: duplicate {label} also used by {previous}"
                )
            else:
                seen[value] = route.source_item_id

    route_set = (
        EvidenceRouteSet(routes=tuple(routes), sha256=_digest([r.projection() for r in routes]))
        if not errors
        else None
    )
    counts = {
        kind.value: sum(route.route_kind is kind for route in routes)
        for kind in RouteKind
    }
    counts["total"] = len(routes)
    counts["semantic_prerequisite"] = len(
        prerequisite_source_item_by_declaration
    )
    stable_top = {
        field: source_map.get(field) if isinstance(source_map, Mapping) else None
        for field in (
            "schema",
            "paper",
            "source_artifact_sha256",
            "semantic_contract_schema",
            "semantic_route_schema",
        )
    }
    # Optional redundant format markers normalize to the same structural
    # meaning as their explicit current value. Their omission cannot force
    # semantic replay when every item carries the required exact structure.
    stable_top.update(
        {
            "source_claim_atoms_schema": 1,
            "source_spec_correspondence_schema": 1,
            "paper_interface_namespace": paper,
        }
    )
    route_projection = [route.projection() for route in routes]
    source_inventory_sha = _digest(
        {
            "schema": 1,
            "source_inventory": stable_top,
            "routes": route_projection,
        }
    )
    route_schema_sha = _digest(
        {
            "schema": 1,
            "route_schema": REQUIRED_MAP_SCHEMAS,
            "route_projection": route_projection,
        }
    )
    unique_errors = tuple(dict.fromkeys(errors))
    source_artifact_sha256 = (
        str(source_map.get("source_artifact_sha256") or "").strip().lower()
        if isinstance(source_map, Mapping)
        else ""
    )
    # The prerequisite declaration-to-item map is an issuance-time worksheet
    # cross-check, not part of structural source-surface identity.  The issued
    # graph/index carries every exact source-atom and Lean judgment binding.
    # Excluding ledger-derived counts and declaration navigation lets terminal
    # verification reproduce this identity without reopening editable ledgers.
    structural_counts = {
        key: value for key, value in counts.items() if key != "semantic_prerequisite"
    }
    preflight_sha = _digest(
        {
            "schema": 1,
            "source_spec_correspondence_required": (
                require_source_spec_correspondence
            ),
            "source_inventory_sha256": source_inventory_sha,
            "route_schema_sha256": route_schema_sha,
            "errors": list(unique_errors),
            "counts": structural_counts,
            "route_obligation_counts": {
                source_item_id: dict(role_counts)
                for source_item_id, role_counts in sorted(
                    route_obligation_counts.items()
                )
            },
            "route_source_quote_sha256s": {
                source_item_id: list(quote_sha256s)
                for source_item_id, quote_sha256s in sorted(
                    route_source_quote_sha256s.items()
                )
            },
        }
    )
    return ObligationStructuralPreflight(
        paper=paper,
        route_set=route_set,
        source_artifact_sha256=source_artifact_sha256,
        source_inventory_sha256=source_inventory_sha,
        route_schema_sha256=route_schema_sha,
        structural_preflight_sha256=preflight_sha,
        source_spec_correspondence_required=(
            require_source_spec_correspondence
        ),
        errors=unique_errors,
        counts=MappingProxyType(counts),
        route_obligation_counts=MappingProxyType(route_obligation_counts),
        route_source_quote_sha256s=MappingProxyType(
            route_source_quote_sha256s
        ),
        prerequisite_source_item_by_declaration=MappingProxyType(
            prerequisite_source_item_by_declaration
        ),
    )
