#!/usr/bin/env python3
"""Portable request and carrier contract for the current v11 Lean graph.

This module owns only the identity and schema boundary around the
non-authoritative Lean graph checkpoint. It does not acquire a Lean graph,
select paper claims, issue semantic judgments, or grant closeout acceptance.
The caller must still validate every returned inventory row, proof contract,
dependency, prerequisite, axiom, source range, and semantic display.

Keeping this contract independent of ``audit_evidence_integrity`` lets current
consumers share one carrier definition without importing historical
source-record authorities.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Any, Iterable, Mapping, Protocol

from scripts.current_closeout.realization import (
    V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE,
    V11_LEAN_REVIEW_GRAPH_CARRIER_SCHEMA,
)
from scripts.lean_declaration_graph_producer import (
    lean_declaration_graph_producer_identity,
)
from scripts.obligation_routes import (
    EvidenceRoute,
    EvidenceRouteSet,
    ObligationRouteError,
    SemanticReviewTargetKind,
)


V11_LEAN_REVIEW_GRAPH_REQUEST_SCHEMA = 5
V11_LEAN_REVIEW_GRAPH_CHECKPOINT_SCHEMA = 1
V11_LEAN_REVIEW_GRAPH_CHECKPOINT_RELATIVE = (
    Path(".lake") / "closeout-objects" / "v11-graph-checkpoints"
)
V11_TERMINAL_GRAPH_CHECKPOINT_SCHEMA = 1
V11_TERMINAL_GRAPH_CHECKPOINT_RELATIVE = (
    Path(".lake") / "closeout-objects" / "v11-terminal-graph-checkpoints"
)
V11_TERMINAL_GRAPH_EVIDENCE_LANE = "v11-terminal-semantic-recovery"
V11_LEAN_DECLARATION_GRAPH_TIMEOUT_SECONDS = 900


class EvidenceSnapshotView(Protocol):
    """Exact input fields needed by the graph-carrier identity."""

    path: Path
    sha256: str | None
    raw_bytes: bytes | None


class V11GraphContextView(Protocol):
    """Minimal immutable transaction surface consumed by this contract."""

    folder: Path
    source_semantic_lane: str
    statement_map: Mapping[str, Any] | None
    v11_lean_review_graph_payload: Mapping[str, Any] | None

    def canonical_sidecar_path(self, basename: str) -> Path: ...

    def json_snapshot(self, path: Path) -> EvidenceSnapshotView | None: ...


class V11GraphAcquisitionContextView(V11GraphContextView, Protocol):
    """Builder-issued frozen inputs required for current graph acquisition."""

    issued_by_builder: bool

    def json_payload(self, path: Path) -> Mapping[str, Any] | None: ...

    def file_bytes_override(self) -> Mapping[Path, bytes | None]: ...


class RetainedV11ReviewSurfaceView(Protocol):
    """Runtime-only result retained by one exact evidence transaction."""

    graph_request: Mapping[str, Any]
    declaration_inventory: Mapping[str, Any]
    build_input_provider: object
    semantic_targets: Mapping[str, Mapping[str, Any]]
    paper_semantic_targets: Mapping[str, Mapping[str, Any]]
    library_semantic_targets: Mapping[str, Mapping[str, Any]]
    library_declaration_sources: Mapping[str, Mapping[str, Any]]


class RetainedV11GraphContextView(V11GraphContextView, Protocol):
    """Exact builder-issued context capable of returning its one graph."""

    issued_by_builder: bool

    def retained_v11_review_surface(
        self,
    ) -> RetainedV11ReviewSurfaceView | None: ...


class V11LeanReviewGraphCarrierMismatch(ValueError):
    """A non-authoritative saved graph cannot serve the current typed request."""


def _configured_assumption_root_names(
    context: V11GraphAcquisitionContextView,
    *,
    entry_module: str,
) -> frozenset[str]:
    """Return exact Lean assumption declarations configured by status roots.

    Assumptions are architecture-level support declarations and may not occur
    in a selected proof term.  They therefore need explicit Lean roots for
    the primary gate to verify their exact declarations and source file.  The
    status snapshot is already a frozen input to this context; its names are
    included in the graph request below so a carrier cannot hide a change.

    Status navigation historically permits short paper-local names, while the
    Lean graph inventory accepts only fully qualified constants.  Resolve a
    short name against the namespace of the already frozen entry module.  A
    name that is already qualified remains exact rather than being rewritten.
    """

    status_payload = getattr(context, "status_payload", None)
    if not isinstance(status_payload, Mapping):
        return frozenset()
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, Mapping):
        return frozenset()
    raw_names = review_surface.get("assumption_names")
    if not isinstance(raw_names, list):
        return frozenset()
    namespace, separator, _ = entry_module.rpartition(".")
    if not separator:
        # Paper graph entrypoints may be the root aggregator module itself
        # (for example, `PaperId` rather than `PaperId.ProofInterface`).  That
        # root is also the namespace of its paper-local assumptions.
        namespace = entry_module

    def qualified(name: str) -> str:
        if "." in name or not namespace:
            return name
        return f"{namespace}.{name}"

    return frozenset(
        qualified(str(name).strip())
        for name in raw_names
        if isinstance(name, str) and str(name).strip()
    )


@dataclass(frozen=True)
class V11LeanReviewGraphRequestPlan:
    """One typed plan shared by Lean acquisition and carrier validation.

    The plan contains only names and contracts selected by the typed source
    routes plus the already validated import-closure identity.  It does not
    discover a Lean declaration or decide whether any semantic claim matches.
    """

    entry_module: str
    paper_modules: tuple[str, ...]
    workspace_modules: tuple[str, ...]
    specifications: tuple[str, ...]
    selected_routes: tuple[EvidenceRoute, ...]
    semantic_declarations: frozenset[str]
    quarantined_support_declarations: frozenset[str]
    semantic_contracts: frozenset[tuple[str, str, str]]
    semantic_review_claim_declarations: frozenset[str]
    lean_import_closure_sha256: str

    def request_projection(self) -> Mapping[str, object]:
        """Return the exact serialized request consumed by a graph carrier."""

        return MappingProxyType(
            {
                "schema": V11_LEAN_REVIEW_GRAPH_REQUEST_SCHEMA,
                "entry_module": self.entry_module,
                "inventory_modules": [],
                "paper_modules": list(self.paper_modules),
                "workspace_modules": list(self.workspace_modules),
                "specification_names": list(self.specifications),
                "semantic_declaration_names": sorted(
                    self.semantic_declarations
                ),
                "quarantined_support_declaration_names": sorted(
                    self.quarantined_support_declarations
                ),
                "semantic_contracts": [
                    {
                        "specification": specification,
                        "evidence": evidence,
                        "mode": mode,
                    }
                    for specification, evidence, mode in sorted(
                        self.semantic_contracts
                    )
                ],
                "semantic_review_claim_declaration_names": sorted(
                    self.semantic_review_claim_declarations
                ),
                "semantic_manifest_modules": list(self.workspace_modules),
                "axiom_root_names": sorted(
                    self.semantic_declarations
                    | self.quarantined_support_declarations
                ),
                "include_semantic_displays": True,
                "include_axiom_closure": True,
                "require_build": True,
                "lean_import_closure_sha256": (
                    self.lean_import_closure_sha256
                ),
            }
        )


def build_graph_request_plan(
    route_set: EvidenceRouteSet,
    expected_specifications: Iterable[str],
    *,
    entry_module: str,
    paper_modules: Iterable[str],
    workspace_modules: Iterable[str],
    lean_import_closure: Mapping[str, Any],
) -> V11LeanReviewGraphRequestPlan:
    """Build one exact request plan from typed routes and validated topology.

    The returned fields drive both the native Lean inventory call and the
    serialized carrier request, so those two representations cannot drift.
    """

    expected = tuple(
        sorted(
            {
                str(specification).strip()
                for specification in expected_specifications
                if str(specification).strip()
            }
        )
    )
    if not expected:
        raise ValueError("v11 Lean review graph has no selected specifications")
    selected_entry_module = str(entry_module).strip()
    if not selected_entry_module:
        raise ValueError("v11 Lean import closure has no entry module")
    selected_paper_modules = tuple(
        sorted(
            {
                str(module).strip()
                for module in paper_modules
                if str(module).strip()
            }
        )
    )
    if not selected_paper_modules:
        raise ValueError("v11 Lean import closure contains no paper-owned modules")
    selected_workspace_modules = tuple(
        sorted(
            {
                str(module).strip()
                for module in workspace_modules
                if str(module).strip()
            }
        )
    )
    missing_paper_modules = sorted(
        set(selected_paper_modules) - set(selected_workspace_modules)
    )
    if missing_paper_modules:
        raise ValueError(
            "v11 Lean paper modules are absent from the workspace closure: "
            + ", ".join(missing_paper_modules[:4])
        )

    routes_by_specification = route_set.result_route_by_specification()
    missing_specifications = sorted(set(expected) - set(routes_by_specification))
    if missing_specifications:
        raise ValueError(
            "v11 Lean review graph lacks typed routes for: "
            + ", ".join(missing_specifications[:4])
        )
    selected_routes = tuple(routes_by_specification[name] for name in expected)
    semantic_declarations = set(route_set.source_semantic_declarations())
    quarantined_support_declarations = {
        declaration
        for route in route_set.routes
        if route.inventory_role == "quarantined_source_defect"
        for declaration in route.support_declarations
    }
    for route in selected_routes:
        if (
            route.semantic_review_target_kind
            is SemanticReviewTargetKind.DEFINITION_DECLARATION
        ):
            semantic_declarations.add(route.semantic_review_declaration)
    semantic_contracts = frozenset(
        (
            route.spec_declaration,
            route.evidence_declaration,
            route.evidence_mode,
        )
        for route in selected_routes
    )
    semantic_review_claim_declarations = frozenset(
        route.semantic_review_declaration for route in selected_routes
    )
    return V11LeanReviewGraphRequestPlan(
        entry_module=selected_entry_module,
        paper_modules=selected_paper_modules,
        workspace_modules=selected_workspace_modules,
        specifications=expected,
        selected_routes=selected_routes,
        semantic_declarations=frozenset(semantic_declarations),
        quarantined_support_declarations=frozenset(
            quarantined_support_declarations
        ),
        semantic_contracts=semantic_contracts,
        semantic_review_claim_declarations=semantic_review_claim_declarations,
        lean_import_closure_sha256=stable_json_sha256(lean_import_closure),
    )


def stable_json_sha256(value: object) -> str:
    """Hash one canonical JSON value for a portable graph identity."""

    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def graph_engine_projection(repository_root: Path) -> dict[str, object]:
    """Return the portable identity of the native Lean graph producer."""

    try:
        from scripts.lean_signature_manifest import (
            _semantic_contract_closure_hash_tool_identity,
            portable_semantic_hash_tool_identity,
        )

        raw_hash_tool = _semantic_contract_closure_hash_tool_identity()
        hash_tool = portable_semantic_hash_tool_identity(raw_hash_tool)
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        raise ValueError("v11 Lean graph hash-tool identity is unavailable") from exc
    if not hash_tool:
        raise ValueError("v11 Lean graph hash-tool identity is unavailable")
    try:
        return lean_declaration_graph_producer_identity(
            repository_root,
            semantic_hash_tool_identity=hash_tool,
        )
    except ValueError as exc:
        raise ValueError("v11 Lean graph engine source is unavailable") from exc


def typed_route_projection(statement_map: object) -> dict[str, object]:
    """Project exactly the route fields that can change Lean's graph request."""

    try:
        route_set = EvidenceRouteSet.from_source_map(statement_map)
        result_routes = route_set.result_routes()
    except ObligationRouteError as exc:
        raise ValueError("v11 Lean graph has invalid typed routes: " + str(exc)) from exc
    return {
        "schema": 1,
        "result_routes": [
            {
                "specification": route.spec_declaration,
                "evidence": route.evidence_declaration,
                "mode": route.evidence_mode,
                "semantic_review_target_kind": (
                    route.semantic_review_target_kind.value
                ),
                "semantic_review_declaration": (
                    route.semantic_review_declaration
                ),
            }
            for route in sorted(
                result_routes, key=lambda item: item.spec_declaration
            )
        ],
        "source_semantic_declarations": list(
            route_set.source_semantic_declarations()
        ),
        "quarantined_defect_support_declarations": sorted(
            {
                declaration
                for route in route_set.routes
                if route.inventory_role == "quarantined_source_defect"
                for declaration in route.support_declarations
            }
        ),
    }


def graph_context_input_projection(
    context: V11GraphContextView,
    *,
    repository_root: Path,
) -> dict[str, object]:
    """Bind only immutable inputs that can change the Lean-owned graph."""

    closure_snapshot = context.json_snapshot(
        context.canonical_sidecar_path("LEAN_IMPORT_CLOSURE_RECEIPT.json")
    )
    if closure_snapshot is None:
        raise ValueError(
            "v11 Lean graph transaction did not snapshot "
            "LEAN_IMPORT_CLOSURE_RECEIPT.json"
        )
    try:
        relative = (
            closure_snapshot.path.resolve()
            .relative_to(repository_root.resolve())
            .as_posix()
        )
    except (OSError, RuntimeError, ValueError) as exc:
        raise ValueError("v11 Lean graph input escapes the repository") from exc
    graph_inputs = [
        {
            "path": relative,
            "state": (
                "present" if closure_snapshot.raw_bytes is not None else "absent"
            ),
            "sha256": closure_snapshot.sha256,
            "byte_length": (
                len(closure_snapshot.raw_bytes)
                if isinstance(closure_snapshot.raw_bytes, bytes)
                else None
            ),
        }
    ]
    return {
        "schema": 4,
        "graph_inputs": graph_inputs,
        "graph_engine": graph_engine_projection(repository_root),
        "typed_route_graph": typed_route_projection(context.statement_map),
    }


def graph_context_input_sha256(
    context: V11GraphContextView,
    *,
    repository_root: Path,
) -> str:
    """Hash the complete portable graph-input contract for one paper."""

    return stable_json_sha256(
        {
            "schema": 4,
            "paper": context.folder.name,
            "source_semantic_lane": context.source_semantic_lane,
            "input_projection": graph_context_input_projection(
                context,
                repository_root=repository_root,
            ),
        }
    )


def _operational_graph_carrier(
    *,
    paper: str,
    source_semantic_lane: str,
    context_input_sha256: str,
    graph_request: Mapping[str, Any],
    inventory: Mapping[str, Any],
) -> dict[str, Any]:
    """Serialize one exact Lean inventory without granting acceptance."""

    material: dict[str, Any] = {
        "schema": V11_LEAN_REVIEW_GRAPH_CARRIER_SCHEMA,
        "acceptance_credential": False,
        "operational_scheduling_only": True,
        "paper": paper,
        "source_semantic_lane": source_semantic_lane,
        "context_input_sha256": context_input_sha256,
        "graph_request": dict(graph_request),
        "inventory": dict(inventory),
        "inventory_sha256": stable_json_sha256(inventory),
    }
    material["receipt_integrity_sha256"] = stable_json_sha256(material)
    return material


def _validated_operational_graph_carrier_inventory(
    raw: object,
    *,
    paper: str,
    source_semantic_lane: str,
    context_input_sha256: str,
    graph_request: Mapping[str, Any],
) -> Mapping[str, Any] | None:
    """Validate one operational carrier against exact reconstructed inputs."""

    if raw is None:
        return None
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
    if not isinstance(raw, Mapping) or set(raw) != required:
        raise V11LeanReviewGraphCarrierMismatch(
            "v11 Lean review graph carrier fields are malformed"
        )
    material = {
        key: value for key, value in raw.items() if key != "receipt_integrity_sha256"
    }
    inventory = raw.get("inventory")
    if (
        raw.get("schema") != V11_LEAN_REVIEW_GRAPH_CARRIER_SCHEMA
        or raw.get("acceptance_credential") is not False
        or raw.get("operational_scheduling_only") is not True
        or raw.get("paper") != paper
        or raw.get("source_semantic_lane") != source_semantic_lane
        or raw.get("context_input_sha256") != context_input_sha256
        or raw.get("graph_request") != dict(graph_request)
        or not isinstance(inventory, Mapping)
        or raw.get("inventory_sha256") != stable_json_sha256(inventory)
        or raw.get("receipt_integrity_sha256") != stable_json_sha256(material)
    ):
        raise V11LeanReviewGraphCarrierMismatch(
            "v11 Lean review graph carrier does not match the current frozen inputs"
        )
    return inventory


def validated_graph_carrier_inventory(
    folder: Path,
    context: V11GraphContextView,
    *,
    graph_request: Mapping[str, Any],
    repository_root: Path,
) -> Mapping[str, Any] | None:
    """Return a saved Lean inventory only under the exact current contract.

    The carrier cannot select declarations or waive a check. Its request must
    equal the request reconstructed from the current typed routes and current
    Lean import closure. The caller must then revalidate the complete
    inventory and every accepting semantic obligation.
    """

    return _validated_operational_graph_carrier_inventory(
        context.v11_lean_review_graph_payload,
        paper=folder.name,
        source_semantic_lane=V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE,
        context_input_sha256=graph_context_input_sha256(
            context,
            repository_root=repository_root,
        ),
        graph_request=graph_request,
    )


@dataclass(frozen=True)
class V11LeanReviewGraphProjection:
    """Strict Lean-owned semantic projection before reviewer-ledger joins."""

    semantic_targets: Mapping[str, Mapping[str, Any]]
    source_declarations: Mapping[str, Mapping[str, Any]]
    library_source_declarations: Mapping[str, Mapping[str, Any]]
    semantic_contracts: Mapping[tuple[str, str, str], Mapping[str, Any]]
    review_claim_manifests: Mapping[str, Mapping[str, Any]]
    paper_semantic_targets: Mapping[str, Mapping[str, Any]]
    library_semantic_targets: Mapping[str, Mapping[str, Any]]
    paper_declaration_sources: Mapping[str, Mapping[str, Any]]
    library_declaration_sources: Mapping[str, Mapping[str, Any]]


@dataclass(frozen=True)
class V11LeanReviewGraphAcquisition:
    """One strictly projected current graph and its acquisition disposition."""

    inventory: Mapping[str, Any]
    projection: V11LeanReviewGraphProjection
    acquired_fresh: bool


@dataclass(frozen=True)
class V11LeanReviewGraphMaterial:
    """One frozen current-v11 graph transaction before reviewer-ledger joins."""

    request_plan: V11LeanReviewGraphRequestPlan
    graph_request: Mapping[str, Any]
    acquisition: V11LeanReviewGraphAcquisition
    module_sources: Mapping[str, tuple[Path, bytes]]
    build_input_provider: object | None
    carrier_reused: bool


def foundation_frontier_unregistered_diagnostic(
    preview: Mapping[str, object],
    *,
    expected_count: int,
    example_limit: int = 8,
) -> str:
    """Render one bounded, content-bound diagnostic for unknown graph roots."""

    rows_by_declaration: dict[str, dict[str, str]] = {}
    raw_specifications = preview.get("specifications")
    if isinstance(raw_specifications, list):
        for specification_row in raw_specifications:
            if not isinstance(specification_row, Mapping):
                continue
            raw_occurrences = specification_row.get(
                "unregistered_external_occurrences"
            )
            if not isinstance(raw_occurrences, list):
                continue
            for occurrence in raw_occurrences:
                if not isinstance(occurrence, Mapping):
                    continue
                declaration = str(occurrence.get("declaration") or "").strip()
                if not declaration:
                    continue
                rows_by_declaration.setdefault(
                    declaration,
                    {
                        "declaration": declaration,
                        "module": str(occurrence.get("module") or "").strip(),
                        "declaration_kind": str(
                            occurrence.get("declaration_kind") or ""
                        ).strip(),
                    },
                )
    rows = [rows_by_declaration[name] for name in sorted(rows_by_declaration)]
    if len(rows) != expected_count:
        return (
            "Lean foundation-frontier preview has inconsistent unregistered "
            f"root detail (summary={expected_count}, rows={len(rows)})"
        )
    limit = max(1, example_limit)
    examples = []
    for row in rows[:limit]:
        module = row["module"] or "<unresolved>"
        kind = row["declaration_kind"] or "<unresolved>"
        examples.append(f"{row['declaration']} [module={module}, kind={kind}]")
    omitted = len(rows) - len(examples)
    suffix = f"; ... {omitted} more" if omitted else ""
    return (
        "Lean foundation-frontier preview found "
        f"{len(rows)} material declaration(s) outside the paper, AppliedModelingLib, "
        "and registered foundation packages: "
        + "; ".join(examples)
        + suffix
        + "; diagnostic_sha256="
        + stable_json_sha256(rows)
    )


def project_validated_graph_inventory(
    repository_root: Path,
    folder: Path,
    request_plan: V11LeanReviewGraphRequestPlan,
    *,
    inventory: Mapping[str, Any],
    module_sources: Mapping[str, tuple[Path, bytes]],
) -> V11LeanReviewGraphProjection:
    """Validate and project one complete Lean inventory for semantic review.

    Lean already owns declaration discovery, elaborated displays, dependency
    closure, proof contracts, axiom closure, and source ranges.  This function
    checks the complete native inventory against the one typed request plan and
    projects only those authenticated facts.  It does not read Lean source,
    parse declarations, select paper claims, join reviewer verdicts, or grant
    closeout acceptance.
    """

    if not inventory:
        raise ValueError("Lean did not produce the complete v11 declaration graph")
    try:
        from scripts.lean_review_surface import (
            lean_owned_semantic_review_display_surface_from_inventory,
        )
        from scripts.lean_signature_manifest import (
            foundation_frontier_preview_from_inventory,
            lean_inventory_library_source_declaration_records,
            lean_inventory_source_declaration_records,
            passing_semantic_contract_rows_from_inventory,
            semantic_review_claim_surfaces_from_inventory,
            semantic_signature_sha256s_from_inventory,
        )
        from scripts.semantic_prerequisite_projection import (
            V11_DEFINITION_TARGET_PROTOCOL,
            V11_LEAN_TARGET_PROTOCOL,
        )

        expected = request_plan.specifications
        expected_set = set(expected)
        semantic_declarations = set(request_plan.semantic_declarations)
        semantic_review_declarations = set(
            request_plan.semantic_review_claim_declarations
        )
        foundation_preview = foundation_frontier_preview_from_inventory(
            repository_root,
            inventory,
            expected_specifications=expected,
        )
        foundation_summary = foundation_preview.get("summary")
        if not isinstance(foundation_summary, Mapping):
            raise ValueError("Lean foundation-frontier preview has no summary")
        unregistered_count = foundation_summary.get(
            "unregistered_external_root_count"
        )
        if not isinstance(unregistered_count, int) or unregistered_count < 0:
            raise ValueError("Lean foundation-frontier preview count is malformed")
        if unregistered_count:
            raise ValueError(
                foundation_frontier_unregistered_diagnostic(
                    foundation_preview,
                    expected_count=unregistered_count,
                )
            )

        claim_surfaces = semantic_review_claim_surfaces_from_inventory(
            inventory,
            expected_declarations=semantic_review_declarations,
        )
        review_claim_manifests: dict[str, dict[str, Any]] = {}
        for route in request_plan.selected_routes:
            declaration = route.semantic_review_declaration
            review_claim_manifests[route.spec_declaration] = {
                "semantic_review_declaration": declaration,
                **claim_surfaces[declaration],
            }
        semantic_contract_rows = passing_semantic_contract_rows_from_inventory(
            inventory,
            expected_contracts=request_plan.semantic_contracts,
        )
        review_surface = lean_owned_semantic_review_display_surface_from_inventory(
            inventory,
            expected_specifications=expected,
        )
        spec_targets = review_surface.specifications
        paper_targets = review_surface.paper_declarations
        library_targets = review_surface.library_declarations
        paper_target_names = tuple(sorted(paper_targets))
        library_target_names = tuple(sorted(library_targets))
        classified_semantic_roots = set(paper_targets) | set(library_targets)
        if not semantic_declarations.issubset(classified_semantic_roots):
            missing = sorted(semantic_declarations - classified_semantic_roots)
            raise ValueError(
                "Lean declaration graph did not classify every explicit "
                "source-semantic root: "
                + ", ".join(missing[:4])
            )
        signature_declarations = (
            semantic_review_declarations
            | set(paper_target_names)
            | set(library_target_names)
        )
        semantic_signatures = semantic_signature_sha256s_from_inventory(
            inventory,
            expected_declarations=signature_declarations,
        )
        paper_targets = {
            name: {
                **dict(target),
                "elaborated_signature_sha256": semantic_signatures[name],
            }
            for name, target in paper_targets.items()
        }
        library_targets = {
            name: {
                **dict(target),
                "elaborated_signature_sha256": semantic_signatures[name],
            }
            for name, target in library_targets.items()
        }

        paper_source_names = tuple(sorted(expected_set | set(paper_target_names)))
        source_declarations = lean_inventory_source_declaration_records(
            inventory,
            module_sources,
            declaration_names=paper_source_names,
        )
        library_source_declarations = (
            lean_inventory_library_source_declaration_records(
                inventory,
                module_sources,
            )
        )

        interface_path = (folder / "PaperInterface.lean").resolve()
        interface_content = next(
            (
                content
                for _module, (path, content) in module_sources.items()
                if path == interface_path
            ),
            None,
        )
        if interface_content is None:
            raise ValueError("Lean declaration graph omits PaperInterface.lean")
        interface_sha256 = hashlib.sha256(interface_content).hexdigest()
        semantic_targets: dict[str, dict[str, Any]] = {}
        for route in request_plan.selected_routes:
            claim_manifest = review_claim_manifests[route.spec_declaration]
            if (
                route.semantic_review_target_kind
                is SemanticReviewTargetKind.DEFINITION_DECLARATION
            ):
                target = paper_targets.get(route.semantic_review_declaration)
                if not isinstance(target, Mapping):
                    target = library_targets.get(route.semantic_review_declaration)
                if not isinstance(target, Mapping):
                    raise ValueError(
                        "Lean produced no definition review target for "
                        f"`{route.spec_declaration}`"
                    )
                semantic_targets[route.spec_declaration] = {
                    "display": str(target.get("display") or ""),
                    "display_sha256": str(target.get("display_sha256") or ""),
                    "expansion_count": (
                        1 if target.get("root_expanded") is True else 0
                    ),
                    "expanded_declarations": (
                        (route.semantic_review_declaration,)
                        if target.get("root_expanded") is True
                        else ()
                    ),
                    "prerequisite_declarations": tuple(
                        target.get("direct_paper_declarations", ())
                    ),
                    "library_declarations": tuple(
                        target.get("direct_library_declarations", ())
                    ),
                    "semantic_target_kind": "definition_declaration",
                    "semantic_review_declaration": (
                        route.semantic_review_declaration
                    ),
                    "lean_target_protocol": V11_DEFINITION_TARGET_PROTOCOL,
                    "paper_interface_sha256": interface_sha256,
                    "lean_expansion_protocol": V11_DEFINITION_TARGET_PROTOCOL,
                    "review_claim_manifest_sha256": claim_manifest[
                        "manifest_sha256"
                    ],
                    "review_claim_atoms_sha256": claim_manifest[
                        "claim_atoms_sha256"
                    ],
                    "review_claim_atoms": claim_manifest["claim_atoms"],
                    "elaborated_signature_sha256": semantic_signatures[
                        route.semantic_review_declaration
                    ],
                }
            else:
                target = spec_targets[route.spec_declaration]
                semantic_targets[route.spec_declaration] = {
                    **dict(target),
                    "elaborated_signature_sha256": semantic_signatures[
                        route.semantic_review_declaration
                    ],
                    "semantic_target_kind": "spec_proposition",
                    "semantic_review_declaration": route.spec_declaration,
                    "lean_target_protocol": V11_LEAN_TARGET_PROTOCOL,
                    "paper_interface_sha256": interface_sha256,
                    "lean_expansion_protocol": V11_LEAN_TARGET_PROTOCOL,
                    "review_claim_manifest_sha256": claim_manifest[
                        "manifest_sha256"
                    ],
                    "review_claim_atoms_sha256": claim_manifest[
                        "claim_atoms_sha256"
                    ],
                    "review_claim_atoms": claim_manifest["claim_atoms"],
                }

        paper_source_overrides: dict[str, dict[str, Any]] = {}
        for name, record in source_declarations.items():
            path = record.get("source_path")
            raw_range = record.get("source_range")
            if not isinstance(path, Path) or not isinstance(raw_range, Mapping):
                continue
            try:
                relative = path.relative_to(repository_root).as_posix()
            except ValueError:
                continue
            paper_source_overrides[name] = {
                "paper_declaration": name,
                "paper_declaration_kind": (
                    "def"
                    if str(record.get("declaration_kind") or "") == "definition"
                    else str(record.get("declaration_kind") or "")
                ),
                "paper_declaration_source": str(record.get("source") or ""),
                "paper_declaration_sha256": str(
                    record.get("source_sha256") or ""
                ),
                "paper_source_path": relative,
                "paper_line_start": raw_range.get("line_start"),
            }
        library_source_overrides: dict[str, dict[str, Any]] = {}
        for name, record in library_source_declarations.items():
            path = record.get("source_path")
            raw_range = record.get("source_range")
            if not isinstance(path, Path) or not isinstance(raw_range, Mapping):
                continue
            try:
                relative = path.relative_to(repository_root).as_posix()
            except ValueError:
                continue
            library_source_overrides[name] = {
                "library_definition": str(record.get("source") or ""),
                "library_definition_sha256": str(
                    record.get("source_sha256") or ""
                ),
                "library_definition_error": "",
                "library_source_path": relative,
                "library_line_start": raw_range.get("line_start"),
                "library_line_end": raw_range.get("line_end"),
            }
    except (OSError, RuntimeError, TypeError) as exc:
        raise ValueError(str(exc)) from exc

    return V11LeanReviewGraphProjection(
        semantic_targets=MappingProxyType(semantic_targets),
        source_declarations=MappingProxyType(dict(source_declarations)),
        library_source_declarations=MappingProxyType(
            dict(library_source_declarations)
        ),
        semantic_contracts=MappingProxyType(dict(semantic_contract_rows)),
        review_claim_manifests=MappingProxyType(review_claim_manifests),
        paper_semantic_targets=MappingProxyType(paper_targets),
        library_semantic_targets=MappingProxyType(library_targets),
        paper_declaration_sources=MappingProxyType(paper_source_overrides),
        library_declaration_sources=MappingProxyType(library_source_overrides),
    )


def acquire_validated_graph_projection(
    repository_root: Path,
    folder: Path,
    request_plan: V11LeanReviewGraphRequestPlan,
    *,
    module_sources: Mapping[str, tuple[Path, bytes]],
    inventory: Mapping[str, Any] | None = None,
    build_input_provider: object | None = None,
    additional_axiom_root_names: Iterable[str] = (),
    root_semantic_manifest_declaration_names: Iterable[str] = (),
    timeout_seconds: int = V11_LEAN_DECLARATION_GRAPH_TIMEOUT_SECONDS,
    build_timeout_seconds: int = 600,
) -> V11LeanReviewGraphAcquisition:
    """Acquire at most once and strictly project the one typed current graph."""

    additional_roots = request_plan.quarantined_support_declarations | frozenset(
        str(name).strip()
        for name in additional_axiom_root_names
        if str(name).strip()
    )
    manifest_roots = frozenset(
        str(name).strip()
        for name in root_semantic_manifest_declaration_names
        if str(name).strip()
    )
    if not manifest_roots.issubset(additional_roots):
        raise ValueError(
            "root semantic manifests are absent from the Lean axiom-root request"
        )
    acquired_fresh = inventory is None
    if inventory is None:
        if build_input_provider is None:
            raise ValueError("current Lean graph acquisition has no build provider")
        from scripts.lean_signature_manifest import run_lean_declaration_inventory

        inventory = run_lean_declaration_inventory(
            repository_root,
            request_plan.entry_module,
            inventory_modules=(),
            paper_modules=request_plan.paper_modules,
            workspace_module_names=request_plan.workspace_modules,
            specification_names=request_plan.specifications,
            semantic_declaration_names=request_plan.semantic_declarations,
            semantic_contracts=request_plan.semantic_contracts,
            semantic_review_claim_declaration_names=(
                request_plan.semantic_review_claim_declarations
            ),
            semantic_manifest_modules=request_plan.workspace_modules,
            axiom_root_names=(
                request_plan.semantic_declarations | additional_roots
            ),
            root_semantic_manifest_declaration_names=manifest_roots,
            include_semantic_displays=True,
            include_axiom_closure=True,
            timeout_seconds=timeout_seconds,
            build_timeout_seconds=build_timeout_seconds,
            build_input_provider=build_input_provider,
            require_build=True,
        )
    projection = project_validated_graph_inventory(
        repository_root,
        folder,
        request_plan,
        inventory=inventory,
        module_sources=module_sources,
    )
    return V11LeanReviewGraphAcquisition(
        inventory=inventory,
        projection=projection,
        acquired_fresh=acquired_fresh,
    )


def paper_module_names_from_sources(
    repository_root: Path,
    folder: Path,
    module_sources: Mapping[str, tuple[Path, bytes]],
    *,
    required_entry_module: str = "",
) -> tuple[str, ...]:
    """Classify paper-owned modules from exact paths, never parsed imports."""

    root = repository_root.resolve()
    paper_folder = folder.resolve()
    expected_folder = (root / "papers" / folder.name).resolve()
    if paper_folder != expected_folder:
        raise ValueError("v11 Lean graph folder is outside the repository papers root")
    paper_aggregator = (root / "papers" / f"{folder.name}.lean").resolve()
    modules = tuple(
        sorted(
            module
            for module, (path, _content) in module_sources.items()
            if path.resolve() == paper_aggregator
            or paper_folder in path.resolve().parents
        )
    )
    if not modules:
        raise ValueError("v11 Lean import closure contains no paper-owned modules")
    required = str(required_entry_module).strip()
    if required and required not in modules:
        raise ValueError("Lean-loaded closure omits the paper graph entry module")
    return modules


def build_v11_lean_review_graph_material(
    repository_root: Path,
    folder: Path,
    expected_specifications: Iterable[str],
    *,
    context: V11GraphAcquisitionContextView,
    checkpoint_projection_only: bool = False,
) -> V11LeanReviewGraphMaterial:
    """Own the complete frozen current-v11 graph-input transaction.

    This service validates the typed source routes and standalone import
    closure, acquires the exact repository-source snapshot, selects paper
    modules by path, reuses or acquires one Lean graph, strictly projects it,
    and checks agreement with the evidence transaction's frozen bytes. It does
    not read reviewer ledgers, issue verdicts, or grant closeout acceptance.
    """

    root = repository_root.resolve()
    paper_folder = folder.resolve()
    expected = tuple(
        sorted(
            {
                str(specification).strip()
                for specification in expected_specifications
                if str(specification).strip()
            }
        )
    )
    if not expected:
        raise ValueError("v11 Lean review graph has no selected specifications")
    if (
        not getattr(context, "issued_by_builder", False)
        or getattr(context, "folder", None) != paper_folder
        or getattr(context, "source_semantic_lane", "")
        != V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
    ):
        raise ValueError(
            "v11 Lean review graph requires its builder-issued current transaction"
        )
    source_map = context.statement_map
    if not isinstance(source_map, Mapping):
        raise ValueError("v11 Lean review graph lacks its exact source map")
    try:
        route_set = EvidenceRouteSet.from_source_map(source_map)
    except ObligationRouteError as exc:
        raise ValueError(
            "v11 Lean review graph has invalid typed routes: " + str(exc)
        ) from exc

    from scripts.lean_import_closure import (
        validated_lean_import_closure_receipt_payload,
    )
    from scripts.lean_signature_manifest import (
        RepositoryBuildInputSnapshotProvider,
    )

    try:
        validated_closure_receipt = validated_lean_import_closure_receipt_payload(
            context.json_payload(
                context.canonical_sidecar_path(
                    "LEAN_IMPORT_CLOSURE_RECEIPT.json"
                )
            ),
            paper=paper_folder.name,
        )
    except ValueError as exc:
        raise ValueError(
            "v11 Lean review graph lacks a current standalone Lean "
            "import-closure receipt: " + str(exc)
        ) from exc
    closure = validated_closure_receipt.get("lean_import_closure")
    if not isinstance(closure, Mapping):
        raise ValueError("v11 Lean import-closure receipt has no closure object")
    entry_module = str(closure.get("entry_module") or "").strip()
    if not entry_module:
        raise ValueError("v11 Lean import-closure receipt has no entry module")

    if checkpoint_projection_only:
        if context.v11_lean_review_graph_payload is None:
            raise V11LeanReviewGraphCarrierMismatch(
                "v11 review projection requires an exact graph checkpoint"
            )
        source_provider = RepositoryBuildInputSnapshotProvider(root)
        source_snapshot = source_provider.validated_repository_source_snapshot(
            closure
        )
        build_input_provider: object | None = None
    else:
        build_input_provider = RepositoryBuildInputSnapshotProvider(
            root,
            lean_import_closure_payload=closure,
        )
        source_snapshot = build_input_provider.repository_source_snapshot(
            entry_module
        )
    if not source_snapshot:
        raise ValueError("v11 Lean import closure has no exact repository sources")
    module_sources = {
        module: (path.resolve(), content)
        for module, path, content, _digest in source_snapshot
    }
    paper_modules = paper_module_names_from_sources(
        root,
        paper_folder,
        module_sources,
        required_entry_module=entry_module,
    )
    request_plan = build_graph_request_plan(
        route_set,
        expected,
        entry_module=entry_module,
        paper_modules=paper_modules,
        workspace_modules=module_sources,
        lean_import_closure=closure,
    )
    assumption_root_names = _configured_assumption_root_names(
        context,
        entry_module=entry_module,
    )
    graph_request = dict(request_plan.request_projection())
    graph_request["axiom_root_names"] = sorted(
        request_plan.semantic_declarations
        | request_plan.quarantined_support_declarations
        | assumption_root_names
    )
    graph_request["root_semantic_manifest_declaration_names"] = sorted(
        assumption_root_names
    )
    inventory = validated_graph_carrier_inventory(
        paper_folder,
        context,
        graph_request=graph_request,
        repository_root=root,
    )
    carrier_reused = inventory is not None
    if inventory is None and checkpoint_projection_only:
        raise V11LeanReviewGraphCarrierMismatch(
            "v11 review projection has no exact saved Lean inventory"
        )
    acquisition = acquire_validated_graph_projection(
        root,
        paper_folder,
        request_plan,
        module_sources=module_sources,
        inventory=inventory,
        build_input_provider=build_input_provider,
        additional_axiom_root_names=assumption_root_names,
        root_semantic_manifest_declaration_names=assumption_root_names,
    )
    frozen_input_bytes = context.file_bytes_override()
    for path, content in module_sources.values():
        if path in frozen_input_bytes and frozen_input_bytes[path] != content:
            raise ValueError(f"Lean graph and evidence snapshots disagree for {path}")
    return V11LeanReviewGraphMaterial(
        request_plan=request_plan,
        graph_request=MappingProxyType(graph_request),
        acquisition=acquisition,
        module_sources=MappingProxyType(module_sources),
        build_input_provider=build_input_provider,
        carrier_reused=carrier_reused,
    )


def builder_issued_v11_lean_review_surface(
    folder: Path,
    context: RetainedV11GraphContextView,
) -> RetainedV11ReviewSurfaceView | None:
    """Return the one graph retained by an exact builder-issued context.

    The context owns the unforgeable run-scoped capability.  This current
    service owns the graph's operational consumers, so the planner no longer
    reaches through the historical evidence module to find or serialize it.
    """

    if (
        not getattr(context, "issued_by_builder", False)
        or getattr(context, "folder", None) != folder.resolve()
        or getattr(context, "source_semantic_lane", "")
        != V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
    ):
        return None
    accessor = getattr(context, "retained_v11_review_surface", None)
    if not callable(accessor):
        return None
    surface = accessor()
    if surface is None:
        return None
    for field in (
        "graph_request",
        "declaration_inventory",
        "semantic_targets",
        "paper_semantic_targets",
        "library_semantic_targets",
        "library_declaration_sources",
    ):
        if not isinstance(getattr(surface, field, None), Mapping):
            raise ValueError(f"retained v11 Lean review surface has malformed {field}")
    if getattr(surface, "build_input_provider", None) is None:
        raise ValueError("retained v11 Lean review surface has no build provider")
    return surface


def builder_issued_v11_lean_operational_provider(
    folder: Path,
    context: RetainedV11GraphContextView,
) -> object | None:
    """Return the exact graph-owned build snapshot for downstream planning."""

    surface = builder_issued_v11_lean_review_surface(folder, context)
    return surface.build_input_provider if surface is not None else None


def builder_issued_v11_lean_review_graph_carrier(
    folder: Path,
    context: RetainedV11GraphContextView,
    *,
    repository_root: Path,
) -> dict[str, Any] | None:
    """Serialize the retained graph as a non-authoritative scheduling carrier."""

    surface = builder_issued_v11_lean_review_surface(folder, context)
    if surface is None:
        return None
    return _operational_graph_carrier(
        paper=folder.name,
        source_semantic_lane=V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE,
        context_input_sha256=graph_context_input_sha256(
            context,
            repository_root=repository_root,
        ),
        graph_request=surface.graph_request,
        inventory=surface.declaration_inventory,
    )


def _v11_graph_checkpoint_index_path(
    repository_root: Path,
    folder: Path,
) -> Path:
    return (
        repository_root
        / V11_LEAN_REVIEW_GRAPH_CHECKPOINT_RELATIVE
        / f"{folder.name}.json"
    )


def _terminal_graph_checkpoint_index_path(
    repository_root: Path,
    folder: Path,
) -> Path:
    return (
        repository_root
        / V11_TERMINAL_GRAPH_CHECKPOINT_RELATIVE
        / f"{folder.name}.json"
    )


def terminal_graph_input_sha256(
    repository_root: Path,
    folder: Path,
    *,
    graph_request: Mapping[str, Any],
    module_sources: Mapping[str, tuple[Path, bytes]],
) -> str:
    """Bind a recovery graph to portable exact current workspace bytes."""

    expected_modules = graph_request.get("workspace_modules")
    if (
        not isinstance(expected_modules, list)
        or any(not isinstance(module, str) or not module for module in expected_modules)
        or expected_modules != sorted(set(expected_modules))
        or set(expected_modules) != set(module_sources)
    ):
        raise ValueError(
            "terminal Lean graph request and workspace source closure differ"
        )
    root = repository_root.resolve()
    source_rows: list[dict[str, object]] = []
    for module in expected_modules:
        raw = module_sources.get(module)
        if (
            not isinstance(raw, tuple)
            or len(raw) != 2
            or not isinstance(raw[0], Path)
            or not isinstance(raw[1], bytes)
        ):
            raise ValueError("terminal Lean graph has a malformed workspace source")
        path, content = raw
        try:
            relative = path.resolve().relative_to(root).as_posix()
        except (OSError, RuntimeError, ValueError) as exc:
            raise ValueError(
                "terminal Lean graph workspace source escapes the repository"
            ) from exc
        source_rows.append(
            {
                "module": module,
                "path": relative,
                "sha256": hashlib.sha256(content).hexdigest(),
                "byte_length": len(content),
            }
        )
    return stable_json_sha256(
        {
            "schema": V11_TERMINAL_GRAPH_CHECKPOINT_SCHEMA,
            "paper": folder.name,
            "source_semantic_lane": V11_TERMINAL_GRAPH_EVIDENCE_LANE,
            "graph_engine": graph_engine_projection(repository_root),
            "graph_request": dict(graph_request),
            "workspace_sources": source_rows,
        }
    )


def current_terminal_lean_graph_inventory(
    repository_root: Path,
    folder: Path,
    *,
    graph_request: Mapping[str, Any],
    module_sources: Mapping[str, tuple[Path, bytes]],
) -> Mapping[str, Any] | None:
    """Load an exact-current recovery graph, treating any cache fault as a miss."""

    try:
        input_sha256 = terminal_graph_input_sha256(
            repository_root,
            folder,
            graph_request=graph_request,
            module_sources=module_sources,
        )
        raw = json.loads(
            _terminal_graph_checkpoint_index_path(
                repository_root, folder
            ).read_text(encoding="utf-8")
        )
        required = {
            "schema",
            "acceptance_credential",
            "operational_scheduling_only",
            "paper",
            "context_input_sha256",
            "graph_reference",
        }
        reference = raw.get("graph_reference") if isinstance(raw, Mapping) else None
        if (
            not isinstance(raw, Mapping)
            or set(raw) != required
            or raw.get("schema") != V11_TERMINAL_GRAPH_CHECKPOINT_SCHEMA
            or raw.get("acceptance_credential") is not False
            or raw.get("operational_scheduling_only") is not True
            or raw.get("paper") != folder.name
            or raw.get("context_input_sha256") != input_sha256
            or not isinstance(reference, Mapping)
        ):
            return None
        from scripts.closeout_content_store import load_closeout_object

        carrier = load_closeout_object(
            repository_root,
            reference,
            expected_kind="v11_terminal_lean_review_graph",
        )
        return _validated_operational_graph_carrier_inventory(
            carrier,
            paper=folder.name,
            source_semantic_lane=V11_TERMINAL_GRAPH_EVIDENCE_LANE,
            context_input_sha256=input_sha256,
            graph_request=graph_request,
        )
    except (
        OSError,
        RuntimeError,
        TypeError,
        ValueError,
        UnicodeDecodeError,
        json.JSONDecodeError,
    ):
        return None


def checkpoint_terminal_lean_graph(
    repository_root: Path,
    folder: Path,
    *,
    graph_request: Mapping[str, Any],
    module_sources: Mapping[str, tuple[Path, bytes]],
    inventory: Mapping[str, Any],
) -> Mapping[str, object]:
    """Persist a validated recovery graph as non-authoritative operational data."""

    from scripts.closeout_content_store import store_closeout_object
    from scripts.closeout_execution_state import atomic_write_json

    input_sha256 = terminal_graph_input_sha256(
        repository_root,
        folder,
        graph_request=graph_request,
        module_sources=module_sources,
    )
    carrier = _operational_graph_carrier(
        paper=folder.name,
        source_semantic_lane=V11_TERMINAL_GRAPH_EVIDENCE_LANE,
        context_input_sha256=input_sha256,
        graph_request=graph_request,
        inventory=inventory,
    )
    reference = store_closeout_object(
        repository_root,
        carrier,
        kind="v11_terminal_lean_review_graph",
    )
    atomic_write_json(
        _terminal_graph_checkpoint_index_path(repository_root, folder),
        {
            "schema": V11_TERMINAL_GRAPH_CHECKPOINT_SCHEMA,
            "acceptance_credential": False,
            "operational_scheduling_only": True,
            "paper": folder.name,
            "context_input_sha256": input_sha256,
            "graph_reference": reference,
        },
    )
    return reference


def checkpoint_builder_issued_v11_lean_review_graph(
    folder: Path,
    context: RetainedV11GraphContextView,
    *,
    repository_root: Path,
) -> Mapping[str, object] | None:
    """Persist one non-authoritative graph for a later planner invocation."""

    carrier = builder_issued_v11_lean_review_graph_carrier(
        folder,
        context,
        repository_root=repository_root,
    )
    if carrier is None:
        return None
    try:
        from scripts.closeout_content_store import store_closeout_object
        from scripts.closeout_execution_state import atomic_write_json

        reference = store_closeout_object(
            repository_root,
            carrier,
            kind="v11_lean_review_graph",
        )
        index = {
            "schema": V11_LEAN_REVIEW_GRAPH_CHECKPOINT_SCHEMA,
            "acceptance_credential": False,
            "operational_scheduling_only": True,
            "paper": folder.name,
            "context_input_sha256": graph_context_input_sha256(
                context,
                repository_root=repository_root,
            ),
            "graph_reference": reference,
        }
        atomic_write_json(
            _v11_graph_checkpoint_index_path(repository_root, folder),
            index,
        )
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        raise ValueError("could not checkpoint the v11 Lean review graph") from exc
    return reference


def current_v11_lean_review_graph_checkpoint_reference(
    folder: Path,
    context: RetainedV11GraphContextView,
    *,
    repository_root: Path,
) -> Mapping[str, object] | None:
    """Return an exact-current operational graph reference, if one exists."""

    path = _v11_graph_checkpoint_index_path(repository_root, folder)
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return None
    required = {
        "schema",
        "acceptance_credential",
        "operational_scheduling_only",
        "paper",
        "context_input_sha256",
        "graph_reference",
    }
    reference = raw.get("graph_reference") if isinstance(raw, Mapping) else None
    context_input_sha256 = graph_context_input_sha256(
        context,
        repository_root=repository_root,
    )
    if (
        not isinstance(raw, Mapping)
        or set(raw) != required
        or raw.get("schema") != V11_LEAN_REVIEW_GRAPH_CHECKPOINT_SCHEMA
        or raw.get("acceptance_credential") is not False
        or raw.get("operational_scheduling_only") is not True
        or raw.get("paper") != folder.name
        or raw.get("context_input_sha256") != context_input_sha256
        or not isinstance(reference, Mapping)
    ):
        return None
    try:
        from scripts.closeout_content_store import load_closeout_object

        carrier = load_closeout_object(
            repository_root,
            reference,
            expected_kind="v11_lean_review_graph",
        )
    except (OSError, RuntimeError, TypeError, ValueError):
        return None
    if (
        not isinstance(carrier, Mapping)
        or carrier.get("schema") != V11_LEAN_REVIEW_GRAPH_CARRIER_SCHEMA
        or carrier.get("paper") != folder.name
        or carrier.get("context_input_sha256") != context_input_sha256
    ):
        return None
    return dict(reference)
