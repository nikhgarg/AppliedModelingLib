#!/usr/bin/env python3
"""Parser-free current-v11 declaration, proof, and axiom gate.

The service consumes only typed source routes plus declaration and contract
records emitted from the elaborated Lean environment.  It does not read source
files, discover declarations, render presentation artifacts, or issue evidence.
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path

from scripts.current_closeout.declarations import (
    LeanDeclaration,
    declaration_index_from_inventory,
    resolve_declaration_name,
    typed_qualified_declaration_identity,
)
from scripts.obligation_routes import (
    EvidenceRoute,
    EvidenceRouteSet,
    ObligationRouteError,
)


@dataclass(frozen=True)
class ResultReviewRoute:
    configured_name: str
    qualified_specification: str
    route: EvidenceRoute


@dataclass(frozen=True)
class DirectReviewRoute:
    configured_name: str
    qualified_declaration: str


@dataclass(frozen=True)
class ReviewRoutePartition:
    result_routes: tuple[ResultReviewRoute, ...]
    direct_routes: tuple[DirectReviewRoute, ...]
    errors: tuple[str, ...]

    def result_map(self) -> dict[str, tuple[str, EvidenceRoute]]:
        return {
            row.configured_name: (row.qualified_specification, row.route)
            for row in self.result_routes
        }

    def direct_map(self) -> dict[str, str]:
        return {
            row.configured_name: row.qualified_declaration
            for row in self.direct_routes
        }


@dataclass(frozen=True)
class CurrentV11PrimaryGateResult:
    """Closed current-path result before evidence publication.

    Each error family corresponds to an accepting obligation.  Keeping the
    families explicit lets the closeout trace retain useful phase timings
    without letting separate implementations grant proof, axiom, or source
    credit.
    """

    declarations: dict[str, list[LeanDeclaration]]
    partition: ReviewRoutePartition
    configuration_errors: tuple[str, ...] = ()
    semantic_errors: tuple[str, ...] = ()
    proof_errors: tuple[str, ...] = ()
    axiom_errors: tuple[str, ...] = ()
    structure_errors: tuple[str, ...] = ()

    @property
    def errors(self) -> tuple[str, ...]:
        return (
            self.configuration_errors
            + self.semantic_errors
            + self.proof_errors
            + self.axiom_errors
            + self.structure_errors
        )

    @property
    def accepted(self) -> bool:
        return not self.errors


_CLOSEOUT_STATUSES = frozenset(
    {
        "formalized",
        "formalized with caveat",
        "partially formalized",
        "conditional",
    }
)
_ASSUMPTION_POLICY_VALUES = frozenset(
    {"strict", "source_assumptions_only", "source-plus-proof-boundary"}
)
_HUMAN_SUMMARY_REVIEW_VALUES = frozenset(
    {"draft", "agent_draft", "human_written", "human_approved"}
)
_PROOF_DECLARATION_KINDS = frozenset({"theorem", "lemma"})


def _string_list(
    value: object,
    *,
    field: str,
    required: bool = False,
) -> tuple[tuple[str, ...], tuple[str, ...]]:
    if not isinstance(value, list) or any(
        not isinstance(item, str) or not item.strip() for item in value
    ):
        return (), (f"`{field}` must be a string list",)
    normalized = tuple(item.strip() for item in value)
    if required and not normalized:
        return (), (f"`{field}` must be a nonempty string list",)
    if len(normalized) != len(set(normalized)):
        return normalized, (f"`{field}` contains duplicate names",)
    return normalized, ()


def _configured_path(
    repository_root: Path,
    value: object,
) -> Path | None:
    if not isinstance(value, str) or not value.strip():
        return None
    candidate = Path(value.strip())
    if not candidate.is_absolute():
        candidate = repository_root / candidate
    try:
        return candidate.resolve()
    except (OSError, RuntimeError):
        return None


def source_structure_errors(
    *,
    paper_id: str,
    folder: Path,
    review_surface: Mapping[str, object],
    surface: object,
    declaration_index: dict[str, list[LeanDeclaration]],
) -> tuple[str, ...]:
    """Validate Lean-emitted claim atoms and the support-declaration inventory."""

    targets = getattr(surface, "semantic_targets", None)
    claims = getattr(surface, "review_claim_manifests", None)
    declarations = getattr(surface, "source_declarations", None)
    if not all(
        isinstance(value, Mapping) for value in (targets, claims, declarations)
    ):
        return (f"`{paper_id}` v11 Lean graph omits its structural claim surface",)

    errors: list[str] = []
    if set(targets) != set(claims):
        errors.append(
            f"`{paper_id}` v11 Lean graph does not have one claim-atom manifest "
            "for every source-facing semantic target"
        )
    for specification in sorted(set(targets) & set(claims)):
        target = targets[specification]
        claim = claims[specification]
        if not isinstance(target, Mapping) or not isinstance(claim, Mapping):
            errors.append(
                f"`{paper_id}` source-facing target `{specification}` has an "
                "invalid Lean-emitted claim-atom manifest"
            )
            continue
        raw_atoms = claim.get("claim_atoms")
        atoms = (
            [dict(atom) for atom in raw_atoms if isinstance(atom, Mapping)]
            if isinstance(raw_atoms, list)
            else []
        )
        roles = [str(atom.get("role") or "") for atom in atoms]
        semantic_atoms = [
            {key: value for key, value in atom.items() if key != "display"}
            for atom in atoms
        ]
        atoms_sha256 = hashlib.sha256(
            json.dumps(
                {"schema": 1, "atoms": semantic_atoms},
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        ).hexdigest()
        malformed = bool(
            not atoms
            or not isinstance(raw_atoms, list)
            or len(atoms) != len(raw_atoms)
            or roles[-1:] != ["conclusion"]
            or roles.count("conclusion") != 1
            or any(
                role not in {"parameter", "assumption", "conclusion"}
                for role in roles
            )
            or atoms_sha256
            != str(claim.get("claim_atoms_sha256") or "").strip().lower()
            or claim.get("claim_atoms_sha256")
            != target.get("review_claim_atoms_sha256")
            or claim.get("manifest_sha256")
            != target.get("review_claim_manifest_sha256")
            or claim.get("claim_atoms") != target.get("review_claim_atoms")
        )
        if malformed:
            errors.append(
                f"`{paper_id}` source-facing target `{specification}` has an "
                "invalid Lean-emitted claim-atom manifest"
            )

    assumption_value = review_surface.get("assumption_source_file")
    assumption_path = _configured_path(
        folder.parents[1],
        assumption_value,
    )
    if assumption_path is None:
        assumption_path = (folder / "Assumptions.lean").resolve()
    raw_assumption_names = review_surface.get("assumption_names", [])
    assumption_names = (
        tuple(raw_assumption_names)
        if isinstance(raw_assumption_names, list)
        and all(isinstance(name, str) and name.strip() for name in raw_assumption_names)
        else ()
    )
    for configured in assumption_names:
        resolved = resolve_declaration_name(declaration_index, configured.strip())
        if len(resolved) != 1 or resolved[0].path.resolve() != assumption_path:
            errors.append(
                f"`{paper_id}` configured assumption `{configured}` does not "
                "resolve uniquely in the exact Assumptions.lean surface"
            )
    configured_support_names: set[str] = set()
    for key in (
        "assumption_names",
        "auxiliary_names",
        "quarantined_auxiliary_names",
    ):
        values = review_surface.get(key)
        if isinstance(values, list):
            configured_support_names.update(
                str(value).strip()
                for value in values
                if isinstance(value, str) and str(value).strip()
            )
    unconfigured: list[str] = []
    for declaration, record in declarations.items():
        if not isinstance(record, Mapping):
            continue
        source_path = record.get("source_path")
        if not (
            isinstance(source_path, Path)
            and source_path.resolve() == assumption_path
        ):
            continue
        qualified = str(declaration).strip()
        short = qualified.rsplit(".", 1)[-1]
        matching = {
            configured
            for configured in configured_support_names
            if configured in {qualified, short}
            or qualified == f"{paper_id}.{configured}"
        }
        if len(matching) != 1:
            unconfigured.append(qualified)
    if unconfigured:
        errors.append(
            f"`{paper_id}` Lean declaration inventory found "
            f"{len(unconfigured)} unconfigured Assumptions.lean support "
            "declaration(s): "
            + ", ".join(sorted(unconfigured)[:8])
            + ("; ..." if len(unconfigured) > 8 else "")
        )
    return tuple(errors)


def partition_review_routes(
    *,
    paper_id: str,
    review_names: Sequence[str],
    route_set: EvidenceRouteSet,
    declarations: dict[str, list[LeanDeclaration]],
) -> ReviewRoutePartition:
    """Partition selected source claims using only typed route authority."""

    try:
        results_by_spec = route_set.result_route_by_specification()
    except ObligationRouteError as exc:
        return ReviewRoutePartition(
            result_routes=(),
            direct_routes=(),
            errors=(f"`{paper_id}` retained v11 transaction has invalid typed routes: {exc}",),
        )
    direct_declarations = set(route_set.source_semantic_declarations())
    result_routes: list[ResultReviewRoute] = []
    direct_routes: list[DirectReviewRoute] = []
    errors: list[str] = []
    for configured_name in sorted(review_names):
        resolved = resolve_declaration_name(declarations, configured_name)
        if len(resolved) != 1:
            errors.append(
                f"`{paper_id}` v11 review row `{configured_name}` does not resolve uniquely"
            )
            continue
        qualified = typed_qualified_declaration_identity(resolved[0])
        result_route = results_by_spec.get(qualified)
        is_direct = qualified in direct_declarations
        if result_route is not None and is_direct:
            errors.append(
                f"`{paper_id}` v11 review row `{configured_name}` is ambiguously "
                "routed as both a result and a direct semantic declaration"
            )
        elif result_route is not None:
            result_routes.append(
                ResultReviewRoute(configured_name, qualified, result_route)
            )
        elif is_direct:
            direct_routes.append(DirectReviewRoute(configured_name, qualified))
        else:
            errors.append(
                f"`{paper_id}` v11 review row `{configured_name}` has no typed "
                "result or direct-declaration route"
            )
    selected_result_specs = {
        route.qualified_specification for route in result_routes
    }
    expected_result_specs = set(results_by_spec)
    missing_result_specs = sorted(expected_result_specs - selected_result_specs)
    if missing_result_specs:
        errors.append(
            f"`{paper_id}` review_surface omits typed source-result Spec(s): "
            + ", ".join(missing_result_specs)
        )
    return ReviewRoutePartition(
        result_routes=tuple(result_routes),
        direct_routes=tuple(direct_routes),
        errors=tuple(errors),
    )


def _contract_candidates(
    contract_rows: Mapping[object, object],
    specification: str,
    evidence: str,
) -> list[Mapping[str, object]]:
    candidates: list[Mapping[str, object]] = []
    for key, row in contract_rows.items():
        if not (
            isinstance(key, tuple)
            and len(key) == 3
            and isinstance(row, Mapping)
        ):
            continue
        spec_name, evidence_name, _mode = key
        if (spec_name, evidence_name) == (specification, evidence):
            candidates.append(row)
    return candidates


def direct_proof_pair_errors(
    *,
    paper_id: str,
    partition: ReviewRoutePartition,
    declarations: dict[str, list[LeanDeclaration]],
    source_path: Path,
    proof_declaration_kinds: frozenset[str],
    contract_rows: object,
) -> tuple[str, ...]:
    """Validate exact typed Spec/proof endpoints against the retained Lean graph.

    The typed source route is the single proof-pair authority.  A second
    status-file proof map or a configured proof-module path would duplicate
    that route and make a mathematically unchanged proof sensitive to file
    organization.  Lean must still expose one theorem/lemma endpoint and one
    matching semantic contract for every result row.
    """

    if partition.errors:
        return partition.errors
    result_routes = partition.result_map()
    direct_routes = partition.direct_map()
    errors: list[str] = []
    requested: dict[str, tuple[str, str]] = {}
    for spec_name, (qualified_spec, typed_route) in sorted(result_routes.items()):
        specs = resolve_declaration_name(declarations, spec_name)
        qualified_proof = typed_route.evidence_declaration
        proofs = resolve_declaration_name(declarations, qualified_proof)
        if len(specs) != 1:
            errors.append(
                f"`{paper_id}` v11 Spec `{spec_name}` does not resolve uniquely"
            )
            continue
        if len(proofs) != 1:
            errors.append(
                f"`{paper_id}` v11 Spec `{spec_name}` has no unique typed proof endpoint"
            )
            continue
        if specs[0].path.resolve() != source_path.resolve():
            errors.append(
                f"`{paper_id}` v11 Spec `{spec_name}` is outside PaperInterface.lean"
            )
            continue
        if proofs[0].kind not in proof_declaration_kinds:
            errors.append(
                f"`{paper_id}` v11 typed proof endpoint `{qualified_proof}` is not "
                "a theorem/lemma in the Lean-owned import closure"
            )
            continue
        resolved_proof = typed_qualified_declaration_identity(proofs[0])
        if resolved_proof != qualified_proof:
            errors.append(
                f"`{paper_id}` v11 typed proof endpoint `{qualified_proof}` resolves "
                "to a different Lean declaration"
            )
            continue
        requested[spec_name] = (qualified_spec, resolved_proof)
    if errors:
        return tuple(errors)
    if set(requested) != set(result_routes):
        return (f"`{paper_id}` v11 proof-pair inventory is incomplete",)
    if not isinstance(contract_rows, Mapping):
        return (
            f"`{paper_id}` retained v11 Lean graph has no typed-contract section",
        )
    for spec_name, route in sorted(requested.items()):
        candidates = _contract_candidates(contract_rows, *route)
        if len(candidates) != 1 or candidates[0].get("matches") is not True:
            errors.append(
                f"`{paper_id}` Lean did not establish the typed semantic relation "
                f"from `{spec_name}` to `{route[1]}`"
            )
    for configured_name, qualified in sorted(direct_routes.items()):
        resolved = resolve_declaration_name(declarations, configured_name)
        if (
            len(resolved) != 1
            or typed_qualified_declaration_identity(resolved[0]) != qualified
            or resolved[0].path.resolve() != source_path.resolve()
        ):
            errors.append(
                f"`{paper_id}` direct semantic declaration `{configured_name}` "
                "is outside PaperInterface.lean"
            )
    return tuple(errors)


def direct_axiom_closure_errors(
    *,
    paper_id: str,
    include_names: Sequence[str],
    partition: ReviewRoutePartition,
    declarations: dict[str, list[LeanDeclaration]],
    declaration_inventory: object,
    contract_rows: object,
    approved_axioms: frozenset[str],
) -> tuple[str, ...]:
    """Validate proof debt from the retained Lean inventory and contracts."""

    if partition.errors:
        return partition.errors
    result_routes = partition.result_map()
    direct_routes = partition.direct_map()
    raw_nodes = (
        declaration_inventory.get("declarations")
        if isinstance(declaration_inventory, Mapping)
        else None
    )
    if not isinstance(raw_nodes, list) or not isinstance(contract_rows, Mapping):
        return (
            f"`{paper_id}` retained v11 Lean graph has no axiom-closure surface",
        )
    nodes = {
        str(row.get("declaration") or "").strip(): row
        for row in raw_nodes
        if isinstance(row, Mapping)
    }
    errors: list[str] = []

    def check_row(label: str, row: Mapping[str, object], prefix: str) -> None:
        checked_field = prefix + "axiom_closure_checked"
        axioms_field = prefix + "axiom_closure"
        unsafe_field = prefix + "is_unsafe"
        sorry_field = prefix + "value_has_sorry"
        axioms = row.get(axioms_field)
        if row.get(checked_field) is not True or not isinstance(axioms, list):
            errors.append(
                f"`{paper_id}` retained Lean graph did not check axiom closure "
                f"for `{label}`"
            )
            return
        if row.get(unsafe_field) is True or row.get(sorry_field) is True:
            errors.append(
                f"`{paper_id}` Lean declaration `{label}` is unsafe or contains `sorry`"
            )
        unapproved = sorted(
            str(name) for name in axioms if str(name) not in approved_axioms
        )
        if unapproved:
            errors.append(
                f"`{paper_id}` Lean declaration `{label}` depends on unapproved "
                "axiom(s): " + ", ".join(unapproved)
            )

    for configured_name in include_names:
        resolved = resolve_declaration_name(declarations, configured_name)
        if len(resolved) != 1:
            errors.append(
                f"`{paper_id}` v11 review row `{configured_name}` does not resolve "
                "uniquely for axiom closure"
            )
            continue
        specification = typed_qualified_declaration_identity(resolved[0])
        node = nodes.get(specification)
        if not isinstance(node, Mapping):
            errors.append(
                f"`{paper_id}` retained Lean graph omits review row `{configured_name}`"
            )
            continue
        check_row(configured_name, node, "")
        if configured_name in direct_routes:
            continue
        typed_route_row = result_routes.get(configured_name)
        if typed_route_row is None:
            errors.append(
                f"`{paper_id}` retained Lean graph has no typed route for "
                f"`{configured_name}`"
            )
            continue
        _qualified_spec, typed_route = typed_route_row
        proof_name = typed_route.evidence_declaration
        resolved_proof = resolve_declaration_name(declarations, proof_name)
        if len(resolved_proof) != 1:
            errors.append(
                f"`{paper_id}` v11 proof endpoint `{proof_name}` does not resolve "
                "uniquely for axiom closure"
            )
            continue
        proof = typed_qualified_declaration_identity(resolved_proof[0])
        pairs = _contract_candidates(contract_rows, specification, proof)
        if len(pairs) != 1:
            errors.append(
                f"`{paper_id}` retained Lean graph omits typed route "
                f"`{configured_name}` -> `{proof_name}`"
            )
            continue
        check_row(proof_name, pairs[0], "evidence_")
    return tuple(errors)


def evaluate_current_v11_primary_gate(
    *,
    repository_root: Path,
    paper_id: str,
    folder: Path,
    status_payload: Mapping[str, object],
    source_map: Mapping[str, object],
    surface: object,
    semantic_review_current: bool,
    semantic_review_error: str = "",
    approved_axioms: frozenset[str] = frozenset(),
) -> CurrentV11PrimaryGateResult:
    """Evaluate the parser-free current semantic/proof/axiom conjunction.

    This function consumes one retained Lean graph and the exact status/map
    snapshots that selected it.  It never reads ambient files and it cannot
    fall back to a historical source-record lane.  Evidence publication and
    the final mutation check remain later, distinct strict stages.
    """

    root = repository_root.resolve()
    paper_folder = folder.resolve()
    configuration_errors: list[str] = []
    empty_partition = ReviewRoutePartition((), (), ())
    if paper_folder != (root / "papers" / paper_id).resolve():
        return CurrentV11PrimaryGateResult(
            declarations={},
            partition=empty_partition,
            configuration_errors=(
                f"`{paper_id}` current closeout folder is outside the canonical papers root",
            ),
        )
    if status_payload.get("id") != paper_id:
        configuration_errors.append(
            f"`{paper_id}` exact status id does not match its paper folder"
        )
    for field in ("title", "source_version", "build_target", "review_entrypoint"):
        value = status_payload.get(field)
        if not isinstance(value, str) or not value.strip():
            configuration_errors.append(
                f"`{paper_id}` exact status has no nonempty `{field}`"
            )
    status = str(status_payload.get("status") or "").strip().lower()
    if status not in _CLOSEOUT_STATUSES:
        configuration_errors.append(
            f"`{paper_id}` status does not select a current closeout lane"
        )
    summary_review = status_payload.get("human_summary_review")
    if summary_review is not None:
        if not isinstance(summary_review, Mapping):
            configuration_errors.append(
                f"`{paper_id}.human_summary_review` must be an object"
            )
        else:
            review_status = summary_review.get("status")
            if review_status not in _HUMAN_SUMMARY_REVIEW_VALUES:
                configuration_errors.append(
                    f"`{paper_id}.human_summary_review.status` is invalid"
                )
            if review_status == "human_approved" and not isinstance(
                status_payload.get("human_summary"), str
            ):
                configuration_errors.append(
                    f"`{paper_id}` has human-approved summary metadata but no "
                    "`human_summary` string"
                )

    interface = status_payload.get("paper_interface")
    review_surface = status_payload.get("review_surface")
    if not isinstance(interface, Mapping):
        configuration_errors.append(
            f"`{paper_id}.paper_interface` must be an object"
        )
        interface = {}
    if not isinstance(review_surface, Mapping):
        configuration_errors.append(
            f"`{paper_id}.review_surface` must be an object"
        )
        review_surface = {}

    interface_path = (paper_folder / "PaperInterface.lean").resolve()
    configured_interface = _configured_path(root, interface.get("path"))
    if configured_interface != interface_path:
        configuration_errors.append(
            f"`{paper_id}.paper_interface.path` must name the canonical PaperInterface.lean"
        )
    source_path = _configured_path(root, review_surface.get("source_file"))
    if source_path != interface_path:
        configuration_errors.append(
            f"`{paper_id}.review_surface.source_file` must name PaperInterface.lean"
        )
    if isinstance(interface.get("audit_surface_path"), str) and str(
        interface.get("audit_surface_path")
    ).strip():
        configuration_errors.append(
            f"`{paper_id}.paper_interface.audit_surface_path` is obsolete"
        )

    assumption_names, assumption_errors = _string_list(
        review_surface.get("assumption_names", []),
        field=f"{paper_id}.review_surface.assumption_names",
    )
    auxiliary_names, auxiliary_errors = _string_list(
        review_surface.get("auxiliary_names", []),
        field=f"{paper_id}.review_surface.auxiliary_names",
    )
    quarantined_names, quarantine_errors = _string_list(
        review_surface.get("quarantined_auxiliary_names", []),
        field=f"{paper_id}.review_surface.quarantined_auxiliary_names",
    )
    boundary_names, boundary_errors = _string_list(
        review_surface.get("proof_boundary_names", []),
        field=f"{paper_id}.review_surface.proof_boundary_names",
    )
    configuration_errors.extend(
        assumption_errors
        + auxiliary_errors
        + quarantine_errors
        + boundary_errors
    )
    assumption_set = set(assumption_names)
    auxiliary_set = set(auxiliary_names)
    quarantine_set = set(quarantined_names)
    boundary_set = set(boundary_names)
    missing_boundaries = sorted(boundary_set - assumption_set)
    if missing_boundaries:
        configuration_errors.append(
            f"`{paper_id}` proof boundaries are not source assumptions: "
            + ", ".join(missing_boundaries)
        )
    missing_quarantine = sorted(quarantine_set - auxiliary_set)
    if missing_quarantine:
        configuration_errors.append(
            f"`{paper_id}` quarantined auxiliaries are not auxiliary names: "
            + ", ".join(missing_quarantine)
        )
    overlap = sorted(
        assumption_set.intersection(auxiliary_set)
    )
    if overlap:
        configuration_errors.append(
            f"`{paper_id}` assumption and auxiliary names overlap: "
            + ", ".join(overlap)
        )
    assumption_policy = str(
        review_surface.get("assumption_policy") or ""
    ).strip().lower()
    if assumption_policy and assumption_policy not in _ASSUMPTION_POLICY_VALUES:
        configuration_errors.append(
            f"`{paper_id}.review_surface.assumption_policy` is invalid"
        )

    inventory = getattr(surface, "declaration_inventory", None)
    module_sources = getattr(surface, "module_sources", None)
    declarations = (
        declaration_index_from_inventory(inventory, module_sources)
        if isinstance(module_sources, Mapping)
        else {}
    )
    support_declarations = (
        declaration_index_from_inventory(
            inventory,
            module_sources,
            source_presented_only=False,
            paper_owned_only=False,
        )
        if isinstance(module_sources, Mapping)
        else {}
    )
    if not declarations:
        configuration_errors.append(
            f"`{paper_id}` retained v11 Lean graph has no usable paper declaration inventory"
        )
    try:
        route_set = EvidenceRouteSet.from_source_map(source_map)
    except (ObligationRouteError, TypeError, ValueError) as exc:
        configuration_errors.append(
            f"`{paper_id}` retained v11 transaction has invalid typed routes: {exc}"
        )
        partition = empty_partition
    else:
        # The schema-2 source map is the only acceptance authority for the
        # result review surface.  Legacy ``status.json.review_surface`` names
        # describe presentation and older workflow metadata; using them here
        # would let a stale dashboard projection select, omit, or invalidate
        # current source claims.  Every typed result Spec remains mandatory,
        # and its typed proof endpoint is checked below from the retained Lean
        # graph, irrespective of either declaration's file location.
        include_names = route_set.result_specifications()
        partition = partition_review_routes(
            paper_id=paper_id,
            review_names=include_names,
            route_set=route_set,
            declarations=declarations,
        )
    semantic_errors = (
        ()
        if semantic_review_current
        else (
            f"`{paper_id}` selected v11 semantic review is not current: "
            + (semantic_review_error.strip() or "semantic review did not pass"),
        )
    )
    contract_rows = getattr(surface, "semantic_contracts", None)
    proof_errors = direct_proof_pair_errors(
        paper_id=paper_id,
        partition=partition,
        declarations=declarations,
        source_path=interface_path,
        proof_declaration_kinds=_PROOF_DECLARATION_KINDS,
        contract_rows=contract_rows,
    )
    accepted_axioms = set(approved_axioms)
    for name in boundary_set:
        accepted_axioms.add(name)
        accepted_axioms.add(f"{paper_id}.{name}")
    axiom_errors = direct_axiom_closure_errors(
        paper_id=paper_id,
        include_names=include_names,
        partition=partition,
        declarations=declarations,
        declaration_inventory=inventory,
        contract_rows=contract_rows,
        approved_axioms=frozenset(accepted_axioms),
    )
    structure_errors = source_structure_errors(
        paper_id=paper_id,
        folder=paper_folder,
        review_surface=review_surface,
        surface=surface,
        declaration_index=support_declarations,
    )
    return CurrentV11PrimaryGateResult(
        declarations=declarations,
        partition=partition,
        configuration_errors=tuple(configuration_errors),
        semantic_errors=semantic_errors,
        proof_errors=proof_errors,
        axiom_errors=axiom_errors,
        structure_errors=structure_errors,
    )
