#!/usr/bin/env python3
"""Materialize authenticated closeout facts into the obligation leaf store.

This module is a protocol-neutral deterministic assembler. Callers must first
authenticate their own current or historical authority, then provide that
authority and its assurance contract here. Materialization neither discovers
authority nor accepts a paper; only the later accepted obligation graph can do
that.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Any, Callable, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.check_formalization_engine_revision import (
    validate_runtime_engine_registration,
    validated_runtime_engine_revision_ledger,
)
from scripts.direct_semantic_review_binding import (
    LEAN_TARGET_PROTOCOL,
    normalized_direct_screening_ledger,
)
from scripts.lean_signature_manifest import (
    RepositoryBuildInputSnapshotProvider,
    semantic_review_claim_surfaces_from_inventory,
    semantic_signature_sha256s_from_inventory,
)
from scripts.lean_review_surface import (
    LeanSemanticReviewDisplaySurface,
    lean_owned_semantic_review_display_surface_from_inventory,
)
from scripts.closeout_content_store import content_sha256
from scripts.obligation_closeout_state import verify_current_stored_paper_obligations
from scripts.obligation_evidence_graph import ObligationEvidenceLeaf
from scripts.obligation_evidence_issuance import (
    STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256,
    ObligationEvidenceIssuance,
)
from scripts.obligation_evidence_projection import (
    ObligationEvidenceProjectionError,
    project_direct_v11_leaves_from_validated_inputs,
    project_focused_build_leaf_from_validated_inputs,
    project_semantic_prerequisite_leaves_from_validated_inputs,
    project_source_route_leaves_from_validated_inputs,
    validated_direct_v11_claims,
)
from scripts.obligation_evidence_store import store_paper_obligation_bundle
from scripts.obligation_paper_index import assemble_complete_paper_obligation_graph
from scripts.obligation_preflight import structural_obligation_preflight
from scripts.obligation_routes import EvidenceRouteSet, ObligationRouteError
from scripts.semantic_prerequisite_projection import (
    LIBRARY_SEMANTIC_TARGET_PROTOCOL,
    PAPER_PREREQUISITE_PROMPT_VERSION,
    PAPER_PREREQUISITE_TARGET_PROTOCOL,
    REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,
    normalized_semantic_prerequisite_ledger,
    selected_library_semantic_prerequisite_targets,
    selected_paper_semantic_prerequisite_targets,
)
from scripts.current_closeout.realization import (
    graph_native_realization_receipts_from_inventory,
)
from scripts.strict_closeout_authority import (
    StrictCloseoutAuthority,
    validate_strict_closeout_authority,
)


ProgressCallback = Callable[[Mapping[str, Any]], None]


class ObligationCloseoutMaterializationError(ValueError):
    """Authenticated closeout facts cannot be materialized safely."""


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


def _sha256(value: object, field: str) -> str:
    text = str(value or "").strip().lower()
    if not SHA256_RE.fullmatch(text):
        raise ObligationCloseoutMaterializationError(f"{field} is not SHA-256")
    return text


@dataclass(frozen=True)
class ObligationCloseoutMaterializationResult:
    paper: str
    operation: str
    issuance_authority_sha256: str
    engine_tree_sha256: str
    graph_sha256: str
    paper_index_sha256: str
    bundle_path: str
    source_route_count: int
    direct_claim_count: int
    semantic_prerequisite_count: int
    reused_prerequisite_leaf_count: int
    materialized_prerequisite_leaf_count: int
    leaf_count: int
    elapsed_seconds: float

    def projection(self) -> dict[str, Any]:
        return {
            "schema": 1,
            "acceptance_credential": False,
            "operation": self.operation,
            "paper": self.paper,
            "issuance_authority_sha256": self.issuance_authority_sha256,
            "engine_tree_sha256": self.engine_tree_sha256,
            "graph_sha256": self.graph_sha256,
            "paper_index_sha256": self.paper_index_sha256,
            "bundle_path": self.bundle_path,
            "source_route_count": self.source_route_count,
            "direct_claim_count": self.direct_claim_count,
            "semantic_prerequisite_count": self.semantic_prerequisite_count,
            "reused_prerequisite_leaf_count": self.reused_prerequisite_leaf_count,
            "materialized_prerequisite_leaf_count": (
                self.materialized_prerequisite_leaf_count
            ),
            "leaf_count": self.leaf_count,
            "elapsed_seconds": self.elapsed_seconds,
        }


@dataclass(frozen=True)
class _AuthenticatedSemanticReviewMaterial:
    """Current Lean denominator plus name-free reviewer-ledger bindings."""

    signatures: Mapping[str, str]
    review_surface: LeanSemanticReviewDisplaySurface
    direct_screening: Mapping[str, Any]
    paper_prerequisites: Mapping[str, Any]
    library_prerequisites: Mapping[str, Any]


def _json(path: Path, label: str) -> Mapping[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ObligationCloseoutMaterializationError(f"{label} is unreadable: {exc}") from exc
    if not isinstance(value, Mapping):
        raise ObligationCloseoutMaterializationError(f"{label} is not an object")
    return value


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError as exc:
        raise ObligationCloseoutMaterializationError(f"could not hash {path}: {exc}") from exc
    return digest.hexdigest()


def _input_snapshot(paths: tuple[Path, ...]) -> Mapping[str, str]:
    return {str(path.resolve()): _sha256_file(path) for path in paths}


def _add_leaf(
    leaves: dict[str, ObligationEvidenceLeaf], leaf: ObligationEvidenceLeaf
) -> None:
    prior = leaves.get(leaf.leaf_sha256)
    if prior is not None and prior != leaf:
        raise ObligationCloseoutMaterializationError(
            f"semantic leaf identity collision: {leaf.leaf_sha256}"
        )
    leaves[leaf.leaf_sha256] = leaf


def _add_issuance(
    issuances: dict[str, ObligationEvidenceIssuance],
    issuance: ObligationEvidenceIssuance,
) -> None:
    prior = issuances.get(issuance.issuance_sha256)
    if prior is not None and prior != issuance:
        raise ObligationCloseoutMaterializationError(
            f"issuance identity collision: {issuance.issuance_sha256}"
        )
    issuances[issuance.issuance_sha256] = issuance


def _progress(callback: ProgressCallback | None, stage: str, **details: Any) -> None:
    if callback is not None:
        callback({"stage": stage, **details})


def _stable_json_sha256(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def _focused_build_target_leaf_sha256s(
    navigation: Mapping[str, Mapping[str, Any]],
) -> tuple[str, ...]:
    """Return the semantic endpoint frontier, not source-row occurrences."""

    return tuple(
        sorted(
            {
                str(route["proof_endpoint_leaf_sha256"])
                for route in navigation.values()
            }
        )
    )


def _authenticated_current_semantic_signatures(
    *,
    paper: str,
    carrier: Mapping[str, Any],
    expected_carrier_sha256: str,
    source_map: Mapping[str, Any],
    screening: Mapping[str, Any],
    paper_prerequisites: Mapping[str, Any],
    library_review: Mapping[str, Any],
    route_set: EvidenceRouteSet,
    paper_dir: Path,
) -> _AuthenticatedSemanticReviewMaterial:
    """Bind one frozen current Lean graph to every reviewed target.

    The LLM verdict remains bound to the exact display stored in its ledger.
    This projection adds the renderer-independent Lean signature produced in
    the same authenticated closeout transaction; it makes no new judgment.
    """

    expected_digest = _sha256(expected_carrier_sha256, "Lean graph carrier")
    if content_sha256(carrier) != expected_digest:
        raise ObligationCloseoutMaterializationError(
            "authenticated Lean graph differs from its closeout-plan object"
        )
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
        key: value for key, value in carrier.items()
        if key != "receipt_integrity_sha256"
    }
    inventory = carrier.get("inventory")
    if (
        set(carrier) != required
        or carrier.get("schema") != 3
        or carrier.get("acceptance_credential") is not False
        or carrier.get("operational_scheduling_only") is not True
        or carrier.get("paper") != paper
        or not isinstance(inventory, Mapping)
        or carrier.get("inventory_sha256") != _stable_json_sha256(inventory)
        or carrier.get("receipt_integrity_sha256")
        != _stable_json_sha256(material)
    ):
        raise ObligationCloseoutMaterializationError(
            "authenticated Lean graph carrier is malformed"
        )
    direct_names = {
        route.semantic_review_declaration for route in route_set.result_routes()
    }
    try:
        review_surface = lean_owned_semantic_review_display_surface_from_inventory(
            inventory,
            expected_specifications=direct_names,
        )
        claim_surfaces = semantic_review_claim_surfaces_from_inventory(
            inventory,
            expected_declarations=direct_names,
        )
    except ValueError as exc:
        raise ObligationCloseoutMaterializationError(
            "authenticated Lean graph review surface is malformed"
        ) from exc
    direct_targets = {
        name: {
            **dict(review_surface.specifications[name]),
            "lean_target_protocol": LEAN_TARGET_PROTOCOL,
            "review_claim_manifest_sha256": claim_surfaces[name][
                "manifest_sha256"
            ],
            "review_claim_atoms_sha256": claim_surfaces[name][
                "claim_atoms_sha256"
            ],
            "review_claim_atoms": claim_surfaces[name]["claim_atoms"],
        }
        for name in sorted(direct_names)
    }
    try:
        normalized_screening = normalized_direct_screening_ledger(
            paper_dir=paper_dir,
            source_map=source_map,
            screening=screening,
            route_set=route_set,
            semantic_targets=direct_targets,
            repository_root=paper_dir.parents[1],
        )
        _source_artifact, claims = validated_direct_v11_claims(
            source_map=source_map,
            v11_screening=normalized_screening,
            route_set=route_set,
        )
    except (ObligationEvidenceProjectionError, ValueError) as exc:
        raise ObligationCloseoutMaterializationError(str(exc)) from exc
    if {claim.review_name for claim in claims} != direct_names:
        raise ObligationCloseoutMaterializationError(
            "normalized direct screening differs from the Lean review surface"
        )
    all_paper_names = set(review_surface.paper_declarations)
    all_library_names = set(review_surface.library_declarations)
    if all_paper_names & all_library_names:
        raise ObligationCloseoutMaterializationError(
            "authenticated Lean graph assigns one prerequisite to both roles"
        )
    # The authenticated strict semantic stage has already compared each exact
    # display to its reviewer-owned ledger.  Repeating that comparison here
    # would make this deterministic graph assembler a second acceptance gate
    # and would bind future currentness to renderer bytes.  This projection
    # records the reviewed display digest from the ledger and the stable Lean
    # identity from the same frozen graph transaction.
    try:
        selected_paper_targets = selected_paper_semantic_prerequisite_targets(
            source_map,
            review_surface.paper_declarations,
        )
        selected_library_names = set(
            selected_library_semantic_prerequisite_targets(
                source_map,
                review_surface.library_declarations,
            )
        )
        expected_names = (
            direct_names
            | set(selected_paper_targets)
            | selected_library_names
        )
        all_signatures = semantic_signature_sha256s_from_inventory(inventory)
        missing_signatures = sorted(expected_names - set(all_signatures))
        if missing_signatures:
            raise ValueError(
                "Lean graph omits selected semantic signature(s): "
                + ", ".join(missing_signatures)
            )
        signatures = {
            name: all_signatures[name]
            for name in sorted(expected_names)
        }
    except ValueError as exc:
        raise ObligationCloseoutMaterializationError(
            "authenticated Lean semantic identities differ from review surface"
        ) from exc
    paper_targets = {
        name: {
            **dict(target),
            "elaborated_signature_sha256": signatures[name],
        }
        for name, target in selected_paper_targets.items()
    }
    library_targets = {
        name: {
            **dict(target),
            "elaborated_signature_sha256": signatures[name],
        }
        for name, target in review_surface.library_declarations.items()
        if name in selected_library_names
    }
    try:
        normalized_paper = normalized_semantic_prerequisite_ledger(
            paper_dir=paper_dir,
            repository_root=paper_dir.parents[1],
            source_map=source_map,
            ledger=paper_prerequisites,
            semantic_targets=paper_targets,
            label="paper prerequisite ledger",
            declaration_field="paper_declaration",
            prompt_version=PAPER_PREREQUISITE_PROMPT_VERSION,
            target_protocol=PAPER_PREREQUISITE_TARGET_PROTOCOL,
            row_target_protocol_field="paper_semantic_target_protocol",
            row_target_sha256_field="paper_semantic_target_sha256",
            row_code_sha256_field="paper_declaration_sha256",
        )
        normalized_library = normalized_semantic_prerequisite_ledger(
            paper_dir=paper_dir,
            repository_root=paper_dir.parents[1],
            source_map=source_map,
            ledger=library_review,
            semantic_targets=library_targets,
            label="library prerequisite ledger",
            declaration_field="library_declaration",
            prompt_version=REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,
            target_protocol=LIBRARY_SEMANTIC_TARGET_PROTOCOL,
            row_target_protocol_field="library_semantic_target_protocol",
            row_target_sha256_field="library_semantic_target_sha256",
            row_code_sha256_field="library_definition_sha256",
        )
    except ValueError as exc:
        raise ObligationCloseoutMaterializationError(str(exc)) from exc
    return _AuthenticatedSemanticReviewMaterial(
        signatures=MappingProxyType(signatures),
        review_surface=review_surface,
        direct_screening=normalized_screening,
        paper_prerequisites=normalized_paper,
        library_prerequisites=normalized_library,
    )


def materialize_authenticated_closeout_to_obligation_bundle(
    root: Path,
    paper: str,
    *,
    operation: str,
    issuance_authority_sha256: str,
    issuance_assurance_contract_sha256: str,
    expected_engine_tree_sha256: str,
    watched_authority_paths: tuple[Path, ...] = (),
    progress_callback: ProgressCallback | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    finalize_build_input_provider: bool = True,
    authenticated_lean_import_closure_receipt: Mapping[str, Any] | None = None,
    authenticated_v11_lean_review_graph: Mapping[str, Any] | None = None,
    authenticated_v11_lean_review_graph_sha256: str | None = None,
) -> ObligationCloseoutMaterializationResult:
    """Project one authenticated transaction through a shared strict core."""

    started = time.perf_counter()
    root = root.resolve()
    paper_dir = root / "papers" / paper
    if not paper_dir.is_dir():
        raise ObligationCloseoutMaterializationError(f"paper folder does not exist: {paper}")
    audit_dir = paper_dir / "audit"
    source_map_path = audit_dir / "paper_statement_map.json"
    screening_path = audit_dir / "v11_raw_source_spec_screening.json"
    manifest_path = audit_dir / "lean_signature_manifest_cache_authority.json"
    paper_prerequisite_path = audit_dir / "paper_semantic_prerequisites.json"
    library_review_path = audit_dir / "library_semantic_review.json"
    focused_build_path = audit_dir / "FOCUSED_BUILD_RECEIPT.json"
    lean_closure_path = audit_dir / "LEAN_IMPORT_CLOSURE_RECEIPT.json"
    input_paths = (
        *watched_authority_paths,
        source_map_path,
        screening_path,
        *((manifest_path,) if authenticated_v11_lean_review_graph is None else ()),
        paper_prerequisite_path,
        library_review_path,
        focused_build_path,
        lean_closure_path,
    )

    authority_sha256 = _sha256(
        issuance_authority_sha256, "issuance authority"
    )
    assurance_contract_sha256 = _sha256(
        issuance_assurance_contract_sha256, "issuance assurance contract"
    )
    expected_engine_sha256 = _sha256(
        expected_engine_tree_sha256, "expected formalization engine"
    )
    _progress(progress_callback, "authenticate_issuance_authority")
    engine = validate_runtime_engine_registration(root)
    if engine.engine_tree_sha256 != expected_engine_sha256:
        raise ObligationCloseoutMaterializationError(
            "formalization engine differs from the authenticated transaction"
        )
    engine_ledger = validated_runtime_engine_revision_ledger(root)
    raw_revisions = (
        engine_ledger.get("revisions")
        if isinstance(engine_ledger, Mapping)
        else None
    )
    if not isinstance(raw_revisions, list):
        raise ObligationCloseoutMaterializationError(
            "registered formalization engine history is unavailable"
        )
    registered_engine_authorities = tuple(
        sorted(
            {
                str(revision.get("engine_tree_sha256") or "").strip().lower()
                for revision in raw_revisions
                if isinstance(revision, Mapping)
            }
        )
    )
    if engine.engine_tree_sha256 not in registered_engine_authorities:
        raise ObligationCloseoutMaterializationError(
            "current formalization engine is absent from registered history"
        )
    initial_inputs = _input_snapshot(input_paths)

    source_map = _json(source_map_path, "paper statement map")
    screening = _json(screening_path, "v11 semantic screening")
    manifest_authority = (
        _json(manifest_path, "Lean manifest authority")
        if authenticated_v11_lean_review_graph is None
        else {}
    )
    paper_prerequisites = _json(
        paper_prerequisite_path, "paper semantic-prerequisite review"
    )
    library_review = _json(
        library_review_path, "library semantic-prerequisite review"
    )
    focused_build = _json(focused_build_path, "focused build receipt")
    lean_closure = (
        _json(lean_closure_path, "Lean import-closure receipt")
        if authenticated_lean_import_closure_receipt is None
        else dict(authenticated_lean_import_closure_receipt)
    )

    if (authenticated_v11_lean_review_graph is None) != (
        authenticated_v11_lean_review_graph_sha256 is None
    ):
        raise ObligationCloseoutMaterializationError(
            "authenticated Lean graph and its object identity must be supplied together"
        )
    try:
        route_set = EvidenceRouteSet.from_source_map(source_map)
    except ObligationRouteError as exc:
        raise ObligationCloseoutMaterializationError(
            "paper statement map has invalid typed routes: " + str(exc)
        ) from exc
    semantic_material = (
        _authenticated_current_semantic_signatures(
            paper=paper,
            carrier=authenticated_v11_lean_review_graph,
            expected_carrier_sha256=str(
                authenticated_v11_lean_review_graph_sha256
            ),
            source_map=source_map,
            screening=screening,
            paper_prerequisites=paper_prerequisites,
            library_review=library_review,
            route_set=route_set,
            paper_dir=paper_dir,
        )
        if authenticated_v11_lean_review_graph is not None
        else None
    )
    if semantic_material is not None:
        screening = semantic_material.direct_screening
        paper_prerequisites = semantic_material.paper_prerequisites
        library_review = semantic_material.library_prerequisites
        current_semantic_signatures: Mapping[str, str] | None = (
            semantic_material.signatures
        )
    else:
        current_semantic_signatures = None

    _progress(progress_callback, "structural_preflight")
    preflight = structural_obligation_preflight(
        source_map,
        paper=paper,
        paper_prerequisites=paper_prerequisites,
        library_semantic_review=library_review,
        require_theorem_endpoints=True,
        require_source_spec_correspondence=(
            authenticated_v11_lean_review_graph is None
        ),
    )
    preflight.require_current()

    graph_native_realization_receipts: Mapping[str, Mapping[str, Any]] | None = None
    if authenticated_v11_lean_review_graph is not None:
        inventory = authenticated_v11_lean_review_graph.get("inventory")
        if not isinstance(inventory, Mapping):
            raise ObligationCloseoutMaterializationError(
                "authenticated Lean graph has no declaration inventory"
            )
        graph_native_realization_receipts, realization_errors = (
            graph_native_realization_receipts_from_inventory(
                source_map=source_map,
                inventory=inventory,
                context_input_sha256=str(
                    authenticated_v11_lean_review_graph.get("context_input_sha256")
                    or ""
                ),
                expected_paper_declarations=(
                    semantic_material.review_surface.paper_declarations
                ),
                expected_library_declarations=(
                    semantic_material.review_surface.library_declarations
                ),
            )
        )
        if realization_errors:
            raise ObligationCloseoutMaterializationError(
                "graph-native realization projection failed: "
                + "; ".join(realization_errors)
            )

    source_projection = project_source_route_leaves_from_validated_inputs(
        source_map=source_map,
        preflight=preflight,
        issuance_authority_sha256=authority_sha256,
        issuance_assurance_contract_sha256=assurance_contract_sha256,
    )

    raw_lean_closure_payload = lean_closure.get("lean_import_closure")
    if not isinstance(raw_lean_closure_payload, Mapping):
        raise ObligationCloseoutMaterializationError(
            "Lean import-closure receipt has no closure payload"
        )
    if build_input_provider is None:
        build_provider = RepositoryBuildInputSnapshotProvider(
            root,
            lean_import_closure_payload=raw_lean_closure_payload,
        )
    else:
        build_provider = build_input_provider
        if (
            build_provider.root != root
            or not build_provider.owns_exact_lean_import_closure_payload(
                raw_lean_closure_payload
            )
        ):
            raise ObligationCloseoutMaterializationError(
                "shared Lean build-input provider does not own the current closure"
            )

    assert preflight.route_set is not None
    direct_projection = project_direct_v11_leaves_from_validated_inputs(
        source_map=source_map,
        v11_screening=screening,
        route_set=preflight.route_set,
        issuance_authority_sha256=authority_sha256,
        issuance_assurance_contract_sha256=assurance_contract_sha256,
        current_semantic_signature_sha256s=current_semantic_signatures,
        graph_native_realization_receipts=graph_native_realization_receipts,
    )

    try:
        prerequisite_projection = (
            project_semantic_prerequisite_leaves_from_validated_inputs(
                source_map=source_map,
                paper_prerequisites=paper_prerequisites,
                library_semantic_review=library_review,
                manifest_authority=manifest_authority,
                issuance_authority_sha256=authority_sha256,
                issuance_assurance_contract_sha256=assurance_contract_sha256,
                current_semantic_signature_sha256s=current_semantic_signatures,
            )
        )
        prerequisite_navigation = prerequisite_projection.navigation
        prerequisite_issuances = prerequisite_projection.issuances
    except ObligationEvidenceProjectionError as exc:
        if "contain no projectable semantic prerequisites" not in str(exc):
            raise
        prerequisite_projection = None
        prerequisite_navigation = {}
        prerequisite_issuances = ()
    if prerequisite_projection is not None and (
        prerequisite_projection.unresolved_declarations
    ):
        raise ObligationCloseoutMaterializationError(
            "semantic-prerequisite projection left unresolved declarations"
        )

    target_leaf_sha256s = _focused_build_target_leaf_sha256s(
        direct_projection.navigation
    )
    build_projection = project_focused_build_leaf_from_validated_inputs(
        focused_build_receipt=focused_build,
        lean_import_closure_receipt=lean_closure,
        target_leaf_sha256s=target_leaf_sha256s,
        issuance_authority_sha256=authority_sha256,
        issuance_assurance_contract_sha256=assurance_contract_sha256,
    )

    leaves: dict[str, ObligationEvidenceLeaf] = {}
    issuances: dict[str, ObligationEvidenceIssuance] = {}
    for graph in (
        source_projection.graph,
        direct_projection.graph,
        prerequisite_projection.graph if prerequisite_projection is not None else None,
    ):
        if graph is not None:
            for leaf in graph.leaves.values():
                _add_leaf(leaves, leaf)
    for issuance_group in (
        source_projection.issuances,
        direct_projection.issuances,
        prerequisite_issuances,
    ):
        for issuance in issuance_group:
            _add_issuance(issuances, issuance)
    _add_leaf(leaves, build_projection.leaf)
    _add_issuance(issuances, build_projection.issuance)

    semantic_roles: dict[str, Mapping[str, tuple[str, ...]]] = {}
    for source_item_id, route in direct_projection.navigation.items():
        semantic_roles[source_item_id] = {
            "semantic_review": (str(route["semantic_review_leaf_sha256"]),),
            "spec": (str(route["spec_leaf_sha256"]),),
            "proof_endpoint": (str(route["proof_endpoint_leaf_sha256"]),),
            "source_lean_judgment": (str(route["judgment_leaf_sha256"]),),
            "proof_realization": (str(route["realization_leaf_sha256"]),),
        }
    prerequisite_roles = {
        declaration: {
            "source_atom": tuple(route["source_atom_leaf_sha256s"]),
            "lean_declaration": (
                str(route["lean_declaration_leaf_sha256"]),
            ),
            "source_lean_judgment": (
                str(route["judgment_leaf_sha256"]),
            ),
        }
        for declaration, route in prerequisite_navigation.items()
    }

    _progress(progress_callback, "assemble_and_publish_complete_bundle")
    graph, paper_index = assemble_complete_paper_obligation_graph(
        leaves=leaves,
        preflight=preflight,
        source_atom_leaf_sha256s_by_source_item=source_projection.navigation,
        semantic_role_leaf_sha256s_by_source_item=semantic_roles,
        build_leaf_sha256=build_projection.leaf.leaf_sha256,
        prerequisite_role_leaf_sha256s_by_declaration=prerequisite_roles,
    )
    if finalize_build_input_provider and not build_provider.finalize_unchanged():
        raise ObligationCloseoutMaterializationError(
            "Lean import-closure inputs changed during obligation migration"
        )
    pointer = store_paper_obligation_bundle(
        root,
        paper,
        paper_index,
        graph,
        issuances.values(),
        preflight=preflight,
    )

    _progress(progress_callback, "terminal_current_control_verification")
    final_engine = validate_runtime_engine_registration(root)
    if final_engine.engine_tree_sha256 != engine.engine_tree_sha256:
        raise ObligationCloseoutMaterializationError(
            "formalization engine changed during obligation migration"
        )
    if _input_snapshot(input_paths) != initial_inputs:
        raise ObligationCloseoutMaterializationError(
            "closeout evidence inputs changed during obligation migration"
        )
    verified = verify_current_stored_paper_obligations(
        root,
        paper,
        paper_index,
        graph,
        preflight=preflight,
        authenticated_authority_sha256s=(
            authority_sha256,
            *registered_engine_authorities,
        ),
    )
    if verified.paper_index_sha256 != paper_index.index_sha256:
        raise ObligationCloseoutMaterializationError(
            "terminal verification returned a different paper index"
        )

    return ObligationCloseoutMaterializationResult(
        paper=paper,
        operation=operation,
        issuance_authority_sha256=authority_sha256,
        engine_tree_sha256=engine.engine_tree_sha256,
        graph_sha256=graph.graph_sha256,
        paper_index_sha256=paper_index.index_sha256,
        bundle_path=pointer.relative_to(root).as_posix(),
        source_route_count=len(source_projection.navigation),
        direct_claim_count=len(direct_projection.navigation),
        semantic_prerequisite_count=len(prerequisite_navigation),
        reused_prerequisite_leaf_count=len(prerequisite_navigation),
        materialized_prerequisite_leaf_count=0,
        leaf_count=len(graph.leaves),
        elapsed_seconds=round(time.perf_counter() - started, 6),
    )


def materialize_passed_strict_closeout_to_obligation_bundle(
    root: Path,
    paper: str,
    *,
    authority: StrictCloseoutAuthority,
    progress_callback: ProgressCallback | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    finalize_build_input_provider: bool = True,
    authenticated_lean_import_closure_receipt: Mapping[str, Any] | None = None,
    authenticated_v11_lean_review_graph: Mapping[str, Any] | None = None,
    authenticated_v11_lean_review_graph_sha256: str | None = None,
) -> ObligationCloseoutMaterializationResult:
    """Materialize fresh closeout leaves without issuing a legacy receipt."""

    validated = validate_strict_closeout_authority(authority)
    if validated.paper != paper:
        raise ObligationCloseoutMaterializationError(
            "strict closeout authority belongs to a different paper"
        )
    if (
        authenticated_v11_lean_review_graph is None
        or authenticated_v11_lean_review_graph_sha256 is None
    ):
        raise ObligationCloseoutMaterializationError(
            "current strict closeout has no authenticated v11 Lean graph"
        )
    return materialize_authenticated_closeout_to_obligation_bundle(
        root,
        paper,
        operation="authenticated_strict_closeout_materialization",
        issuance_authority_sha256=validated.authority_sha256,
        issuance_assurance_contract_sha256=(
            STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256
        ),
        expected_engine_tree_sha256=validated.engine_tree_sha256,
        progress_callback=progress_callback,
        build_input_provider=build_input_provider,
        finalize_build_input_provider=finalize_build_input_provider,
        authenticated_lean_import_closure_receipt=(
            authenticated_lean_import_closure_receipt
        ),
        authenticated_v11_lean_review_graph=authenticated_v11_lean_review_graph,
        authenticated_v11_lean_review_graph_sha256=(
            authenticated_v11_lean_review_graph_sha256
        ),
    )
