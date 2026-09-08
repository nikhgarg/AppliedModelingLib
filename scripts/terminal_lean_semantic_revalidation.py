#!/usr/bin/env python3
"""Revalidate accepted paper semantics after nonsemantic Lean-container drift.

The historical import-closure receipt is the cheap terminal fast path. When
container bytes drift, this module revalidates the accepted graph against the
current typed source routes and asks Lean to check every Spec/proof route in
one focused build. It creates no source judgment, LLM decision, obligation
leaf, or closure receipt.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from collections.abc import Mapping
from pathlib import Path
from types import SimpleNamespace
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.current_closeout.lean_review_graph import (
    V11LeanReviewGraphProjection,
    V11LeanReviewGraphRequestPlan,
    _configured_assumption_root_names,
    acquire_validated_graph_projection,
    build_graph_request_plan,
    checkpoint_terminal_lean_graph,
    current_terminal_lean_graph_inventory,
    paper_module_names_from_sources,
)
from scripts.lean_axiom_closure import APPROVED_LEAN_AXIOMS
from scripts.lean_review_surface import LeanSemanticReviewDisplaySurface
from scripts.lean_signature_manifest import (
    RepositoryBuildInputSnapshotProvider,
    lean_inventory_review_declaration_modules,
)
from scripts.obligation_current_material import current_source_semantic_material
from scripts.obligation_evidence_graph import (
    ObligationEvidenceError,
    source_atom_semantic_projection,
)
from scripts.obligation_evidence_projection import (
    ObligationEvidenceProjectionError,
    project_source_route_leaf_material_from_validated_inputs,
)
from scripts.obligation_paper_index import (
    PaperObligationIndexError,
    prerequisite_source_judgments_by_source_item,
)
from scripts.obligation_preflight import ObligationStructuralPreflight
from scripts.obligation_routes import EvidenceRoute, EvidenceRouteSet, RouteKind
from scripts.semantic_review_binding import (
    unique_reusable_judgment_bindings,
)
from scripts.public_source_role_projection import (
    PUBLIC_SOURCE_ROLE_PROJECTION_FILE,
    validate_runtime_public_source_role_projection,
)


class TerminalLeanSemanticRevalidationError(ValueError):
    """Current Lean meaning cannot be proved equal to accepted review material."""


LEGACY_MANIFEST_FIELDS = frozenset(
    {
        "elaborated_signature_sha256",
        "elaborated_proposition_graph_sha256",
        "semantic_dependency_sha256",
    }
)
LEAN_MODULE_RE = re.compile(
    r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*"
)


def _json_bytes(path: Path, label: str) -> tuple[dict[str, Any], bytes]:
    try:
        raw = path.read_bytes()
        payload = json.loads(raw)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise TerminalLeanSemanticRevalidationError(
            f"{label} is unavailable or malformed: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise TerminalLeanSemanticRevalidationError(f"{label} is not an object")
    return payload, raw


def _configured_assumption_names(
    status: Mapping[str, Any], *, entry_module: str
) -> tuple[str, ...]:
    """Validate discovery names and use the shared graph owner's qualification."""

    review_surface = status.get("review_surface")
    raw = (
        review_surface.get("assumption_names")
        if isinstance(review_surface, Mapping)
        else None
    )
    if raw is None:
        return ()
    if (
        not isinstance(raw, list)
        or any(not isinstance(name, str) or not name.strip() for name in raw)
        or len({name.strip() for name in raw}) != len(raw)
    ):
        raise TerminalLeanSemanticRevalidationError(
            "paper status has a malformed assumption-name inventory"
        )
    return tuple(sorted(_configured_assumption_root_names(
        SimpleNamespace(status_payload=status), entry_module=entry_module
    )))


def _current_review_import_module(
    status: Mapping[str, Any],
    paper: str,
    *,
    accepted_import_closure: Mapping[str, Any],
) -> str:
    """Return the current paper-owned module that exposes proof endpoints.

    The caller authenticates the accepted import closure against the accepted
    build leaf before recovery. Its entry module remains the execution root
    unless the current review surface explicitly replaces it with
    ``proof_module``. Container drift invalidates the old byte snapshot, not
    the choice of import root. Current Lean acquisition must rebuild that root
    and validate every typed endpoint; declaration namespaces do not identify
    the modules that contain their proofs.
    """

    review_surface = status.get("review_surface")
    if not isinstance(review_surface, Mapping):
        raise TerminalLeanSemanticRevalidationError(
            "paper status has no review_surface object"
        )
    configured = review_surface.get("proof_module")
    module = (
        configured.strip()
        if isinstance(configured, str) and configured.strip()
        else accepted_import_closure.get("entry_module")
    )
    if not isinstance(module, str) or not LEAN_MODULE_RE.fullmatch(module):
        raise TerminalLeanSemanticRevalidationError(
            "paper recovery has a malformed review proof module"
        )
    if module != paper and not module.startswith(f"{paper}."):
        raise TerminalLeanSemanticRevalidationError(
            "review proof module is not owned by the paper"
        )
    return module


def _trusted_public_source_role_envelope(paper_dir: Path) -> bytes:
    """Read release authority from a fetched canonical public main Git tree.

    A contributor's working file or branch cannot issue this bridge. CI checks
    out the canonical repository with full remote history; offline readers
    must likewise have fetched its main ref. The private release guard checks
    issuance against private inputs before the public maintainer merges it.
    """

    paper_dir = paper_dir.resolve()
    root = paper_dir.parents[1]
    if paper_dir.parent.name != "papers" or not re.fullmatch(
        r"[A-Za-z0-9][A-Za-z0-9_-]*", paper_dir.name
    ):
        raise ValueError("public source-role envelope has an invalid paper path")
    relative = f"papers/{paper_dir.name}/{PUBLIC_SOURCE_ROLE_PROJECTION_FILE}"

    def git(*args: str) -> bytes:
        result = subprocess.run(
            ["git", "-C", str(root), *args], capture_output=True, timeout=30
        )
        if result.returncode:
            raise ValueError("canonical public Git source-role authority is unavailable")
        return result.stdout

    canonical = re.compile(
        r"(?:https://github\.com/|git@github\.com:|ssh://git@github\.com/)"
        r"nikhgarg/(?:AppliedModelingLib|EconCSLib)(?:\.git)?"
    )
    candidates = []
    for remote in git("remote").decode().splitlines():
        urls = git("remote", "get-url", "--all", remote).decode().splitlines()
        if len(urls) == 1 and canonical.fullmatch(urls[0]):
            try:
                candidates.append(git("show", f"refs/remotes/{remote}/main:{relative}"))
            except ValueError:
                continue
    try:
        current = (root / relative).read_bytes()
    except OSError as exc:
        raise ValueError("public source-role envelope is unavailable") from exc
    if current not in candidates:
        raise ValueError(
            "public source-role envelope is not authenticated by canonical public main"
        )
    return current


def _validate_current_source_routes(
    loaded: object,
    source_map: Mapping[str, Any],
    preflight: ObligationStructuralPreflight,
    *,
    paper_dir: Path,
    allow_withheld_source_material: bool = False,
    authenticated_prerequisite_source_items_by_declaration: (
        Mapping[str, str] | None
    ) = None,
) -> Mapping[str, str]:
    """Bind current clauses and bundles to accepted routes by semantic identity.

    Source-item keys are navigation. Exact keys are preferred when their
    semantics still agree; a renamed key is accepted only through a complete
    mutual one-to-one match of source atoms and reviewed verbatim bundle.
    """

    paper_index = getattr(loaded, "paper_index", None)
    indexed = getattr(paper_index, "route_leaf_sha256s_by_source_item", None)
    prerequisites = getattr(
        paper_index, "prerequisite_leaf_sha256s_by_declaration", None
    )
    graph = getattr(loaded, "graph", None)
    leaves = getattr(graph, "leaves", None)
    if not all(
        isinstance(value, Mapping) for value in (indexed, prerequisites, leaves)
    ):
        raise TerminalLeanSemanticRevalidationError(
            "accepted graph has no exact source-route index"
        )
    assert isinstance(indexed, Mapping)
    assert isinstance(prerequisites, Mapping)
    assert isinstance(leaves, Mapping)
    try:
        projected_source_map = source_map
        withheld_roles = set()
        if allow_withheld_source_material:
            if "source_text_file" in source_map:
                raise ValueError("public source recovery requires a withheld source locator")
            items = source_map.get("items", {})
            corrected_roles = {
                key for key, item in items.items()
                if isinstance(item, Mapping) and item.get("corrected_target") is not None
            }
            withheld_roles = corrected_roles | {
                key for key, item in items.items()
                if isinstance(item, Mapping)
                and item.get("user_approved_scope_exclusion") is not None
            }
            if corrected_roles:
                if source_map.get("publication_corrected_target_projection") != {
                    "schema": 1, "approval_material_included": False
                }:
                    raise ValueError("public corrected targets lack their withholding declaration")
                # The private corrected-target parser requires the withheld
                # approval. Project its atoms without that object; the trusted
                # bridge below independently binds every retained target field.
                projected_source_map = dict(source_map, items={
                    key: {k: v for k, v in item.items() if k != "corrected_target"}
                    for key, item in items.items()
                })
        current_leaves, navigation = (
            project_source_route_leaf_material_from_validated_inputs(
                source_map=projected_source_map,
                preflight=preflight,
            )
        )
        if allow_withheld_source_material:
            if "source_text_file" in source_map:
                raise ValueError("public source recovery requires a withheld source locator")
            source_material = None
        else:
            source_material = current_source_semantic_material(
                paper_dir=paper_dir,
                source_map=source_map,
                source_route_navigation=navigation,
            )
    except (
        ObligationEvidenceError,
        ObligationEvidenceProjectionError,
        ValueError,
    ) as exc:
        raise TerminalLeanSemanticRevalidationError(str(exc)) from exc
    def semantic_atoms(
        digests: tuple[str, ...], universe: Mapping[str, object]
    ) -> tuple[tuple[str, str, str], ...]:
        result = []
        for digest in digests:
            leaf = universe.get(digest)
            try:
                projection = source_atom_semantic_projection(leaf)  # type: ignore[arg-type]
            except ObligationEvidenceError as exc:
                raise TerminalLeanSemanticRevalidationError(str(exc)) from exc
            result.append(
                (
                    projection["source_quote_sha256"],
                    projection["source_component_sha256"],
                    projection["source_role_contract_sha256"],
                )
            )
        return tuple(sorted(result))

    accepted_atom_ids: dict[str, tuple[str, ...]] = {}
    accepted_entries: dict[str, dict[str, object]] = {}
    accepted_bundles: dict[str, set[str]] = {}
    for source_item_id, roles in sorted(indexed.items()):
        if not isinstance(roles, Mapping):
            raise TerminalLeanSemanticRevalidationError(
                f"accepted source route is malformed: {source_item_id}"
            )
        atom_ids = tuple(roles.get("source_atom", ()))
        accepted_atom_ids[str(source_item_id)] = atom_ids
        accepted_entries[str(source_item_id)] = {
            "source_atoms": semantic_atoms(atom_ids, leaves),
        }
        accepted_bundles[str(source_item_id)] = set()

    if allow_withheld_source_material:
        if withheld_roles:
            try:
                map_payload, map_bytes = _json_bytes(
                    paper_dir / "audit/paper_statement_map.json", "public source map"
                )
                if map_payload != source_map:
                    raise ValueError("public source map changed during revalidation")
                _, display_bytes = _json_bytes(
                    paper_dir / "audit/public_source_display_projection.json",
                    "public source display manifest",
                )
                validate_runtime_public_source_role_projection(
                    trusted_envelope_bytes=_trusted_public_source_role_envelope(paper_dir),
                    paper=paper_dir.name,
                    public_source_map_bytes=map_bytes,
                    public_display_manifest_bytes=display_bytes,
                    # The credential's graph property exposes only its inner
                    # semantic DAG. The release bridge pins the accepting DAG,
                    # whose identity belongs to the credential itself.
                    accepted_graph_sha256=getattr(loaded, "graph_sha256", ""),
                    accepted_role_sha256s_by_source_item={
                        key: tuple(atom[2] for atom in entry["source_atoms"])
                        for key, entry in accepted_entries.items()
                    },
                )
            except (ValueError, OSError, subprocess.SubprocessError) as exc:
                raise TerminalLeanSemanticRevalidationError(str(exc)) from exc
        # Public exports cannot replay private verbatim/approval bundles. Keep
        # their exact route names and semantic source atoms fixed instead;
        # subsequent Lean checks still validate every target and dependency.
        # This route reads recorded evidence and cannot issue acceptance.
        if set(navigation) != set(accepted_entries) or any(
            tuple(a[:2] if source_item_id in withheld_roles else a
                  for a in semantic_atoms(tuple(atom_ids), current_leaves))
            != tuple(a[:2] if source_item_id in withheld_roles else a
                     for a in accepted_entries[source_item_id]["source_atoms"])
            for source_item_id, atom_ids in navigation.items()
        ):
            raise TerminalLeanSemanticRevalidationError(
                "public source routes or semantic atoms changed"
            )
        return {source_item_id: source_item_id for source_item_id in navigation}

    def judgment_bundle(digest: str, atom_ids: tuple[str, ...]) -> str:
        leaf = leaves.get(digest)
        payload = getattr(leaf, "semantic_payload", None)
        if not isinstance(payload, Mapping):
            raise TerminalLeanSemanticRevalidationError(
                "accepted source judgment is malformed"
            )
        if tuple(payload.get("source_atom_sha256s", ())) != atom_ids:
            raise TerminalLeanSemanticRevalidationError(
                "accepted source judgment binds different clauses"
            )
        bundle = str(
            payload.get("verbatim_source_bundle_sha256") or ""
        ).strip().lower()
        if not re.fullmatch(r"[0-9a-f]{64}", bundle):
            raise TerminalLeanSemanticRevalidationError(
                "accepted source judgment has no exact bundle"
            )
        return bundle

    # Direct result judgments are already owned by their accepted route.
    for source_item_id, roles in sorted(indexed.items()):
        assert isinstance(roles, Mapping)
        atom_ids = accepted_atom_ids[str(source_item_id)]
        for digest in roles.get("source_lean_judgment", ()):
            accepted_bundles[str(source_item_id)].add(
                judgment_bundle(str(digest), atom_ids)
            )

    # Prerequisite judgments are routed by the immutable graph/index relation.
    # When two source items share its exact atoms, an issuance-authenticated
    # review row may retain the more specific accepted owner. Unauthenticated
    # editable navigation never participates.
    try:
        prerequisite_judgments = prerequisite_source_judgments_by_source_item(
            paper_index,
            preflight,
            authenticated_source_items_by_declaration=(
                authenticated_prerequisite_source_items_by_declaration
            ),
        )
    except (PaperObligationIndexError, ValueError) as exc:
        raise TerminalLeanSemanticRevalidationError(str(exc)) from exc
    for source_item_id, judgment_ids in prerequisite_judgments.items():
        atom_ids = accepted_atom_ids[source_item_id]
        for judgment_id in judgment_ids:
            accepted_bundles[source_item_id].add(
                judgment_bundle(str(judgment_id), atom_ids)
            )

    route_set = getattr(preflight, "route_set", None)
    result_routes = (
        route_set.result_routes()
        if route_set is not None
        else ()
    )
    reviewed_current_routes = {
        route.source_item_id
        for route in result_routes
    }
    if route_set is not None:
        reviewed_current_routes.update(
            route.source_item_id
            for route in getattr(route_set, "routes", ())
            if route.route_kind is RouteKind.SOURCE_SEMANTIC_DECLARATION
        )
    # A prior prerequisite source judgment remains a current source-input
    # obligation through the accepted graph/index relation.  Fresh route
    # admission can later classify that source presentation as proof support,
    # but that presentation change must not turn its required bundle into an
    # empty tuple during terminal recovery.  ``prerequisite_judgments`` is
    # already fail-closed: it binds each accepted prerequisite judgment to an
    # exact-atom owner, refined only by authenticated accepted ownership.
    # Including those routes here still requires the current full bundle
    # (including any approved review contexts) to equal the accepted judgment
    # bundle.
    reviewed_current_routes.update(prerequisite_judgments)
    if route_set is None:
        reviewed_current_routes.update(
            source_item_id
            for source_item_id in navigation
            if accepted_bundles.get(source_item_id)
        )
    current_entries: dict[str, dict[str, object]] = {}
    for source_item_id, atom_ids in sorted(navigation.items()):
        bundle = source_material[source_item_id].source_input_bundle_sha256
        current_entries[source_item_id] = {
            "source_atoms": semantic_atoms(atom_ids, current_leaves),
            "reviewed_bundles": (
                (bundle,) if source_item_id in reviewed_current_routes else ()
            ),
        }
    for source_item_id, accepted_entry in accepted_entries.items():
        accepted_entry["reviewed_bundles"] = tuple(
            sorted(accepted_bundles[source_item_id])
        )

    def reusable_route(
        prior: object, current: Mapping[str, Any]
    ) -> dict[str, str] | None:
        if not isinstance(prior, Mapping):
            return None
        return (
            {"identity": "exact-source-route-semantics"}
            if prior.get("source_atoms") == current.get("source_atoms")
            and prior.get("reviewed_bundles") == current.get("reviewed_bundles")
            else None
        )

    bindings = unique_reusable_judgment_bindings(
        current_entries,
        accepted_entries,
        reusable_judgment=reusable_route,
    )
    used_accepted = {accepted for accepted, _metadata in bindings.values()}
    if set(bindings) != set(current_entries) or used_accepted != set(accepted_entries):
        for source_item_id in sorted(set(current_entries) & set(accepted_entries)):
            prior = accepted_entries[source_item_id]
            current = current_entries[source_item_id]
            if prior.get("source_atoms") == current.get("source_atoms") and prior.get(
                "reviewed_bundles"
            ) != current.get("reviewed_bundles"):
                raise TerminalLeanSemanticRevalidationError(
                    f"current verbatim source bundle changed: {source_item_id}"
                )
        raise TerminalLeanSemanticRevalidationError(
            "current exact source routes do not form a complete one-to-one "
            "semantic binding to the accepted graph"
        )
    return {
        current: accepted
        for current, (accepted, _metadata) in bindings.items()
    }


def _validate_accepted_direct_route(
    route: EvidenceRoute,
    roles: Mapping[str, object],
    leaves: Mapping[str, object],
    current_semantic_targets: Mapping[str, object],
    semantic_signatures: Mapping[str, str],
    *,
    require_reviewed_display: bool = False,
) -> None:
    """Validate one accepted direct route after the shared Lean acquisition."""

    def one_leaf(role: str) -> object:
        leaf_ids = roles.get(role, ())
        if (
            not isinstance(leaf_ids, (list, tuple))
            or len(leaf_ids) != 1
            or leaf_ids[0] not in leaves
        ):
            raise TerminalLeanSemanticRevalidationError(
                f"accepted direct route has no unique {role} leaf: "
                + route.source_item_id
            )
        return leaves[leaf_ids[0]]

    review_leaf = one_leaf("semantic_review")
    spec_leaf = one_leaf("spec")
    endpoint_leaf = one_leaf("proof_endpoint")
    realization_leaf = one_leaf("proof_realization")
    if review_leaf is not spec_leaf and getattr(
        review_leaf, "leaf_sha256", None
    ) != getattr(spec_leaf, "leaf_sha256", None):
        raise TerminalLeanSemanticRevalidationError(
            "accepted direct route separates its reviewed target and Spec: "
            + route.source_item_id
        )
    review_payload = getattr(review_leaf, "semantic_payload", None)
    endpoint_payload = getattr(endpoint_leaf, "semantic_payload", None)
    realization_payload = getattr(realization_leaf, "semantic_payload", None)
    if not all(
        isinstance(payload, Mapping)
        for payload in (review_payload, endpoint_payload, realization_payload)
    ):
        raise TerminalLeanSemanticRevalidationError(
            "accepted direct route has malformed Lean leaves: " + route.source_item_id
        )
    assert isinstance(review_payload, Mapping)
    assert isinstance(endpoint_payload, Mapping)
    assert isinstance(realization_payload, Mapping)
    target = current_semantic_targets.get(route.semantic_review_declaration)
    current_target = (
        str(target.get("display_sha256") or "").strip().lower()
        if isinstance(target, Mapping)
        else ""
    )
    reviewed_target = str(
        review_payload.get("reviewed_semantic_target_sha256") or ""
    ).strip().lower()
    if require_reviewed_display and not reviewed_target:
        raise TerminalLeanSemanticRevalidationError(
            "changed-container recovery requires an accepted reviewed semantic "
            "target for " + route.semantic_review_declaration
            + "; require deliberate new acceptance"
        )
    if {
        "reviewed_semantic_target_sha256",
        "elaborated_signature_sha256",
    } <= set(review_payload):
        review_matches = (
            review_payload.get("semantic_target_kind")
            == route.semantic_review_target_kind.value
            and current_target == reviewed_target
            and semantic_signatures.get(route.semantic_review_declaration)
            == review_payload.get("elaborated_signature_sha256")
        )
    elif "reviewed_semantic_target_sha256" in review_payload:
        review_matches = (
            current_target == reviewed_target
            and review_payload.get("semantic_target_kind")
            == route.semantic_review_target_kind.value
        )
    elif LEGACY_MANIFEST_FIELDS <= set(review_payload):
        review_matches = review_payload.get(
            "semantic_target_kind"
        ) == route.semantic_review_target_kind.value and semantic_signatures.get(
            route.semantic_review_declaration
        ) == review_payload.get("elaborated_signature_sha256")
    else:
        review_matches = False
    if not review_matches:
        raise TerminalLeanSemanticRevalidationError(
            "accepted direct semantic target changed: "
            + route.semantic_review_declaration
        )
    accepted_spec = getattr(spec_leaf, "leaf_sha256", None)
    accepted_endpoint = getattr(endpoint_leaf, "leaf_sha256", None)
    if "spec_declaration_sha256" in endpoint_payload:
        endpoint_matches = (
            endpoint_payload.get("spec_declaration_sha256") == accepted_spec
            and endpoint_payload.get("relation") == route.evidence_mode
        )
    elif LEGACY_MANIFEST_FIELDS <= set(endpoint_payload):
        # Historical engines represented a proof implementation by the same
        # whole-declaration manifest used for a reviewed Spec. That proof-body
        # identity is not a source-semantic obligation: the current graph
        # instead elaborates the exact named endpoint, checks its typed
        # relation to the unchanged accepted Spec, and recomputes its complete
        # axiom/sorry/unsafe boundary. Requiring the old proof-body manifest as
        # well would make proof refactors invalidate a mathematical review
        # without adding correctness.
        endpoint_matches = (
            endpoint_payload.get("semantic_target_kind") == "proof_endpoint"
        )
    else:
        endpoint_matches = False
    if (
        not endpoint_matches
        or realization_payload.get("spec_declaration_sha256") != accepted_spec
        or realization_payload.get("proof_endpoint_sha256") != accepted_endpoint
        or realization_payload.get("relation") != route.evidence_mode
    ):
        raise TerminalLeanSemanticRevalidationError(
            f"accepted direct typed relation changed: {route.source_item_id}"
        )


def _validate_accepted_direct_routes(
    loaded: object,
    routes: tuple[EvidenceRoute, ...],
    current_semantic_targets: Mapping[str, object],
    semantic_signatures: Mapping[str, str],
    source_route_bindings: Mapping[str, str] | None = None,
    *,
    require_reviewed_display: bool = False,
) -> None:
    """Bind all current Lean results to the exact accepted direct leaves.

    Lean acquisition is shared by the whole paper. Report every independently
    stale route discovered from that acquisition so a repair pass does not
    need to repeat the expensive graph walk merely to reveal the next route.
    """

    paper_index = getattr(loaded, "paper_index", None)
    indexed = getattr(paper_index, "route_leaf_sha256s_by_source_item", None)
    graph = getattr(loaded, "graph", None)
    leaves = getattr(graph, "leaves", None)
    if not isinstance(indexed, Mapping) or not isinstance(leaves, Mapping):
        raise TerminalLeanSemanticRevalidationError(
            "accepted graph has no exact direct-route index"
        )
    route_bindings = source_route_bindings or {
        route.source_item_id: route.source_item_id for route in routes
    }
    claim_ids = {
        route_bindings.get(route.source_item_id, "") for route in routes
    }
    accepted_claim_ids = {
        str(source_item_id)
        for source_item_id, roles in indexed.items()
        if isinstance(roles, Mapping)
        and any(
            role in roles
            for role in (
                "semantic_review",
                "spec",
                "proof_endpoint",
                "proof_realization",
            )
        )
    }
    if claim_ids != accepted_claim_ids:
        raise TerminalLeanSemanticRevalidationError(
            "accepted graph direct routes differ from the current paper surface"
        )

    failures: list[str] = []
    for route in routes:
        accepted_source_item = route_bindings.get(route.source_item_id)
        roles = indexed.get(accepted_source_item) if accepted_source_item else None
        if not isinstance(roles, Mapping):
            failures.append(
                f"accepted direct route is malformed: {route.source_item_id}"
            )
            continue
        try:
            _validate_accepted_direct_route(
                route,
                roles,
                leaves,
                current_semantic_targets,
                semantic_signatures,
                require_reviewed_display=require_reviewed_display,
            )
        except TerminalLeanSemanticRevalidationError as exc:
            failures.append(str(exc))
    if failures:
        raise TerminalLeanSemanticRevalidationError(
            "accepted direct-route revalidation found "
            f"{len(failures)} failure(s):\n- " + "\n- ".join(failures)
        )


def _unchanged_prerequisite_declarations_from_inventory(
    inventory: Mapping[str, Any],
    provider: RepositoryBuildInputSnapshotProvider,
    import_module: str,
    accepted_import_closure: Mapping[str, Any],
    *,
    paper_declarations: set[str],
    library_declarations: set[str],
) -> set[str]:
    """Return accepted declarations whose complete source module is unchanged.

    The terminal recovery graph already records each declaration's Lean-owned
    source module. The accepted import closure records that module's full
    source digest. Exact module equality is a conservative proof that a
    historical declaration-code contract is unchanged when a newer renderer
    no longer reproduces its old display. No declaration parser, source range,
    or saved line hint participates.
    """

    snapshots = provider.repository_source_snapshot(import_module)
    if not snapshots:
        raise TerminalLeanSemanticRevalidationError(
            "current Lean import closure has no frozen source snapshot"
        )
    try:
        declaration_modules = lean_inventory_review_declaration_modules(
            inventory,
            paper_declarations=paper_declarations,
            library_declarations=library_declarations,
        )
    except ValueError as exc:
        raise TerminalLeanSemanticRevalidationError(str(exc)) from exc
    expected = paper_declarations | library_declarations
    if set(declaration_modules) != expected:
        raise TerminalLeanSemanticRevalidationError(
            "Lean source-module projection differs from accepted prerequisites"
        )
    raw_sources = accepted_import_closure.get("sources")
    if not isinstance(raw_sources, list):
        raise TerminalLeanSemanticRevalidationError(
            "accepted Lean import closure has no source inventory"
        )
    accepted_source_sha256s: dict[str, str] = {}
    for raw in raw_sources:
        if not isinstance(raw, Mapping):
            raise TerminalLeanSemanticRevalidationError(
                "accepted Lean import closure has a malformed source row"
            )
        module = str(raw.get("module") or "").strip()
        digest = str(raw.get("sha256") or "").strip().lower()
        if (
            not LEAN_MODULE_RE.fullmatch(module)
            or not re.fullmatch(r"[0-9a-f]{64}", digest)
            or module in accepted_source_sha256s
        ):
            raise TerminalLeanSemanticRevalidationError(
                "accepted Lean import closure has an ambiguous source inventory"
            )
        accepted_source_sha256s[module] = digest
    current_source_sha256s = {
        module: digest for module, _path, _content, digest in snapshots
    }
    return {
        name
        for name, module in declaration_modules.items()
        if accepted_source_sha256s.get(module)
        == current_source_sha256s.get(module)
    }


def _current_paper_modules(
    root: Path,
    paper: str,
    import_module: str,
    provider: RepositoryBuildInputSnapshotProvider,
    *,
    timeout_seconds: int,
) -> tuple[tuple[str, ...], dict[str, tuple[Path, bytes]]]:
    """Return the Lean-owned paper modules and exact repository snapshot."""

    if not provider.lean_loaded_module_names(
        import_module, timeout_seconds=timeout_seconds
    ):
        detail = provider.lean_loaded_module_error(import_module)
        raise TerminalLeanSemanticRevalidationError(
            "current Lean-loaded module closure is unavailable"
            + (": " + detail if detail else "")
        )
    snapshots = provider.repository_source_snapshot(import_module)
    if not snapshots:
        raise TerminalLeanSemanticRevalidationError(
            "current Lean repository-source snapshot is unavailable"
        )
    module_sources: dict[str, tuple[Path, bytes]] = {}
    for module, path, content, _digest in snapshots:
        resolved = path.resolve()
        module_sources[module] = (resolved, content)
    try:
        result = paper_module_names_from_sources(
            root,
            root / "papers" / paper,
            module_sources,
            required_entry_module=import_module,
        )
    except ValueError as exc:
        raise TerminalLeanSemanticRevalidationError(str(exc)) from exc
    return result, module_sources


def _acquire_terminal_graph_projection(
    root: Path,
    paper_dir: Path,
    *,
    route_set: EvidenceRouteSet,
    expected_specifications: set[str],
    import_module: str,
    paper_modules: tuple[str, ...],
    module_sources: Mapping[str, tuple[Path, bytes]],
    accepted_import_closure: Mapping[str, Any],
    assumption_names: set[str],
    provider: RepositoryBuildInputSnapshotProvider,
    build_timeout_seconds: int,
) -> tuple[
    V11LeanReviewGraphRequestPlan,
    Mapping[str, Any],
    V11LeanReviewGraphProjection,
]:
    """Acquire and project the same typed Lean graph used by fresh closeout."""

    try:
        request_plan = build_graph_request_plan(
            route_set,
            expected_specifications,
            entry_module=import_module,
            paper_modules=paper_modules,
            workspace_modules=module_sources,
            lean_import_closure=accepted_import_closure,
        )
        terminal_graph_request = dict(request_plan.request_projection())
        terminal_graph_request["axiom_root_names"] = sorted(
            request_plan.semantic_declarations | assumption_names
        )
        terminal_graph_request["root_semantic_manifest_declaration_names"] = sorted(
            assumption_names
        )
        inventory = current_terminal_lean_graph_inventory(
            root,
            paper_dir,
            graph_request=terminal_graph_request,
            module_sources=module_sources,
        )
        # Recovery requests the same complete graph as fresh closeout.
        # Its acquisition owner supplies the shared bounded graph budget;
        # the separate build timeout must not truncate that budget.
        acquisition = acquire_validated_graph_projection(
            root,
            paper_dir,
            request_plan,
            module_sources=module_sources,
            inventory=inventory,
            build_input_provider=provider,
            additional_axiom_root_names=assumption_names,
            root_semantic_manifest_declaration_names=assumption_names,
            build_timeout_seconds=build_timeout_seconds,
        )
        inventory = acquisition.inventory
        projection = acquisition.projection
        if acquisition.acquired_fresh:
            try:
                checkpoint_terminal_lean_graph(
                    root,
                    paper_dir,
                    graph_request=terminal_graph_request,
                    module_sources=module_sources,
                    inventory=inventory,
                )
            except (OSError, RuntimeError, TypeError, ValueError):
                # An operational cache can save work but can never be required
                # for acceptance after the current graph itself has validated.
                pass
    except ValueError as exc:
        raise TerminalLeanSemanticRevalidationError(str(exc)) from exc
    return request_plan, inventory, projection


def _validate_prerequisites(
    loaded: object,
    *,
    review_surface: LeanSemanticReviewDisplaySurface,
    semantic_signatures: Mapping[str, str],
    unchanged_declaration_names: set[str] | None = None,
    require_reviewed_display: bool = False,
) -> None:
    """Compare accepted prerequisite identities to the one current Lean graph.

    This is terminal currentness recovery for an already accepted graph, not a
    new closeout under today's discovery policy.  Lean may now expose more
    prerequisite rows than the issuing engine did.  Those are obligations for
    a later protocol migration, while every prerequisite leaf the accepted
    graph actually owns must still be present and semantically identical.
    Fresh closeout materialization continues to require the complete current
    Lean-discovered surface exactly.
    """

    paper_index = getattr(loaded, "paper_index", None)
    indexed = getattr(paper_index, "prerequisite_leaf_sha256s_by_declaration", None)
    graph = getattr(loaded, "graph", None)
    leaves = getattr(graph, "leaves", None)
    if not isinstance(indexed, Mapping) or not isinstance(leaves, Mapping):
        raise TerminalLeanSemanticRevalidationError(
            "accepted graph has no prerequisite declaration index"
        )
    unchanged_names = unchanged_declaration_names or set()
    accepted: dict[str, Mapping[str, Any]] = {}
    failures: list[str] = []
    for name, roles in sorted(indexed.items()):
        lean_ids = (
            roles.get("lean_declaration", ()) if isinstance(roles, Mapping) else ()
        )
        if (
            not isinstance(lean_ids, (list, tuple))
            or len(lean_ids) != 1
            or lean_ids[0] not in leaves
        ):
            failures.append(f"accepted prerequisite has no unique Lean leaf: {name}")
            continue
        payload = getattr(leaves[lean_ids[0]], "semantic_payload", None)
        if not isinstance(payload, Mapping):
            failures.append(f"accepted prerequisite Lean leaf is malformed: {name}")
            continue
        if require_reviewed_display and not str(
            payload.get("reviewed_semantic_target_sha256") or ""
        ).strip():
            failures.append(
                "changed-container recovery requires an accepted reviewed semantic "
                f"target for {name}; require deliberate new acceptance"
            )
            continue
        accepted[name] = {**dict(payload), "accepted_name": name}
    if failures:
        raise TerminalLeanSemanticRevalidationError(
            "accepted prerequisite revalidation found "
            f"{len(failures)} failure(s):\n- " + "\n- ".join(failures)
        )

    current_targets = {
        name: {
            "lean_name": name,
            "display_sha256": str(target.get("display_sha256") or "").strip(),
            "elaborated_signature_sha256": str(
                semantic_signatures.get(name) or ""
            ).strip(),
        }
        for targets in (
            review_surface.paper_declarations,
            review_surface.library_declarations,
        )
        for name, target in targets.items()
    }

    def reusable(
        prior: object, current: Mapping[str, Any]
    ) -> dict[str, str] | None:
        if not isinstance(prior, Mapping):
            return None
        if prior.get("semantic_target_kind") != "semantic_prerequisite":
            return None
        accepted_signature = str(
            prior.get("elaborated_signature_sha256") or ""
        ).strip()
        current_signature = str(
            current.get("elaborated_signature_sha256") or ""
        ).strip()
        if accepted_signature:
            if "reviewed_semantic_target_sha256" in prior:
                reviewed_target = str(
                    prior.get("reviewed_semantic_target_sha256") or ""
                ).strip()
                if not reviewed_target or reviewed_target != str(
                    current.get("display_sha256") or ""
                ).strip():
                    return None
            return (
                {"identity": accepted_signature}
                if accepted_signature == current_signature
                else None
            )
        reviewed_target = str(
            prior.get("reviewed_semantic_target_sha256") or ""
        ).strip()
        if not reviewed_target or reviewed_target != str(
            current.get("display_sha256") or ""
        ).strip():
            return None
        if "declaration_content_sha256" in prior and (
            str(prior.get("accepted_name") or "").strip()
            != str(current.get("lean_name") or "").strip()
            or str(current.get("lean_name") or "").strip() not in unchanged_names
        ):
            return None
        return {"identity": reviewed_target}

    bindings = unique_reusable_judgment_bindings(
        current_targets,
        accepted,
        reusable_judgment=reusable,
    )
    used_accepted = {name for name, _metadata in bindings.values()}
    if used_accepted != set(accepted):
        missing = sorted(set(accepted) - used_accepted)
        raise TerminalLeanSemanticRevalidationError(
            "current Lean graph cannot uniquely reproduce "
            f"{len(missing)} accepted prerequisite semantic identity(s): "
            + ", ".join(missing[:8])
        )


def _material_axiom_boundary_names(
    *,
    proof_endpoints: set[str],
    configured_names: set[str],
    inventory: Mapping[str, Any],
) -> set[str]:
    """Collect nonfoundation axioms reached by every required native root."""

    raw_nodes = inventory.get("declarations")
    if not isinstance(raw_nodes, list):
        raise TerminalLeanSemanticRevalidationError(
            "Lean graph omits declaration axiom closures"
        )
    closures = {
        str(node.get("declaration") or "").strip(): {
            str(value) for value in node.get("axiom_closure") or []
        }
        for node in raw_nodes
        if isinstance(node, Mapping)
        and node.get("axiom_closure_checked") is True
        and str(node.get("declaration") or "").strip()
    }
    required_roots = proof_endpoints | configured_names
    if not required_roots.issubset(closures):
        raise TerminalLeanSemanticRevalidationError(
            "Lean graph omits a required axiom-closure root"
        )
    return set().union(*(closures[root] for root in required_roots)) - set(
        APPROVED_LEAN_AXIOMS
    )


def revalidate_terminal_lean_semantics(
    root: Path,
    paper: str,
    loaded: object,
    *,
    preflight: ObligationStructuralPreflight,
    accepted_import_closure: Mapping[str, Any],
    current_import_closure: Mapping[str, Any] | None = None,
    allow_withheld_source_material: bool = False,
    authenticated_prerequisite_source_items_by_declaration: (
        Mapping[str, str] | None
    ) = None,
    build_timeout_seconds: int = 600,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> tuple[RepositoryBuildInputSnapshotProvider, tuple[Path, ...]]:
    """Return a current provider only after shared material and Lean checks pass."""

    root = root.resolve()
    paper_dir = root / "papers" / paper
    audit_dir = paper_dir / "audit"
    status_path = paper_dir / "status.json"
    source_map_path = audit_dir / "paper_statement_map.json"
    status, status_raw = _json_bytes(status_path, "paper status")
    execution_import_closure = (
        current_import_closure
        if current_import_closure is not None
        else accepted_import_closure
    )
    import_module = _current_review_import_module(
        status, paper, accepted_import_closure=execution_import_closure,
    )
    source_map, source_map_raw = _json_bytes(source_map_path, "paper statement map")
    configured_assumptions = _configured_assumption_names(
        status, entry_module=import_module
    )
    preflight.require_current()
    assert preflight.route_set is not None
    result_routes = preflight.route_set.result_routes()
    expected_specifications = {
        route.spec_declaration for route in result_routes
    }

    source_route_bindings = _validate_current_source_routes(
        loaded,
        source_map,
        preflight,
        paper_dir=paper_dir,
        allow_withheld_source_material=allow_withheld_source_material,
        authenticated_prerequisite_source_items_by_declaration=(
            authenticated_prerequisite_source_items_by_declaration
        ),
    )

    if build_input_provider is None:
        if current_import_closure is not None:
            raise TerminalLeanSemanticRevalidationError(
                "current Lean import closure requires its adopting build-input provider"
            )
        provider = RepositoryBuildInputSnapshotProvider(root)
    else:
        provider = build_input_provider
        if provider.root != root:
            raise TerminalLeanSemanticRevalidationError(
                "shared Lean build-input provider belongs to a different repository"
            )
        if (
            current_import_closure is not None
            and not provider.owns_exact_lean_import_closure_payload(
                current_import_closure
            )
        ):
            raise TerminalLeanSemanticRevalidationError(
                "shared Lean build-input provider does not own the current closure"
            )
    paper_modules, module_sources = _current_paper_modules(
        root,
        paper,
        import_module,
        provider,
        timeout_seconds=build_timeout_seconds,
    )
    accepted_index = getattr(
        getattr(loaded, "paper_index", None),
        "prerequisite_leaf_sha256s_by_declaration",
        None,
    )
    if not isinstance(accepted_index, Mapping):
        raise TerminalLeanSemanticRevalidationError(
            "accepted graph has no prerequisite declaration index"
        )
    accepted_prerequisite_names = set(accepted_index)
    request_plan, inventory, projection = _acquire_terminal_graph_projection(
        root,
        paper_dir,
        route_set=preflight.route_set,
        expected_specifications=expected_specifications,
        import_module=import_module,
        paper_modules=paper_modules,
        module_sources=module_sources,
        accepted_import_closure=execution_import_closure,
        assumption_names=set(configured_assumptions),
        provider=provider,
        build_timeout_seconds=build_timeout_seconds,
    )
    try:
        review_surface = LeanSemanticReviewDisplaySurface(
            specifications={
                name: projection.semantic_targets[name]
                for name in request_plan.specifications
            },
            paper_declarations=projection.paper_semantic_targets,
            library_declarations=projection.library_semantic_targets,
        )
        semantic_signatures = {
            name: str(target.get("elaborated_signature_sha256") or "").strip()
            for targets in (
                projection.paper_semantic_targets,
                projection.library_semantic_targets,
            )
            for name, target in targets.items()
        }
        current_review_targets: dict[str, Mapping[str, Any]] = {}
        for route in request_plan.selected_routes:
            target = projection.semantic_targets[route.spec_declaration]
            current_review_targets[route.semantic_review_declaration] = target
            semantic_signatures[route.semantic_review_declaration] = str(
                target.get("elaborated_signature_sha256") or ""
            ).strip()
        common_paper_names = accepted_prerequisite_names & set(
            projection.paper_semantic_targets
        )
        common_library_names = accepted_prerequisite_names & set(
            projection.library_semantic_targets
        )
        unchanged_declaration_names = set()
        if current_import_closure is None:
            unchanged_declaration_names = (
                _unchanged_prerequisite_declarations_from_inventory(
                    inventory,
                    provider,
                    import_module,
                    accepted_import_closure,
                    paper_declarations=common_paper_names,
                    library_declarations=common_library_names,
                )
            )
    except ValueError as exc:
        raise TerminalLeanSemanticRevalidationError(str(exc)) from exc
    def validate_axiom_boundaries() -> None:
        material_names = _material_axiom_boundary_names(
            proof_endpoints={route.evidence_declaration for route in result_routes},
            configured_names=set(configured_assumptions),
            inventory=inventory,
        )
        if material_names:
            # Current status and self-pinned worksheets cannot extend the
            # historically accepted trust boundary. Existing graph contracts
            # do not authenticate an axiom-boundary set and proposition pins.
            raise TerminalLeanSemanticRevalidationError(
                "historical accepted graph lacks authenticated axiom-boundary "
                "evidence for: " + ", ".join(sorted(material_names))
                + "; preserve the exact-import fast path or require deliberate "
                "new acceptance"
            )

    # All three checks consume the same expensive Lean graph and are mutually
    # independent after that graph has passed its structural validation. Run
    # all of them before returning a failure so one repair cycle sees the full
    # semantic delta instead of paying for another Lean acquisition per lane.
    semantic_failures: list[str] = []
    checks = (
        (
            "direct routes",
            lambda: _validate_accepted_direct_routes(
                loaded,
                result_routes,
                current_review_targets,
                semantic_signatures,
                source_route_bindings,
                require_reviewed_display=current_import_closure is not None,
            ),
        ),
        (
            "axiom boundaries",
            validate_axiom_boundaries,
        ),
        (
            "semantic prerequisites",
            lambda: _validate_prerequisites(
                loaded,
                review_surface=review_surface,
                semantic_signatures=semantic_signatures,
                unchanged_declaration_names=unchanged_declaration_names,
                require_reviewed_display=current_import_closure is not None,
            ),
        ),
    )
    for label, check in checks:
        try:
            check()
        except TerminalLeanSemanticRevalidationError as exc:
            semantic_failures.append(f"{label}: {exc}")
    if semantic_failures:
        raise TerminalLeanSemanticRevalidationError(
            "terminal Lean semantic revalidation found "
            f"{len(semantic_failures)} failing lane(s):\n- "
            + "\n- ".join(semantic_failures)
        )

    snapshots: dict[Path, bytes] = {
        status_path: status_raw,
        source_map_path: source_map_raw,
    }
    for path, expected in snapshots.items():
        try:
            current = path.read_bytes()
        except OSError as exc:
            raise TerminalLeanSemanticRevalidationError(
                f"semantic revalidation input disappeared: {path}: {exc}"
            ) from exc
        if current != expected:
            raise TerminalLeanSemanticRevalidationError(
                f"semantic revalidation input changed during verification: {path}"
            )
    return provider, tuple(sorted(snapshots, key=str))
