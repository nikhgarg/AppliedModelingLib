"""Build a non-evidence semantic-review bundle before graph acquisition.

This service is deliberately outside the closeout acceptance path.  It asks
Lean for the current expanded selected ``Spec`` declarations and for the
source-mapped paper-local model declarations, then joins them to the already
byte-pinned source items.  The resulting JSON is intended for a
context-isolated reviewer while an interface or source map is still being
repaired.  It writes no graph checkpoint, decision queue, ledger, receipt, or
review result.

The point is ordering, not a second evidence lane: repair source/Lean scope
questions before acquiring the one graph which later selects the exact
prerequisite denominator and supplies the accepting review inputs.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from scripts.current_closeout.lean_review_graph import paper_module_names_from_sources
from scripts.lean_signature_manifest import (
    RepositoryBuildInputSnapshotProvider,
    run_lean_paper_semantic_review_graph,
)
from scripts.obligation_routes import (
    EvidenceRouteSet,
    ObligationRouteError,
    RouteKind,
    SemanticReviewTargetKind,
)
from scripts.source_review_input import (
    approved_corrected_target_review_context,
    source_anchor_file_error,
    source_semantic_input_bundle,
)

DRAFT_SEMANTIC_PREFLIGHT_SCHEMA = "applied-modeling-lib.draft-semantic-preflight/v1"
# This display-only preflight is deliberately separate from the one accepted
# obligation graph.  A paper can have many independent source-facing Specs,
# and asking Lean to pretty-print all of them in one process can exceed a
# machine's memory even though every bounded request is sound.  Keep the
# non-evidentiary surface bounded; the later accepting graph remains exactly
# one frozen Lean transaction.
DRAFT_SEMANTIC_PREFLIGHT_MAX_ROOTS_PER_BATCH = 4
# A single bounded display can still legitimately need more than the generic
# declaration-inventory default: large source-facing Specs must be rendered in
# full so this repair-stage preflight can reject printer elision.  This remains
# below the closeout graph's 900-second transaction budget and applies only to
# this non-evidentiary, bounded display surface.
DRAFT_SEMANTIC_PREFLIGHT_DISPLAY_TIMEOUT_SECONDS = 600


class DraftSemanticPreflightError(ValueError):
    """Raised when a draft review bundle cannot be built faithfully."""


def _draft_display_batches(
    specifications: tuple[str, ...],
    declarations: tuple[str, ...],
) -> tuple[tuple[tuple[str, ...], tuple[str, ...]], ...]:
    """Partition display roots deterministically without changing review scope."""

    roots = tuple(
        [("specification", name) for name in specifications]
        + [("declaration", name) for name in declarations]
    )
    batches: list[tuple[tuple[str, ...], tuple[str, ...]]] = []
    for start in range(0, len(roots), DRAFT_SEMANTIC_PREFLIGHT_MAX_ROOTS_PER_BATCH):
        batch = roots[start : start + DRAFT_SEMANTIC_PREFLIGHT_MAX_ROOTS_PER_BATCH]
        batches.append(
            (
                tuple(name for kind, name in batch if kind == "specification"),
                tuple(name for kind, name in batch if kind == "declaration"),
            )
        )
    return tuple(batches)


def _merge_draft_display_target(
    targets: dict[str, Mapping[str, Any]],
    declaration: str,
    target: Mapping[str, Any],
    *,
    target_kind: str,
) -> None:
    """Merge one Lean-owned display while rejecting inconsistent batch output."""

    existing = targets.get(declaration)
    if existing is not None and existing != target:
        raise DraftSemanticPreflightError(
            f"Lean returned conflicting {target_kind} displays for `{declaration}`"
        )
    targets[declaration] = target


def _draft_dependency_display(
    declaration: str, target: Mapping[str, Any]
) -> dict[str, Any]:
    """Preserve owner semantics, excluding batch-relative traversal roles."""

    display = str(target.get("display") or "").strip()
    digest = str(target.get("display_sha256") or "").strip()
    if not display or len(digest) != 64:
        raise DraftSemanticPreflightError(
            f"Lean returned an incomplete dependency display for `{declaration}`"
        )
    # A theorem may be an explicit semantic root in one bounded request and
    # an erased proof argument in another. Its owner display is invariant;
    # the traversal's direct-dependency and proof-role lists are not. Keep
    # the native display, kind, expansion flag, signature and source locator.
    return {
        key: value
        for key, value in target.items()
        if key not in {
            "direct_paper_declarations",
            "direct_library_declarations",
            "erased_proof_declarations",
        }
    }


def _run_bounded_draft_display_surface(
    *,
    root: Path,
    entry_module: str,
    specifications: tuple[str, ...],
    declarations: tuple[str, ...],
    paper_modules: tuple[str, ...],
    provider: RepositoryBuildInputSnapshotProvider,
) -> dict[str, dict[str, Mapping[str, Any]]]:
    """Collect every requested display through bounded, non-evidence Lean calls.

    This function is intentionally not a graph cache or evidence issuer.  It
    requests the same complete set of source-facing roots as the former single
    call, but bounds the *display* request so one pathological paper cannot
    consume the host before its interface can be repaired.  The first request
    checks the import target; all later requests share the same frozen provider
    and therefore only elaborate their bounded display roots.
    """

    specification_targets: dict[str, Mapping[str, Any]] = {}
    paper_targets: dict[str, Mapping[str, Any]] = {}
    library_targets: dict[str, Mapping[str, Any]] = {}
    paper_sources: dict[str, Mapping[str, Any]] = {}
    library_sources: dict[str, Mapping[str, Any]] = {}
    paper_dependency_targets: dict[str, Mapping[str, Any]] = {}
    library_dependency_targets: dict[str, Mapping[str, Any]] = {}
    batches = _draft_display_batches(specifications, declarations)
    if not batches:
        raise DraftSemanticPreflightError("draft semantic preflight has no display roots")
    for batch_index, (specification_batch, declaration_batch) in enumerate(batches):
        surface = run_lean_paper_semantic_review_graph(
            root,
            entry_module,
            specification_names=specification_batch,
            semantic_declaration_names=declaration_batch,
            semantic_review_claim_declaration_names=(),
            paper_modules=paper_modules,
            build_input_provider=provider,
            timeout_seconds=DRAFT_SEMANTIC_PREFLIGHT_DISPLAY_TIMEOUT_SECONDS,
            require_build=batch_index == 0,
        )
        if not surface:
            requested = specification_batch + declaration_batch
            raise DraftSemanticPreflightError(
                "Lean could not produce the bounded draft semantic review surface for "
                + ", ".join(f"`{name}`" for name in requested)
            )
        raw_specs = surface.get("specification_targets")
        raw_paper = surface.get("paper_declaration_targets")
        raw_library = surface.get("library_declaration_targets")
        raw_paper_sources = surface.get("paper_declaration_sources", {})
        raw_library_sources = surface.get("library_declaration_sources", {})
        if not isinstance(raw_specs, Mapping) or not isinstance(raw_paper, Mapping) or not isinstance(
            raw_library, Mapping
        ) or not isinstance(raw_paper_sources, Mapping) or not isinstance(
            raw_library_sources, Mapping
        ):
            raise DraftSemanticPreflightError(
                "Lean returned a malformed bounded draft semantic review surface"
            )
        if set(raw_specs) != set(specification_batch):
            raise DraftSemanticPreflightError(
                "Lean returned an incomplete Spec preflight batch"
            )
        for raw_targets, destination, other_owner in (
            (raw_paper, paper_dependency_targets, library_dependency_targets),
            (raw_library, library_dependency_targets, paper_dependency_targets),
        ):
            for declaration, target in raw_targets.items():
                if not isinstance(declaration, str) or not isinstance(target, Mapping):
                    raise DraftSemanticPreflightError(
                        "Lean returned a malformed dependency display"
                    )
                if declaration in other_owner:
                    raise DraftSemanticPreflightError(
                        "Lean returned conflicting paper/library ownership for "
                        f"`{declaration}`"
                    )
                _merge_draft_display_target(
                    destination,
                    declaration,
                    _draft_dependency_display(declaration, target),
                    target_kind="dependency",
                )
        for declaration in specification_batch:
            target = raw_specs.get(declaration)
            if not isinstance(target, Mapping):
                raise DraftSemanticPreflightError(
                    f"Lean returned no Spec display for `{declaration}`"
                )
            _merge_draft_display_target(
                specification_targets,
                declaration,
                target,
                target_kind="Spec",
            )
        for declaration in declaration_batch:
            paper_target = raw_paper.get(declaration)
            library_target = raw_library.get(declaration)
            if isinstance(paper_target, Mapping) == isinstance(library_target, Mapping):
                raise DraftSemanticPreflightError(
                    "Lean must return exactly one paper or library declaration display for "
                    f"`{declaration}`"
                )
            target = paper_target if isinstance(paper_target, Mapping) else library_target
            assert isinstance(target, Mapping)
            destination = paper_targets if isinstance(paper_target, Mapping) else library_targets
            source_records = (
                raw_paper_sources
                if isinstance(paper_target, Mapping)
                else raw_library_sources
            )
            source_record = source_records.get(declaration)
            if source_record is not None and not isinstance(source_record, Mapping):
                raise DraftSemanticPreflightError(
                    f"Lean returned a malformed exact declaration source for `{declaration}`"
                )
            _merge_draft_display_target(
                destination,
                declaration,
                target,
                target_kind="semantic declaration",
            )
            if isinstance(source_record, Mapping):
                source_destination = (
                    paper_sources
                    if isinstance(paper_target, Mapping)
                    else library_sources
                )
                _merge_draft_display_target(
                    source_destination,
                    declaration,
                    source_record,
                    target_kind="semantic declaration source",
                )
    if set(specification_targets) != set(specifications):
        raise DraftSemanticPreflightError("Lean returned an incomplete Spec preflight surface")
    if set(paper_targets) | set(library_targets) != set(declarations):
        raise DraftSemanticPreflightError(
            "Lean returned an incomplete semantic-declaration preflight surface"
        )
    return {
        "specification_targets": specification_targets,
        "paper_declaration_targets": paper_targets,
        "library_declaration_targets": library_targets,
        "paper_declaration_sources": paper_sources,
        "library_declaration_sources": library_sources,
        "paper_dependency_support": {
            name: target for name, target in sorted(paper_dependency_targets.items())
            if name not in declarations
        },
        "library_dependency_support": {
            name: target for name, target in sorted(library_dependency_targets.items())
            if name not in declarations
        },
    }


def _draft_statement_map(folder: Path) -> Mapping[str, Any]:
    """Read the author-curated map without acquiring an evidence transaction.

    This preflight is deliberately usable immediately after changing a source
    map or paper interface.  It must not demand a still-current receipt whose
    closure necessarily predates that edit.  The accepting closeout later
    snapshots and validates this same map under its normal evidence boundary.
    """

    path = folder / "audit" / "paper_statement_map.json"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise DraftSemanticPreflightError(
            "draft semantic preflight cannot read paper_statement_map.json"
        ) from exc
    if not isinstance(payload, Mapping):
        raise DraftSemanticPreflightError("paper statement map must be an object")
    return payload


def _source_items_by_declaration(
    source_map: Mapping[str, Any], routes: EvidenceRouteSet
) -> tuple[tuple[str, str, Mapping[str, Any]], ...]:
    """Return explicit source/declaration pairs from the typed route surface.

    A source-model declaration can faithfully represent several distinct
    printed source conditions.  The preflight must preserve each source-item
    comparison while asking Lean for the declaration's expanded target only
    once.  The typed route projection, rather than a reverse one-to-one
    declaration map, is the authority for those associations.
    """

    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise DraftSemanticPreflightError("paper statement map has no source items")
    pairs: list[tuple[str, str, Mapping[str, Any]]] = []
    for route in routes.routes:
        if route.route_kind is not RouteKind.SOURCE_SEMANTIC_DECLARATION:
            continue
        item = raw_items.get(route.source_item_id)
        if not isinstance(item, Mapping):
            raise DraftSemanticPreflightError(
                "source semantic declaration route has no source item"
            )
        for declaration in route.semantic_declarations:
            pairs.append((declaration, route.source_item_id, item))
    return tuple(sorted(pairs, key=lambda pair: (pair[0], pair[1])))


def _explicit_prerequisite_source_pairs(
    source_map: Mapping[str, Any],
) -> tuple[tuple[str, str, Mapping[str, Any]], ...]:
    """Return explicit source-mapped paper and library prerequisite roots.

    The accepting prerequisite lanes already use these exact curator-authored
    mappings. Preflight must retain the same roots before rendering a result
    Spec; otherwise Lean may inline a material source model until the pretty
    printer hides its premises. This reads the typed map only and never
    discovers declarations from Lean text or names.
    """

    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise DraftSemanticPreflightError("paper statement map has no source items")
    pairs: list[tuple[str, str, Mapping[str, Any]]] = []
    for field in (
        "paper_semantic_prerequisite_sources",
        "library_semantic_prerequisite_sources",
    ):
        raw_sources = source_map.get(field, {})
        if not isinstance(raw_sources, Mapping):
            raise DraftSemanticPreflightError(
                f"{field} must map Lean declaration names to source-item ids"
            )
        for raw_declaration, raw_source_item in raw_sources.items():
            declaration = str(raw_declaration or "").strip()
            source_item_id = str(raw_source_item or "").strip()
            if not declaration or not source_item_id:
                raise DraftSemanticPreflightError(
                    f"{field} must map nonempty Lean declaration names to "
                    "nonempty source-item ids"
                )
            source_item = raw_items.get(source_item_id)
            if not isinstance(source_item, Mapping):
                raise DraftSemanticPreflightError(
                    f"{field} names absent source item `{source_item_id}`"
                )
            pairs.append((declaration, source_item_id, source_item))
    return tuple(sorted(pairs, key=lambda pair: (pair[0], pair[1])))


def _deduplicated_declaration_source_pairs(
    pairs: tuple[tuple[str, str, Mapping[str, Any]], ...],
) -> tuple[tuple[str, str, Mapping[str, Any]], ...]:
    """Deduplicate identical typed declaration/source coordinates only."""

    selected: dict[tuple[str, str], tuple[str, str, Mapping[str, Any]]] = {}
    for declaration, source_item_id, source_item in pairs:
        coordinate = (declaration, source_item_id)
        existing = selected.get(coordinate)
        if existing is not None and existing[2] != source_item:
            raise DraftSemanticPreflightError(
                "same source declaration/source-item coordinate has conflicting "
                "statement-map records"
            )
        selected[coordinate] = (declaration, source_item_id, source_item)
    return tuple(selected[coordinate] for coordinate in sorted(selected))


def _source_material(
    *,
    folder: Path,
    repository_root: Path,
    source_item: Mapping[str, Any],
) -> tuple[str, str, list[dict[str, Any]]]:
    anchor_error = source_anchor_file_error(
        folder,
        source_item,
        repository_root=repository_root,
    )
    if anchor_error:
        raise DraftSemanticPreflightError(anchor_error)
    text, digest, source_error = source_semantic_input_bundle(
        source_item,
        require_context_roles=True,
    )
    if source_error:
        raise DraftSemanticPreflightError(source_error)
    raw_contexts = source_item.get("approved_review_contexts")
    if raw_contexts is None:
        contexts: list[dict[str, Any]] = []
    elif isinstance(raw_contexts, list) and all(
        isinstance(context, Mapping) for context in raw_contexts
    ):
        contexts = [dict(context) for context in raw_contexts]
    else:
        raise DraftSemanticPreflightError(
            "source item has malformed approved review contexts"
        )
    return text, digest, contexts


def _review_row(
    *,
    review_id: str,
    review_kind: str,
    declaration: str,
    source_item_id: str,
    source_item: Mapping[str, Any],
    lean_target: Mapping[str, Any],
    lean_declaration_source: Mapping[str, Any] | None = None,
    folder: Path,
    repository_root: Path,
) -> dict[str, Any]:
    source_text, source_sha256, approved_contexts = _source_material(
        folder=folder,
        repository_root=repository_root,
        source_item=source_item,
    )
    display = str(lean_target.get("display") or "").strip()
    display_sha256 = str(lean_target.get("display_sha256") or "").strip()
    if not display or len(display_sha256) != 64:
        raise DraftSemanticPreflightError(
            f"Lean returned no complete expanded semantic display for `{declaration}`"
        )
    if "⋯" in display:
        raise DraftSemanticPreflightError(
            f"Lean source-review target for `{declaration}` contains pretty-printer "
            "elision (`⋯`); expose a readable semantic Spec or source-mapped "
            "prerequisite before requesting a reviewer judgment"
        )
    corrected_target, corrected_target_error = approved_corrected_target_review_context(
        source_item
    )
    if corrected_target_error:
        raise DraftSemanticPreflightError(
            f"{source_item_id}: {corrected_target_error}"
        )
    row = {
        "review_id": review_id,
        "review_kind": review_kind,
        "declaration": declaration,
        "source_item": source_item_id,
        "source_statement": str(source_item.get("statement") or "").strip(),
        "source_input": source_text,
        "source_input_sha256": source_sha256,
        "approved_review_contexts": approved_contexts,
        "lean_expanded_target": display,
        "lean_expanded_target_sha256": display_sha256,
    }
    if corrected_target is not None:
        row["approved_corrected_target"] = corrected_target
    if lean_declaration_source is not None:
        declaration_source = str(lean_declaration_source.get("source") or "").strip()
        declaration_source_sha256 = str(
            lean_declaration_source.get("source_sha256") or ""
        ).strip()
        if not declaration_source or len(declaration_source_sha256) != 64:
            raise DraftSemanticPreflightError(
                f"Lean returned an incomplete exact declaration source for `{declaration}`"
            )
        row["lean_exact_declaration_source"] = declaration_source
        row["lean_exact_declaration_source_sha256"] = declaration_source_sha256
        row["lean_exact_declaration_source_module"] = str(
            lean_declaration_source.get("source_module") or ""
        ).strip()
        row["lean_exact_declaration_source_path"] = str(
            lean_declaration_source.get("source_path") or ""
        ).strip()
        raw_range = lean_declaration_source.get("source_range")
        if isinstance(raw_range, Mapping):
            row["lean_exact_declaration_source_range"] = dict(raw_range)
    return row


def build_draft_semantic_preflight(
    repository_root: Path,
    folder: Path,
) -> dict[str, Any]:
    """Build one stdout-only source/interface preflight from Lean's displays."""

    root = repository_root.resolve()
    paper_folder = folder.resolve()
    source_map = _draft_statement_map(paper_folder)
    try:
        routes = EvidenceRouteSet.from_source_map(source_map)
    except ObligationRouteError as exc:
        raise DraftSemanticPreflightError(
            "current statement map has invalid typed source routes: " + str(exc)
        ) from exc
    specifications = routes.result_specifications()
    if not specifications:
        raise DraftSemanticPreflightError("current statement map has no result Specs")
    declaration_sources = _deduplicated_declaration_source_pairs(
        _source_items_by_declaration(source_map, routes)
        + _explicit_prerequisite_source_pairs(source_map)
    )

    namespace = str(source_map.get("paper_interface_namespace") or "").strip()
    if not namespace:
        raise DraftSemanticPreflightError(
            "paper statement map has no paper_interface_namespace"
        )
    # Default to the paper's canonical aggregator. A curator may instead name
    # a source-only interface module when every selected source declaration is
    # available there. This keeps the repair-stage display independent of
    # unrelated proof implementation imports; final closeout still checks the
    # canonical paper root. Lean verifies the selected module's actual closure
    # rather than Python reconstructing import relationships.
    entry_module = str(
        source_map.get("semantic_preflight_import_module") or namespace
    ).strip()
    # Lean module names and declaration namespaces are separate coordinates.
    # The provider below resolves the configured module through Lean's actual
    # import closure; requiring a spelling prefix here would reject a sound
    # paper after a namespace-only library reorganization.
    # This live provider asks Lean for the current loaded-module boundary only
    # in memory.  It neither reads a historical receipt nor persists a new
    # one, so an interface repair can be reviewed before the accepting graph is
    # reacquired.
    provider = RepositoryBuildInputSnapshotProvider(root)
    source_snapshot = provider.repository_source_snapshot(entry_module)
    module_sources = {
        module: (path.resolve(), content)
        for module, path, content, _digest in source_snapshot
    }
    if not module_sources:
        raise DraftSemanticPreflightError("Lean import closure has no source modules")
    paper_modules = paper_module_names_from_sources(
        root,
        paper_folder,
        module_sources,
        required_entry_module=entry_module,
    )
    routes_by_specification = routes.result_route_by_specification()
    definition_review_declarations = {
        route.semantic_review_declaration
        for route in routes_by_specification.values()
        if getattr(
            route,
            "semantic_review_target_kind",
            SemanticReviewTargetKind.SPEC_PROPOSITION,
        )
        is SemanticReviewTargetKind.DEFINITION_DECLARATION
    }
    declarations = tuple(
        sorted(
            {
                *(declaration for declaration, _item_id, _item in declaration_sources),
                *definition_review_declarations,
            }
        )
    )
    surface = _run_bounded_draft_display_surface(
        root=root,
        entry_module=entry_module,
        specifications=specifications,
        declarations=declarations,
        paper_modules=paper_modules,
        provider=provider,
    )
    specification_targets = surface.get("specification_targets")
    paper_declaration_targets = surface.get("paper_declaration_targets")
    library_declaration_targets = surface.get("library_declaration_targets", {})
    paper_declaration_sources = surface.get("paper_declaration_sources", {})
    library_declaration_sources = surface.get("library_declaration_sources", {})
    if not isinstance(specification_targets, Mapping) or set(specification_targets) != set(
        specifications
    ):
        raise DraftSemanticPreflightError("Lean returned an incomplete Spec preflight surface")
    if not isinstance(paper_declaration_targets, Mapping) or not isinstance(
        library_declaration_targets, Mapping
    ):
        raise DraftSemanticPreflightError(
            "Lean returned an incomplete semantic-declaration preflight surface"
        )
    declaration_targets = paper_declaration_targets | library_declaration_targets
    declaration_sources_by_name = paper_declaration_sources | library_declaration_sources
    if set(declaration_targets) != set(declarations):
        raise DraftSemanticPreflightError(
            "Lean returned an incomplete semantic-declaration preflight surface"
        )

    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise DraftSemanticPreflightError("paper statement map has no source items")
    result_rows: list[dict[str, Any]] = []
    for specification in specifications:
        route = routes_by_specification[specification]
        item = raw_items.get(route.source_item_id)
        if not isinstance(item, Mapping):
            raise DraftSemanticPreflightError(
                f"source route for `{specification}` has no source item"
            )
        if getattr(
            route,
            "semantic_review_target_kind",
            SemanticReviewTargetKind.SPEC_PROPOSITION,
        ) is SemanticReviewTargetKind.DEFINITION_DECLARATION:
            target_declaration = route.semantic_review_declaration
            target = declaration_targets.get(target_declaration)
        else:
            target_declaration = None
            target = specification_targets.get(specification)
        if not isinstance(target, Mapping):
            raise DraftSemanticPreflightError(
                "Lean omitted preflight target for "
                f"`{route.semantic_review_declaration}`"
            )
        result_rows.append(
            _review_row(
                review_id="source-result:" + specification,
                review_kind="source_result_spec",
                declaration=specification,
                source_item_id=route.source_item_id,
                source_item=item,
                lean_target=target,
                lean_declaration_source=(
                    declaration_sources_by_name.get(target_declaration)
                    if target_declaration is not None
                    else None
                ),
                folder=paper_folder,
                repository_root=root,
            )
        )

    declaration_rows: list[dict[str, Any]] = []
    for declaration, item_id, item in declaration_sources:
        target = declaration_targets.get(declaration)
        if not isinstance(target, Mapping):
            raise DraftSemanticPreflightError(
                f"Lean omitted preflight declaration for `{declaration}`"
            )
        declaration_rows.append(
            _review_row(
                review_id="source-declaration:" + declaration + ":" + item_id,
                review_kind="source_model_or_definition",
                declaration=declaration,
                source_item_id=item_id,
                source_item=item,
                lean_target=target,
                lean_declaration_source=declaration_sources_by_name.get(declaration),
                folder=paper_folder,
                repository_root=root,
            )
        )
    if not provider.finalize_unchanged():
        raise DraftSemanticPreflightError(
            "paper sources changed while the draft semantic preflight was running"
        )
    return {
        "schema": DRAFT_SEMANTIC_PREFLIGHT_SCHEMA,
        "acceptance_credential": False,
        "non_evidence": True,
        "persisted": False,
        "paper": paper_folder.name,
        "semantic_preflight_import_module": entry_module,
        "reviewer_instruction": (
            "Use this only to repair the source map or Lean interface before graph "
            "acquisition. A context-isolated reviewer must return matches, mismatch, "
            "or uncertain for each row; for a row with an "
            "approved_corrected_target, it may return "
            "matches_approved_corrected_target only when the fully expanded Lean "
            "target matches that displayed approved correction. If an otherwise "
            "reasonable source-model "
            "interpretation needs maintainer confirmation, the reviewer may return "
            "needs_maintainer_clarification with the exact source passage, Lean "
            "reading, and affected scope. No verdict from this bundle is a ledger "
            "judgment or closeout evidence. Resolve named dependencies through "
            "lean_dependency_support: these are Lean-emitted owner displays, "
            "not additional source claims or standalone source-review rows."
        ),
        "source_result_rows": result_rows,
        "source_model_and_definition_rows": declaration_rows,
        "lean_dependency_support": {
            "paper_declarations": surface.get("paper_dependency_support", {}),
            "library_declarations": surface.get("library_dependency_support", {}),
        },
    }


def main(argv: list[str] | None = None) -> int:
    """Write the diagnostic preflight bundle selected by the closeout planner."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True, help="paper folder under papers/")
    args = parser.parse_args(argv)
    root = Path(__file__).resolve().parents[2]
    paper = root / "papers" / str(args.paper).strip()
    try:
        payload = build_draft_semantic_preflight(root, paper)
    except (DraftSemanticPreflightError, OSError, ValueError) as exc:
        print(f"draft-semantic-preflight: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


__all__ = [
    "DRAFT_SEMANTIC_PREFLIGHT_SCHEMA",
    "DraftSemanticPreflightError",
    "build_draft_semantic_preflight",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
