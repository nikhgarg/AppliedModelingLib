#!/usr/bin/env python3
"""Reissue selected raw-source-to-expanded-Spec screening rows.

This writer deliberately does not decide whether a source claim and a Lean
``Spec`` match.  A reviewer supplies an explicit verdict and explanation for
each selected row.  The command reconstructs the exact byte-pinned source
bundle and the exact transparent ``PaperInterface`` declaration, then replaces
only the hash-bound transport fields.  It refuses an unknown source row, a
thin/non-``Spec`` target, a missing source context role, or a verdict without
an explanation.

Use this after a source/context or PaperInterface change made an existing v11
screening stale.  It is a screening reissue, not a replacement for the
atom-level source-spec correspondence receipt or Lean proof endpoint.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import semantic_review_decision_queue as review_queue  # noqa: E402
from scripts.corrected_target_identity import (  # noqa: E402
    CORRECTED_TARGET_REVIEW_PROTOCOL,
    corrected_target_review_digest,
)
from scripts.current_closeout.review_surface import (  # noqa: E402
    load_current_v11_review_graph_projection,
)
from scripts.direct_semantic_review_binding import (  # noqa: E402
    APPROVED_CORRECTED_TARGET_MATCH,
    LEAN_TARGET_PROTOCOL as LEAN_PROTOCOL,
    SOURCE_INPUT_PROTOCOL as SOURCE_PROTOCOL,
    direct_current_identity_from_queue_context,
    reusable_direct_source_spec_judgment,
)
from scripts.lean_signature_manifest import (  # noqa: E402
    review_claim_target_text,
    validated_review_claim_atom_material,
)
from scripts.obligation_routes import (  # noqa: E402
    EvidenceRouteSet,
    ObligationRouteError,
)
from scripts.source_review_input import (  # noqa: E402
    source_anchor_file_error,
    source_semantic_input_bundle,
    statement_digest,
)
from scripts.v11_screening_contract import (  # noqa: E402
    V11_SCREENING_PROMPT_VERSION,
    V11_SCREENING_SCHEMA,
    validate_v11_screening_container,
)


SCREENING_RELATIVE = Path("audit") / "v11_raw_source_spec_screening.json"
SCREENING_SCHEMA = V11_SCREENING_SCHEMA
PROMPT_VERSION = V11_SCREENING_PROMPT_VERSION
VALID_VERDICTS = frozenset(
    {"matches", "mismatch", "uncertain", APPROVED_CORRECTED_TARGET_MATCH}
)


class ScreeningReissueError(ValueError):
    """Raised when a reissue request cannot be verified mechanically."""


def _reusable_screening_items(
    container: object,
    *,
    paper: str,
) -> Mapping[str, Any]:
    """Return rows only when their reviewer provenance can authorize reuse."""

    validation = validate_v11_screening_container(container, paper=paper)
    if not validation.usable_item_ledger or not isinstance(container, Mapping):
        return {}
    if not str(container.get("validator") or "").strip() or not str(
        container.get("validated_at") or ""
    ).strip():
        return {}
    items = container.get("items")
    return items if isinstance(items, Mapping) else {}


def _review_claim_atom_material(
    semantic_target: Mapping[str, Any],
) -> tuple[list[dict[str, Any]], str]:
    """Validate the exact atom surface emitted by Lean for source review."""

    try:
        return validated_review_claim_atom_material(semantic_target)
    except ValueError as exc:
        raise ScreeningReissueError(str(exc)) from exc


def source_review_target_text(semantic_target: Mapping[str, Any]) -> str:
    """Render one exact reviewer target without reparsing Lean syntax."""

    try:
        return review_claim_target_text(semantic_target)
    except ValueError as exc:
        raise ScreeningReissueError(str(exc)) from exc


def _load_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ScreeningReissueError(f"could not read {label}: {exc}") from exc
    if not isinstance(payload, dict):
        raise ScreeningReissueError(f"{label} must be a JSON object")
    return payload


def _decision_rows(path: Path, *, paper: str) -> dict[str, dict[str, Any]]:
    payload = _load_object(path, label="decision file")
    try:
        return review_queue.normalized_decisions(
            payload,
            paper=paper,
            valid_verdicts=VALID_VERDICTS,
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise ScreeningReissueError(str(exc)) from exc


def _result_routes_by_spec(source_map: Mapping[str, Any]) -> dict[str, Any]:
    """Return the exact typed source route for every source-facing Spec."""

    paper = str(source_map.get("paper") or "").strip()
    if not paper:
        raise ScreeningReissueError("paper statement map has no paper namespace")
    try:
        return EvidenceRouteSet.from_source_map(
            source_map
        ).result_route_by_specification()
    except ObligationRouteError as exc:
        raise ScreeningReissueError(
            "invalid typed source route surface: " + str(exc)
        ) from exc


def _records_by_spec(source_map: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise ScreeningReissueError("paper statement map has no items object")
    routes = _result_routes_by_spec(source_map)
    return {
        specification: dict(raw_items[route.source_item_id])
        for specification, route in routes.items()
    }


def decision_template(
    paper_dir: Path,
    source_map: Mapping[str, Any],
    semantic_targets: Mapping[str, Mapping[str, Any]],
    interface_items: Mapping[str, Mapping[str, Any]],
    *,
    selected_specifications: set[str] | None = None,
    supporting_declarations: Mapping[str, Mapping[str, Any]] | None = None,
    supporting_declaration_names_by_item: Mapping[str, tuple[str, ...]] | None = None,
) -> dict[str, Any]:
    """Create an exact raw-source-to-expanded-Spec review queue.

    The direct semantic lane reviews only the source claim and its transparent
    semantic target.  When the target takes a paper model or library object as
    a parameter, its bounded, Lean-owned semantic prerequisites are displayed
    as context so that the reviewer can assess the actual model rather than a
    bare identifier.  Those prerequisites retain their own review lane; they
    do not turn an unchanged source/Spec judgment into a whole-paper recheck.
    """

    routes = _result_routes_by_spec(source_map)
    if selected_specifications is not None:
        unknown = sorted(selected_specifications - set(routes))
        if unknown:
            raise ScreeningReissueError(
                "selected specification(s) are outside the typed source surface: "
                + ", ".join(unknown)
            )
        routes = {
            name: route
            for name, route in routes.items()
            if name in selected_specifications
        }
    expected = set(routes)
    missing_targets = sorted(expected - set(semantic_targets))
    missing_declarations = sorted(expected - set(interface_items))
    if missing_targets or missing_declarations:
        details: list[str] = []
        if missing_targets:
            details.append(
                "missing semantic targets: " + ", ".join(missing_targets[:4])
            )
        if missing_declarations:
            details.append(
                "missing PaperInterface declarations: "
                + ", ".join(missing_declarations[:4])
            )
        raise ScreeningReissueError(
            "current v11 review transaction is incomplete: " + "; ".join(details)
        )

    items: dict[str, Any] = {}
    material: dict[str, dict[str, Any]] = {}
    source_items = source_map.get("items")
    if not isinstance(source_items, Mapping):
        raise ScreeningReissueError("paper statement map has no items object")
    for specification, route in sorted(routes.items()):
        target = semantic_targets[specification]
        interface_item = interface_items[specification]
        source_record = source_items.get(route.source_item_id)
        if not isinstance(source_record, Mapping):
            raise ScreeningReissueError(
                f"{specification}: typed source record is unavailable"
            )
        declaration = str(interface_item.get("lean_statement") or "").strip()
        display = source_review_target_text(target)
        display_sha256 = hashlib.sha256(display.encode("utf-8")).hexdigest()
        _claim_atoms, claim_atoms_digest = _review_claim_atom_material(target)
        claim_manifest_digest = str(
            target.get("review_claim_manifest_sha256") or ""
        ).strip().lower()
        if not re.fullmatch(r"[0-9a-f]{64}", claim_manifest_digest):
            raise ScreeningReissueError(
                f"{specification}: Lean claim manifest identity is unavailable"
            )
        if not declaration:
            raise ScreeningReissueError(
                f"{specification}: exact declaration or expanded semantic target is unavailable"
            )
        items[specification] = {
            "source_item": route.source_item_id,
            "candidate_source_items": [route.source_item_id],
            "judgment": "",
            "reason": "",
        }
        material[specification] = {
            "semantic_target": display,
            "semantic_target_sha256": display_sha256,
            "declaration_source": declaration,
            "declaration_source_sha256": hashlib.sha256(
                declaration.encode("utf-8")
            ).hexdigest(),
            "review_claim_atoms_sha256": claim_atoms_digest,
            "review_claim_manifest_sha256": claim_manifest_digest,
            "lean_expanded_statement_sha256": str(
                target.get("display_sha256") or ""
            ).strip().lower(),
            "lean_target_protocol": str(
                target.get("lean_target_protocol") or LEAN_PROTOCOL
            ).strip(),
            "semantic_review_declaration": str(
                target.get("semantic_review_declaration") or specification
            ).strip(),
            "coverage_status": str(
                source_record.get("coverage_status") or ""
            ).strip(),
            "corrected_target_sha256": str(
                (
                    source_record.get("corrected_target")
                    if isinstance(source_record.get("corrected_target"), Mapping)
                    else {}
                ).get("corrected_target_sha256")
                or ""
            ).strip().lower(),
        }
        if isinstance(source_record.get("corrected_target"), Mapping):
            material[specification]["corrected_target_review_sha256"] = (
                corrected_target_review_digest(source_record["corrected_target"])
            )

    payload = {
        "schema": 1,
        "paper": paper_dir.name,
        "items": items,
    }
    try:
        return review_queue.enrich_queue(
            payload,
            paper_dir=paper_dir,
            source_map=source_map,
            material_by_name=material,
            semantic_target_field="semantic_target",
            semantic_target_sha256_field="semantic_target_sha256",
            declaration_source_field="declaration_source",
            declaration_source_sha256_field="declaration_source_sha256",
            declaration_identity_fields=(
                "review_claim_atoms_sha256",
                "review_claim_manifest_sha256",
                "lean_expanded_statement_sha256",
                "lean_target_protocol",
                "semantic_review_declaration",
                "coverage_status",
                "corrected_target_sha256",
            ),
            optional_declaration_identity_fields=(
                "corrected_target_review_sha256",
            ),
            supporting_declarations=supporting_declarations,
            supporting_declaration_names_by_item=supporting_declaration_names_by_item,
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise ScreeningReissueError(str(exc)) from exc


def _template_output_path(paper_dir: Path, raw_path: Path) -> Path:
    try:
        return review_queue.template_output_path(
            paper_dir, raw_path, repository_root=ROOT
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise ScreeningReissueError(str(exc)) from exc


def _content_addressed_queue_path(
    paper_dir: Path, payload: Mapping[str, Any]
) -> Path:
    try:
        return review_queue.content_addressed_queue_path(
            paper_dir,
            payload,
            filename_prefix="v11_raw_source_spec_reissue_decisions_",
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise ScreeningReissueError(str(exc)) from exc


def _validated_current_review_targets(
    paper_dir: Path,
    review_graph: Any,
) -> tuple[Mapping[str, Any], Mapping[str, Any]]:
    """Validate and expose the exact current graph transaction."""

    source_map = review_graph.context.statement_map
    if review_graph.context.folder != paper_dir.resolve():
        raise ScreeningReissueError(
            "current v11 review transaction belongs to a different paper"
        )
    review_targets = review_graph.target_material()
    specifications = sorted(_result_routes_by_spec(source_map))
    semantic_targets = review_targets.get("semantic_targets")
    if not isinstance(semantic_targets, Mapping) or set(semantic_targets) != set(
        specifications
    ):
        raise ScreeningReissueError(
            "the current v11 review graph has an incomplete specifications surface"
        )
    return source_map, review_targets


def _paperinterface_items_from_review_targets(
    review_targets: Mapping[str, Any],
    *,
    expected_specifications: set[str],
) -> dict[str, dict[str, Any]]:
    """Adapt graph-owned exact declaration slices to the legacy writer shape."""

    raw_sources = review_targets.get("paper_declaration_sources")
    if not isinstance(raw_sources, Mapping):
        raise ScreeningReissueError(
            "current v11 review graph has no exact paper declaration sources"
        )
    items: dict[str, dict[str, Any]] = {}
    for name in sorted(expected_specifications):
        raw = raw_sources.get(name)
        if not isinstance(raw, Mapping):
            raise ScreeningReissueError(
                f"{name}: current v11 review graph has no exact declaration source"
            )
        statement = str(raw.get("paper_declaration_source") or "").strip()
        kind = str(raw.get("paper_declaration_kind") or "").strip()
        if not statement or not kind:
            raise ScreeningReissueError(
                f"{name}: current v11 declaration source is incomplete"
            )
        items[name] = {"kind": kind, "lean_statement": statement}
    return items


def _direct_review_support(
    review_targets: Mapping[str, Any],
    semantic_targets: Mapping[str, Any],
    *,
    selected_specifications: set[str] | None = None,
) -> tuple[dict[str, dict[str, Any]] | None, dict[str, tuple[str, ...]] | None]:
    """Return per-claim bounded prerequisite displays for a direct review card.

    Lean has already selected these direct semantic prerequisites in the
    unified graph.  Python only projects their bounded dependency context for
    presentation; it neither parses nor normalizes Lean. Non-routed semantic
    helpers remain exact display/code context, not independent judgment rows.
    A source-routed prerequisite is not a display cutoff: its body may still
    refer to material constructors needed to interpret this result's model.
    """

    paper_targets = review_targets.get("paper_prerequisite_targets")
    library_targets = review_targets.get("library_semantic_targets")
    if not isinstance(paper_targets, Mapping) or not isinstance(library_targets, Mapping):
        raise ScreeningReissueError(
            "current v11 review graph has malformed prerequisite targets"
        )
    selected = (
        set(semantic_targets)
        if selected_specifications is None
        else set(selected_specifications)
    )
    unknown_specs = sorted(selected - set(semantic_targets))
    if unknown_specs:
        raise ScreeningReissueError(
            "direct-review support names specification(s) outside the current graph: "
            + ", ".join(unknown_specs[:4])
        )
    known_prerequisites = set(paper_targets) | set(library_targets)
    roots_by_spec: dict[str, tuple[str, ...]] = {}
    all_roots: set[str] = set()
    for specification in sorted(selected):
        raw_target = semantic_targets.get(specification)
        if not isinstance(raw_target, Mapping):
            raise ScreeningReissueError(
                f"{specification}: current semantic target is malformed"
            )
        root_lists = [
            raw_target.get(field, ())
            for field in ("prerequisite_declarations", "library_declarations")
        ]
        if not all(isinstance(names, (list, tuple)) for names in root_lists):
            raise ScreeningReissueError(
                f"{specification}: Lean prerequisite surface is malformed"
            )
        roots = tuple(
            sorted({
                str(name).strip()
                for names in root_lists for name in names if str(name).strip()
            })
        )
        unknown_roots = sorted(set(roots) - known_prerequisites)
        if unknown_roots:
            raise ScreeningReissueError(
                f"{specification}: Lean prerequisite display is unavailable for "
                + ", ".join(unknown_roots[:4])
            )
        roots_by_spec[specification] = roots
        all_roots.update(roots)
    if not all_roots:
        return None, None
    try:
        support, names_by_root = review_queue.review_support_from_targets(
            review_targets,
            root_declarations=all_roots,
            include_nearest_source_use_context=False,
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise ScreeningReissueError(str(exc)) from exc
    names_by_spec = {
        specification: tuple(
            sorted(
                {
                    name
                    for root in roots
                    for name in names_by_root.get(root, ())
                }
            )
        )
        for specification, roots in roots_by_spec.items()
    }
    return support, names_by_spec


def _current_decision_template(
    paper_dir: Path,
    *,
    source_map: Mapping[str, Any],
    review_targets: Mapping[str, Any],
    selected_specifications: set[str] | None = None,
) -> dict[str, Any]:
    """Build the exact-current direct queue with Lean-owned model context."""

    semantic_targets = review_targets.get("semantic_targets", {})
    if not isinstance(semantic_targets, Mapping):
        raise ScreeningReissueError("current v11 review graph has no semantic targets")
    interface_items = _paperinterface_items_from_review_targets(
        review_targets,
        expected_specifications=set(_result_routes_by_spec(source_map)),
    )
    support, names_by_spec = _direct_review_support(
        review_targets,
        semantic_targets,
        selected_specifications=selected_specifications,
    )
    return decision_template(
        paper_dir,
        source_map,
        semantic_targets,
        interface_items,
        selected_specifications=selected_specifications,
        supporting_declarations=support,
        supporting_declaration_names_by_item=names_by_spec,
    )


def current_decision_template_and_path(
    paper_dir: Path,
    *,
    review_graph: Any,
) -> tuple[dict[str, Any], Path]:
    """Build this exact review queue and give it a content-addressed path."""

    source_map, review_targets = _validated_current_review_targets(
        paper_dir, review_graph
    )
    payload = _current_decision_template(
        paper_dir,
        source_map=source_map,
        review_targets=review_targets,
    )
    return payload, _content_addressed_queue_path(paper_dir, payload)


def _unchanged_screening_judgment(
    prior: object,
    *,
    declaration_context: Mapping[str, Any],
    source_context: Mapping[str, Any],
) -> bool:
    """Recognize reviewer authority only through exact durable semantics.

    The prior row records the literal declaration, target rendering, and
    Lean-owned claim roles shown to the reviewer.  Declaration and role/atom
    views remain useful issuance provenance and coverage diagnostics, but they
    are not the reuse identity: the reviewer has judged the verbatim source
    bundle against the full Lean-expanded proposition.  Requiring a derived
    atom view to remain byte-identical would schedule a new judgment for an
    unchanged proposition whenever presentation or coverage bookkeeping
    changes.

    Reuse therefore retains the exact verbatim source bundle, target protocol,
    full Lean-expanded target, verdict, and corrected-target disposition.  A
    changed premise, conclusion, source excerpt, protocol, or correction still
    fails closed.  The current graph independently validates the atom and
    manifest surface before this binding is consulted.
    """

    current = direct_current_identity_from_queue_context(
        declaration_context=declaration_context,
        source_context=source_context,
    )
    return bool(
        current
        and reusable_direct_source_spec_judgment(prior, current) is not None
    )


def _current_screening_reuse_bindings(
    queue: Mapping[str, Any],
    existing_items: Mapping[str, Any],
) -> dict[str, tuple[str, dict[str, str]]]:
    """Resolve current source/Spec rows to prior judgments without names."""

    review_material = queue.get("review_material")
    if not isinstance(review_material, Mapping):
        raise ScreeningReissueError("current v11 queue has no review material")
    declarations = review_material.get("declarations")
    sources = review_material.get("source_items")
    items = queue.get("items")
    if (
        not isinstance(declarations, Mapping)
        or not isinstance(sources, Mapping)
        or not isinstance(items, Mapping)
    ):
        raise ScreeningReissueError("current v11 queue review material is malformed")

    current_entries: dict[str, Mapping[str, Any]] = {}
    for raw_name, raw_item in items.items():
        name = str(raw_name or "").strip()
        if not name or not isinstance(raw_item, Mapping):
            continue
        source_item = str(raw_item.get("source_item") or "").strip()
        declaration_context = declarations.get(name)
        source_context = sources.get(source_item)
        if not isinstance(declaration_context, Mapping) or not isinstance(
            source_context, Mapping
        ):
            continue
        current_entries[name] = {
            "declaration_context": declaration_context,
            "source_context": source_context,
        }

    def reusable(
        prior: object, entry: Mapping[str, Any]
    ) -> dict[str, str] | None:
        declaration_context = entry.get("declaration_context")
        source_context = entry.get("source_context")
        if not isinstance(declaration_context, Mapping) or not isinstance(
            source_context, Mapping
        ):
            return None
        if not _unchanged_screening_judgment(
            prior,
            declaration_context=declaration_context,
            source_context=source_context,
        ):
            return None
        assert isinstance(prior, Mapping)
        return {
            "judgment": str(prior.get("judgment") or "").strip(),
            "reason": str(prior.get("reason") or "").strip(),
        }

    return review_queue.unique_reusable_judgment_bindings(
        current_entries,
        existing_items,
        reusable_judgment=reusable,
    )


def current_changed_decision_template_and_path(
    paper_dir: Path,
    *,
    review_graph: Any,
) -> tuple[dict[str, Any], Path] | None:
    """Return only current source/Spec rows lacking reusable exact judgments."""

    source_map, review_targets = _validated_current_review_targets(
        paper_dir, review_graph
    )
    full = _current_decision_template(
        paper_dir,
        source_map=source_map,
        review_targets=review_targets,
    )
    current_path = paper_dir / SCREENING_RELATIVE
    current = (
        _load_object(current_path, label="current v11 screening")
        if current_path.is_file()
        else {}
    )
    existing_items = _reusable_screening_items(
        current,
        paper=paper_dir.name,
    )
    bindings = _current_screening_reuse_bindings(
        full,
        existing_items,
    )
    changed = set(full["items"]) - set(bindings)
    if not changed:
        return None
    payload = _current_decision_template(
        paper_dir,
        source_map=source_map,
        review_targets=review_targets,
        selected_specifications=changed,
    )
    return payload, _content_addressed_queue_path(paper_dir, payload)


def _matching_legacy_current_queue(
    paper_dir: Path,
    *,
    template: Mapping[str, Any],
) -> Mapping[str, Any] | None:
    """Return the former fixed-name queue only when its review bytes match.

    The filename was operational, not evidence.  A closeout may have paused
    after a reviewer filled that queue but before the screening ledger was
    issued.  Moving to content-addressed queues must not erase that completed
    work.  Reuse is therefore based on the exact embedded source/Lean material
    and typed route projection, never on the old filename or engine revision.
    """

    path = paper_dir / "audit" / "v11_raw_source_spec_reissue_decisions.json"
    if not path.is_file():
        return None
    if current_decision_queue_error(
        path,
        template=template,
        paper=paper_dir.name,
    ):
        return None
    return _load_object(path, label="legacy current v11 review queue")


def _queue_route_projection(payload: Mapping[str, Any]) -> dict[str, Any]:
    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        return {}
    return {
        str(name): {
            "source_item": str(raw.get("source_item") or "").strip(),
            "candidate_source_items": sorted(
                str(item).strip()
                for item in raw.get("candidate_source_items", ())
                if str(item).strip()
            ),
        }
        for name, raw in raw_items.items()
        if str(name).strip() and isinstance(raw, Mapping)
    }


def current_decision_queue_error(
    path: Path,
    *,
    template: Mapping[str, Any],
    paper: str,
) -> str:
    """Validate an existing content-addressed queue without judging its rows."""

    try:
        payload = _load_object(path, label="current v11 review queue")
        review_queue.validated_queue_items(payload, paper=paper)
        if (
            payload.get("review_material_sha256")
            != template.get("review_material_sha256")
            or _queue_route_projection(payload) != _queue_route_projection(template)
        ):
            raise ScreeningReissueError(
                "saved queue does not match the current typed review surface"
            )
    except (
        OSError,
        ScreeningReissueError,
        review_queue.SemanticReviewDecisionQueueError,
    ) as exc:
        return str(exc)
    return ""


def reissued_row(
    full_name: str,
    *,
    paper_dir: Path,
    source_item: str,
    record: Mapping[str, Any],
    interface_item: Mapping[str, Any],
    semantic_target: Mapping[str, Any],
    decision: Mapping[str, Any],
    current_support_sha256: str | None = None,
) -> dict[str, object]:
    """Construct one current v11 row from an explicit reviewer decision."""

    source_error = source_anchor_file_error(paper_dir, record)
    if source_error:
        raise ScreeningReissueError(
            f"{full_name}: raw source bundle is invalid: {source_error}"
        )
    source_text, source_digest, source_error = source_semantic_input_bundle(
        record, require_context_roles=True
    )
    if source_error or not source_text or not source_digest:
        raise ScreeningReissueError(f"{full_name}: raw source bundle is invalid: {source_error}")
    lean_text = str(interface_item.get("lean_statement") or "")
    expanded_text = str(semantic_target.get("display") or "")
    expanded_digest = str(semantic_target.get("display_sha256") or "").strip().lower()
    review_target_text = source_review_target_text(semantic_target)
    review_target_digest = hashlib.sha256(
        review_target_text.encode("utf-8")
    ).hexdigest()
    _claim_atoms, claim_atoms_digest = _review_claim_atom_material(semantic_target)
    claim_manifest_digest = str(
        semantic_target.get("review_claim_manifest_sha256") or ""
    ).strip().lower()
    interface_digest = str(
        semantic_target.get("paper_interface_sha256") or ""
    ).strip().lower()
    if (
        not lean_text
        or not expanded_text
        or not re.fullmatch(r"[0-9a-f]{64}", expanded_digest)
        or not re.fullmatch(r"[0-9a-f]{64}", claim_manifest_digest)
        or not re.fullmatch(r"[0-9a-f]{64}", interface_digest)
        or not full_name.endswith("Spec")
        or str(interface_item.get("kind") or "") != "def"
        or re.search(r":\s*Prop\s*:=", lean_text, flags=re.DOTALL) is None
    ):
        raise ScreeningReissueError(
            f"{full_name}: the semantic target must be one explicit `def ...Spec : Prop :=` in PaperInterface"
        )
    if str(decision.get("source_item") or "").strip() != source_item:
        raise ScreeningReissueError(
            f"{full_name}: reviewed source item does not match the current typed route"
        )
    try:
        review_queue.validate_current_identity(
            full_name,
            decision,
            {
                "semantic_target_sha256": review_target_digest,
                "declaration_source_sha256": hashlib.sha256(
                    lean_text.encode("utf-8")
                ).hexdigest(),
                "source_input_bundle_sha256": source_digest,
                "verbatim_source_input": source_text,
                **(
                    {"semantic_supporting_declarations_sha256": current_support_sha256}
                    if current_support_sha256 is not None else {}
                ),
            },
            semantic_target_sha256_field="semantic_target_sha256",
            declaration_source_sha256_field="declaration_source_sha256",
            declaration_identity={
                "review_claim_atoms_sha256": claim_atoms_digest,
                "review_claim_manifest_sha256": claim_manifest_digest,
                "lean_expanded_statement_sha256": expanded_digest,
                "lean_target_protocol": str(
                    semantic_target.get("lean_target_protocol") or LEAN_PROTOCOL
                ).strip(),
                "semantic_review_declaration": str(
                    semantic_target.get("semantic_review_declaration") or full_name
                ).strip(),
                "coverage_status": str(
                    record.get("coverage_status") or ""
                ).strip(),
                "corrected_target_sha256": str(
                    (
                        record.get("corrected_target")
                        if isinstance(record.get("corrected_target"), Mapping)
                        else {}
                    ).get("corrected_target_sha256")
                    or ""
                ).strip().lower(),
                **(
                    {
                        "corrected_target_review_sha256": corrected_target_review_digest(
                            record["corrected_target"]
                        )
                    }
                    if isinstance(record.get("corrected_target"), Mapping)
                    else {}
                ),
            },
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise ScreeningReissueError(str(exc)) from exc
    verdict = str(decision["judgment"])
    corrected_target = record.get("corrected_target")
    approved_correction = verdict == APPROVED_CORRECTED_TARGET_MATCH
    is_corrected_source_statement = (
        str(record.get("coverage_status") or "").strip()
        == "corrected_source_statement"
    )
    if approved_correction:
        if (
            str(record.get("coverage_status") or "").strip()
            != "corrected_source_statement"
            or not isinstance(corrected_target, Mapping)
            or corrected_target.get("archival_equivalence_claimed") is not False
            or not str(corrected_target.get("corrected_target_sha256") or "").strip()
            or corrected_target_review_digest(corrected_target)
            != str(
                corrected_target.get("corrected_target_review_sha256")
                or corrected_target_review_digest(corrected_target)
            ).strip().lower()
        ):
            raise ScreeningReissueError(
                f"{full_name}: approved-corrected-target judgment requires a current "
                "corrected_source_statement map record"
            )
    elif is_corrected_source_statement:
        raise ScreeningReissueError(
            f"{full_name}: a corrected_source_statement retains different archival "
            "text and therefore requires the "
            "`matches_approved_corrected_target` verdict"
        )
    row: dict[str, object] = {
        "judgment": verdict,
        "reason": str(decision["reason"]),
        "source_item": source_item,
        "source_input_protocol": SOURCE_PROTOCOL,
        "source_input_bundle_sha256": source_digest,
        # The semantic target is the literal source text shown to the
        # reviewer.  The distinct bundle digest binds that text to its exact
        # anchors and permitted context.
        "paper_statement_sha256": statement_digest(source_text),
        "lean_target_protocol": str(
            semantic_target.get("lean_target_protocol") or LEAN_PROTOCOL
        ).strip(),
        "semantic_target_declaration": full_name,
        "lean_expanded_statement_sha256": expanded_digest,
        "review_claim_manifest_sha256": claim_manifest_digest,
        "review_claim_atoms_sha256": claim_atoms_digest,
        "source_review_target_sha256": review_target_digest,
        "paper_interface_sha256": interface_digest,
    }
    semantic_review_declaration = str(
        semantic_target.get("semantic_review_declaration") or full_name
    ).strip()
    if semantic_review_declaration != full_name:
        row["semantic_review_declaration"] = semantic_review_declaration
    if approved_correction:
        assert isinstance(corrected_target, Mapping)
        row["corrected_target_protocol"] = CORRECTED_TARGET_REVIEW_PROTOCOL
        row["corrected_target_review_sha256"] = corrected_target_review_digest(
            corrected_target
        )
    return row


def reissue(
    paper_dir: Path,
    decisions: Mapping[str, Mapping[str, Any]],
    *,
    validator: str,
    replace_current_surface: bool = False,
    review_graph: Any,
) -> dict[str, Any]:
    source_map, review_targets = _validated_current_review_targets(
        paper_dir, review_graph
    )
    interface_items = _paperinterface_items_from_review_targets(
        review_targets,
        expected_specifications=set(_result_routes_by_spec(source_map)),
    )
    records = _records_by_spec(source_map)
    routes = _result_routes_by_spec(source_map)
    semantic_targets = {
        name: dict(review_graph.semantic_targets[name])
        for name in records
        if name in review_graph.semantic_targets
    }
    current_path = paper_dir / SCREENING_RELATIVE
    current = (
        _load_object(current_path, label="current v11 screening")
        if current_path.is_file()
        else {}
    )
    existing_items = _reusable_screening_items(
        current,
        paper=paper_dir.name,
    )
    full_queue = _current_decision_template(
        paper_dir,
        source_map=source_map,
        review_targets=review_targets,
    )
    try:
        current_queue_rows = review_queue.validated_queue_items(
            full_queue,
            paper=paper_dir.name,
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise ScreeningReissueError(str(exc)) from exc
    bindings = _current_screening_reuse_bindings(full_queue, existing_items)
    expected = set(records)
    extra = sorted(set(decisions) - expected)
    missing = sorted(expected - set(decisions) - set(bindings))
    if extra or missing:
        details: list[str] = []
        if missing:
            details.append(
                "missing decisions for new or semantically changed Specs: "
                + ", ".join(missing)
            )
        if extra:
            details.append(
                "out-of-surface decision(s) for " + ", ".join(extra)
            )
        raise ScreeningReissueError(
            "current Spec decision coverage is not exact: " + "; ".join(details)
        )
    if replace_current_surface:
        if set(decisions) != expected:
            missing = sorted(expected - set(decisions))
            extra = sorted(set(decisions) - expected)
            details: list[str] = []
            if missing:
                details.append("missing decision(s) for " + ", ".join(missing))
            if extra:
                details.append("out-of-surface decision(s) for " + ", ".join(extra))
            raise ScreeningReissueError(
                "--replace-current-surface requires exact current Spec decisions: "
                + "; ".join(details)
            )
    items: dict[str, object] = {}
    for full_name in sorted(expected):
        record = records[full_name]
        interface_item = interface_items.get(full_name)
        semantic_target = semantic_targets.get(full_name)
        if interface_item is None:
            raise ScreeningReissueError(f"{full_name}: no transparent PaperInterface Spec declaration")
        if semantic_target is None:
            raise ScreeningReissueError(
                f"{full_name}: Lean could not produce a complete transparent semantic target"
            )
        decision = decisions.get(full_name)
        prior_review_target = ""
        if decision is None:
            prior_name, reviewer = bindings[full_name]
            prior = existing_items[prior_name]
            assert isinstance(prior, Mapping)
            prior_review_target = str(
                prior.get("source_review_target_sha256") or ""
            ).strip().lower()
            decision = {
                **current_queue_rows[full_name],
                "judgment": reviewer["judgment"],
                "reason": reviewer["reason"],
            }
        row = reissued_row(
            full_name,
            paper_dir=paper_dir,
            source_item=routes[full_name].source_item_id,
            record=record,
            interface_item=interface_item,
            semantic_target=semantic_target,
            decision=decision,
            current_support_sha256=str(
                current_queue_rows[full_name].get(
                    "_reviewed_supporting_declarations_sha256"
                ) or ""
            ),
        )
        # Preserve the exact renderer trace the prior reviewer actually saw.
        # It is issuance provenance, not the current semantic reuse identity.
        # The current expanded Lean digest and claim atoms above are still
        # regenerated and checked independently.
        if re.fullmatch(r"[0-9a-f]{64}", prior_review_target):
            row["source_review_target_sha256"] = prior_review_target
        items[full_name] = row
    effective_validator = (
        validator.strip()
        if decisions
        else str(current.get("validator") or "").strip()
    )
    effective_validated_at = (
        datetime.now(timezone.utc).replace(microsecond=0).isoformat()
        if decisions
        else str(current.get("validated_at") or "").strip()
    )
    if not effective_validator or not effective_validated_at:
        raise ScreeningReissueError(
            "structural refresh requires the prior screening reviewer provenance"
        )
    return {
        "schema": SCREENING_SCHEMA,
        "paper": paper_dir.name,
        "audit_kind": "raw_source_to_expanded_spec_screening",
        "prompt_version": PROMPT_VERSION,
        "validator": effective_validator,
        "validated_at": effective_validated_at,
        "comment": (
            "Each listed verdict compares the exact byte-pinned source-anchor bundle "
            "and explicitly pinned semantic context with Lean's fully expanded "
            "paper-local semantic target and Lean-elaborated parameter, premise, and "
            "conclusion roles. The paired proof endpoint is reviewed separately."
        ),
        "items": dict(sorted(items.items())),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--decisions", type=Path)
    mode.add_argument(
        "--emit-template",
        type=Path,
        help=(
            "write a self-contained non-evidence decision queue from the "
            "exact-current v11 review graph"
        ),
    )
    mode.add_argument(
        "--emit-current-template",
        action="store_true",
        help=(
            "write or reuse the content-addressed non-evidence queue for the "
            "exact-current unified graph and source surface"
        ),
    )
    mode.add_argument(
        "--refresh-current",
        action="store_true",
        help=(
            "rewrite only current routing and renderer provenance while reusing "
            "every uniquely matched source/Spec semantic judgment"
        ),
    )
    parser.add_argument("--validator", default="")
    parser.add_argument(
        "--replace-current-surface",
        action="store_true",
        help=(
            "require decisions for every current selected Spec and replace the screening "
            "ledger, removing rows from a retired review surface"
        ),
    )
    parser.add_argument(
        "--v11-review-graph",
        action="store_true",
        help=(
            "use the exact current builder-issued v11 graph targets; this loads "
            "no dashboard cache and launches no Lean discovery"
        ),
    )
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    if not args.v11_review_graph:
        raise ScreeningReissueError(
            "current semantic-review writing requires --v11-review-graph"
        )
    review_graph = load_current_v11_review_graph_projection(root, paper_dir)
    if review_graph is None:
        raise ScreeningReissueError(
            "no exact-current v11 review graph; prepare the unified graph first"
        )
    if args.emit_current_template:
        if args.write or args.validator.strip() or args.replace_current_surface:
            raise ScreeningReissueError(
                "--emit-current-template cannot be combined with --write, --validator, "
                "or --replace-current-surface"
            )
        delta = current_changed_decision_template_and_path(
            paper_dir,
            review_graph=review_graph,
        )
        if delta is None:
            print(
                f"{args.paper}: every current v11 source/Spec judgment is reusable"
            )
            return 0
        payload, path = delta
        if path.is_file():
            error = current_decision_queue_error(
                path,
                template=payload,
                paper=args.paper,
            )
            if error:
                raise ScreeningReissueError(
                    "existing content-addressed review queue is invalid: " + error
                )
            print(f"{args.paper}: reused current non-evidence v11 review queue {path}")
            return 0
        legacy = _matching_legacy_current_queue(
            paper_dir,
            template=payload,
        )
        if legacy is not None:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(
                json.dumps(legacy, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            print(
                f"{args.paper}: preserved exact prior reviewer work in "
                f"content-addressed queue {path}"
            )
            return 0
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        print(f"{args.paper}: wrote current non-evidence v11 review queue to {path}")
        return 0
    if args.emit_template is not None:
        if args.write or args.validator.strip() or args.replace_current_surface:
            raise ScreeningReissueError(
                "--emit-template cannot be combined with --write, --validator, "
                "or --replace-current-surface"
            )
        source_map, review_targets = _validated_current_review_targets(
            paper_dir, review_graph
        )
        payload = _current_decision_template(
            paper_dir,
            source_map=source_map,
            review_targets=review_targets,
        )
        path = _template_output_path(paper_dir, args.emit_template)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        print(f"{args.paper}: wrote non-evidence v11 review queue to {path}")
        return 0
    if args.refresh_current:
        if args.validator.strip() or args.replace_current_surface:
            raise ScreeningReissueError(
                "--refresh-current cannot be combined with --validator or "
                "--replace-current-surface"
            )
        payload = reissue(
            paper_dir,
            {},
            validator="",
            review_graph=review_graph,
        )
        if not args.write:
            print(
                f"{args.paper}: validated structural source/Spec refresh with all "
                f"{len(payload['items'])} semantic judgments reused; rerun with --write"
            )
            return 0
        path = paper_dir / SCREENING_RELATIVE
        path.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        print(
            f"{args.paper}: refreshed {path} with all "
            f"{len(payload['items'])} semantic judgments reused"
        )
        return 0
    if args.decisions is None or not args.validator.strip():
        raise ScreeningReissueError(
            "--decisions requires a nonempty --validator"
        )
    decisions = _decision_rows(args.decisions, paper=args.paper)
    payload = reissue(
        paper_dir,
        decisions,
        validator=args.validator.strip(),
        replace_current_surface=args.replace_current_surface,
        review_graph=review_graph,
    )
    if not args.write:
        print(f"{args.paper}: validated {len(decisions)} v11 screening decision(s); rerun with --write")
        return 0
    path = paper_dir / SCREENING_RELATIVE
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"{args.paper}: wrote {path} ({len(decisions)} reissued decision(s))")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ScreeningReissueError as exc:
        print(f"v11 screening reissue refused: {exc}", file=sys.stderr)
        raise SystemExit(1)
