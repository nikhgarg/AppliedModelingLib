#!/usr/bin/env python3
"""Render a human-review packet from already-prepared closeout data.

Lean graph acquisition belongs to the current closeout graph-preparation
action. This module may project an exact current graph into the packet
transport cache, but it never discovers declarations or starts Lean itself.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import re
import subprocess
import sys
from collections.abc import Iterable, Mapping
from pathlib import Path, PurePosixPath
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import human_review_packet_renderer as packet_renderer
from scripts.obligation_routes import EvidenceRouteSet, ObligationRouteError
from scripts.semantic_prerequisite_projection import (
    V11_DEFINITION_TARGET_PROTOCOL,  # noqa: F401 -- public packet schema API
    V11_LEAN_TARGET_PROTOCOL,
    selected_library_semantic_prerequisite_targets,
    selected_paper_semantic_prerequisite_targets,
)
from scripts.source_spec_protocol import raw_source_spec_screening_requested

TEMPLATE_PATH = Path(__file__).with_name("templates") / "HUMAN_REVIEW_PACKET.tex.in"
PACKET_NAME = "HUMAN_REVIEW_PACKET"

_RETAINED_REVIEW_QUEUE_STEMS = (
    "v11_raw_source_spec_reissue_decisions",
    "paper_semantic_prerequisite_reissue_decisions",
    "library_semantic_reissue_decisions",
)
_REVIEW_CLAIM_TARGET_PREFIX = "Expanded Lean semantic target:\n"
_REVIEW_CLAIM_ROLE_SEPARATOR = "\n\nLean-elaborated claim roles:\n"


def _review_surface_module():
    """Load the graph owner only for explicit graph projection or rendering."""

    from scripts.current_closeout import review_surface

    return review_surface


def _lean_source_tree_sha256(root: Path) -> str:
    """Hash the Lean source tree that can affect a cached display."""

    digest = hashlib.sha256()
    if not root.is_dir():
        return ""
    for path in sorted(root.rglob("*.lean")):
        if path.is_relative_to(root / "Audit"):
            continue
        relative = path.relative_to(root).as_posix().encode("utf-8")
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        contents = path.read_bytes()
        digest.update(len(contents).to_bytes(8, "big"))
        digest.update(contents)
    return digest.hexdigest()


def _write_packet_lean_cache(paper_dir: Path, payload: Mapping[str, Any]) -> None:
    review_surface = _review_surface_module()
    material = dict(payload)
    library_targets = material.get("library_semantic_targets")
    if not isinstance(library_targets, Mapping):
        raise ValueError("packet Lean cache has no library semantic targets")
    module_hashes = review_surface._library_semantic_source_modules_sha256(
        library_targets
    )
    if module_hashes is None:
        raise ValueError(
            "packet Lean cache cannot identify every reusable semantic target source"
        )
    material["library_semantic_source_modules_sha256"] = module_hashes
    review_surface._packet_lean_cache_path(paper_dir).write_text(
        json.dumps(material, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def _retained_review_queue_paths(paper_dir: Path) -> tuple[Path, ...]:
    """Return only this paper's registered review-material carrier families."""

    audit_dir = paper_dir / "audit"
    paths: set[Path] = set()
    for stem in _RETAINED_REVIEW_QUEUE_STEMS:
        for path in audit_dir.glob(f"{stem}*.json"):
            suffix = path.stem.removeprefix(stem)
            if (
                (not suffix or re.fullmatch(r"_[0-9a-f]{64}", suffix))
                and path.is_file()
                and not path.is_symlink()
            ):
                paths.add(path)
    return tuple(sorted(paths))


def _add_display_candidate(
    candidates: dict[str, set[str]], display: object
) -> None:
    if not isinstance(display, str) or not display.strip():
        return
    digest = hashlib.sha256(display.encode("utf-8")).hexdigest()
    candidates.setdefault(digest, set()).add(display)


def _retained_terminal_graph_display_candidates(
    paper_dir: Path,
) -> tuple[dict[str, set[str]], dict[tuple[str, str], set[str]]]:
    """Read display bytes from one validated terminal graph checkpoint.

    The checkpoint is operational transport, so its names and graph request
    grant no selection, judgment, or reuse authority. The accepted graph must
    still select every returned byte string by its recomputed display digest.
    """

    from scripts.closeout_content_store import load_closeout_object
    from scripts.current_closeout import lean_review_graph
    from scripts.lean_review_surface import (
        TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SCHEMA,
        TRANSPARENT_PAPER_DECLARATION_DISPLAY_SCHEMA,
        TRANSPARENT_PAPER_SPEC_DISPLAY_SCHEMA,
    )

    candidates: dict[str, set[str]] = {}
    source_modules: dict[tuple[str, str], set[str]] = {}
    try:
        index = json.loads(
            lean_review_graph._terminal_graph_checkpoint_index_path(
                ROOT, paper_dir
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
        reference = index.get("graph_reference") if isinstance(index, Mapping) else None
        if (
            not isinstance(index, Mapping)
            or set(index) != required
            or index.get("schema")
            != lean_review_graph.V11_TERMINAL_GRAPH_CHECKPOINT_SCHEMA
            or index.get("acceptance_credential") is not False
            or index.get("operational_scheduling_only") is not True
            or index.get("paper") != paper_dir.name
            or not isinstance(reference, Mapping)
        ):
            return candidates, source_modules
        carrier = load_closeout_object(
            ROOT,
            reference,
            expected_kind="v11_terminal_lean_review_graph",
        )
        graph_request = carrier.get("graph_request")
        context_sha256 = index.get("context_input_sha256")
        if not isinstance(graph_request, Mapping) or not isinstance(
            context_sha256, str
        ):
            return candidates, source_modules
        inventory = lean_review_graph._validated_operational_graph_carrier_inventory(
            carrier,
            paper=paper_dir.name,
            source_semantic_lane=(
                lean_review_graph.V11_TERMINAL_GRAPH_EVIDENCE_LANE
            ),
            context_input_sha256=context_sha256,
            graph_request=graph_request,
        )
        if inventory is None:
            return candidates, source_modules
    except (
        OSError,
        RuntimeError,
        TypeError,
        ValueError,
        UnicodeDecodeError,
        json.JSONDecodeError,
    ):
        return candidates, source_modules

    sections = (
        (
            inventory.get("transparent_spec_displays"),
            TRANSPARENT_PAPER_SPEC_DISPLAY_SCHEMA,
            "specification",
            False,
        ),
        (
            inventory.get("paper_prerequisite_displays"),
            TRANSPARENT_PAPER_DECLARATION_DISPLAY_SCHEMA,
            "declaration",
            False,
        ),
        (
            inventory.get("library_prerequisite_displays"),
            TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SCHEMA,
            "declaration",
            True,
        ),
    )
    for section, schema, name_field, carries_module in sections:
        if (
            not isinstance(section, Mapping)
            or set(section) != {"schema", "items"}
            or str(section.get("schema") or "") != str(schema)
            or not isinstance(section.get("items"), list)
        ):
            return {}, {}
        for row in section["items"]:
            if not isinstance(row, Mapping):
                return {}, {}
            name = str(row.get(name_field) or "").strip()
            display = row.get("display")
            if not name or not isinstance(display, str) or not display.strip():
                return {}, {}
            if name_field == "specification" and row.get("complete") is not True:
                continue
            _add_display_candidate(candidates, display)
            source_module = str(row.get("source_module") or "").strip()
            if carries_module and source_module:
                digest = hashlib.sha256(display.encode("utf-8")).hexdigest()
                source_modules.setdefault((name, digest), set()).add(source_module)
    return candidates, source_modules


def _retained_review_material_display_candidates(
    paper_dir: Path,
) -> tuple[dict[str, set[str]], dict[tuple[str, str], set[str]]]:
    """Read display bytes only from bounded, validated retained transports.

    Queues provide no claim, route, verdict, or currentness authority here.
    Their embedded material is accepted only after content validation, and a
    caller must still bind every byte string to an accepted-graph digest.
    """

    from scripts import semantic_review_decision_queue as review_queue

    candidates: dict[str, set[str]] = {}
    cached_source_modules: dict[tuple[str, str], set[str]] = {}
    review_surface = _review_surface_module()
    cache_path = review_surface._packet_lean_cache_path(paper_dir)
    if cache_path.is_file():
        try:
            cache = review_surface._read_json(cache_path)
        except ValueError:
            cache = {}
        for field in (
            "semantic_targets",
            "paper_prerequisite_targets",
            "library_semantic_targets",
        ):
            raw_targets = cache.get(field)
            if not isinstance(raw_targets, Mapping):
                continue
            for raw_name, raw_target in raw_targets.items():
                name = str(raw_name).strip()
                if not name or not isinstance(raw_target, Mapping):
                    continue
                display = raw_target.get("display")
                digest = str(raw_target.get("display_sha256") or "").strip().lower()
                if (
                    isinstance(display, str)
                    and display.strip()
                    and re.fullmatch(r"[0-9a-f]{64}", digest)
                    and hashlib.sha256(display.encode("utf-8")).hexdigest() == digest
                ):
                    _add_display_candidate(candidates, display)
                    source_module = str(raw_target.get("source_module") or "").strip()
                    if source_module:
                        cached_source_modules.setdefault((name, digest), set()).add(
                            source_module
                        )

    terminal_candidates, terminal_source_modules = (
        _retained_terminal_graph_display_candidates(paper_dir)
    )
    for digest, displays in terminal_candidates.items():
        candidates.setdefault(digest, set()).update(displays)
    for key, modules in terminal_source_modules.items():
        cached_source_modules.setdefault(key, set()).update(modules)

    for path in _retained_review_queue_paths(paper_dir):
        try:
            payload = review_surface._read_json(path)
            validated_items = review_queue.validated_queue_items(
                payload, paper=paper_dir.name
            )
        except (
            OSError,
            ValueError,
            review_queue.SemanticReviewDecisionQueueError,
        ):
            continue
        material = payload.get("review_material")
        if not isinstance(material, Mapping):
            continue
        declarations = material.get("declarations")
        if isinstance(declarations, Mapping):
            for name in validated_items:
                raw = declarations.get(name)
                if not isinstance(raw, Mapping):
                    continue
                reviewed_target = raw.get("semantic_target")
                _add_display_candidate(candidates, reviewed_target)
                if isinstance(reviewed_target, str) and reviewed_target.startswith(
                    _REVIEW_CLAIM_TARGET_PREFIX
                ):
                    body = reviewed_target[len(_REVIEW_CLAIM_TARGET_PREFIX):]
                    if _REVIEW_CLAIM_ROLE_SEPARATOR in body:
                        display, _roles = body.rsplit(
                            _REVIEW_CLAIM_ROLE_SEPARATOR, 1
                        )
                        _add_display_candidate(candidates, display)
        supporting = material.get("supporting_declarations")
        if isinstance(supporting, Mapping):
            # ``validated_queue_items`` authenticated the complete mapping.
            for raw in supporting.values():
                if isinstance(raw, Mapping):
                    _add_display_candidate(candidates, raw.get("semantic_target"))
    return candidates, cached_source_modules


def _recover_accepted_displays(
    expected_sha256s: Mapping[str, str],
    candidates: Mapping[str, Iterable[str]],
    *,
    label: str,
) -> dict[str, str]:
    """Require one exact retained byte string for every graph-owned digest."""

    recovered: dict[str, str] = {}
    missing: list[str] = []
    ambiguous: list[str] = []
    for name, digest in sorted(expected_sha256s.items()):
        displays = {
            display
            for display in candidates.get(digest, ())
            if isinstance(display, str)
            and hashlib.sha256(display.encode("utf-8")).hexdigest() == digest
        }
        if not displays:
            missing.append(name)
        elif len(displays) != 1:
            ambiguous.append(name)
        else:
            recovered[name] = displays.pop()
    errors = []
    if missing:
        errors.append("missing " + label + " display(s): " + ", ".join(missing))
    if ambiguous:
        errors.append(
            "ambiguous " + label + " display(s): " + ", ".join(ambiguous)
        )
    if errors:
        raise ValueError(
            "accepted graph display recovery is incomplete: " + "; ".join(errors)
        )
    return recovered


def _accepted_prerequisite_locations(
    paper_dir: Path,
    prerequisite_sha256s: Mapping[str, str],
    projection: object,
) -> tuple[
    set[str], set[str], Mapping[str, Any], Mapping[str, Any]
]:
    """Recover graph-root locations from its authenticated canonical ledgers."""

    review_surface = _review_surface_module()
    raw_metadata = getattr(
        projection, "prerequisite_review_metadata_by_declaration", {}
    )
    authenticated_metadata = (
        raw_metadata if isinstance(raw_metadata, Mapping) else {}
    )

    def ledger_items(path_name: str) -> Mapping[str, Any]:
        payload = review_surface._read_json(paper_dir / path_name)
        items = payload.get("items")
        if (
            payload.get("schema") != 1
            or payload.get("paper") != paper_dir.name
            or not isinstance(items, Mapping)
        ):
            raise ValueError(
                f"accepted graph display recovery has a malformed {path_name}"
            )
        return items

    paper_items = ledger_items(review_surface.PAPER_PREREQUISITE_LEDGER_NAME)
    library_items = ledger_items(review_surface.LIBRARY_SEMANTIC_REVIEW_NAME)
    paper_names: set[str] = set()
    library_names: set[str] = set()
    unresolved: list[str] = []
    for name, digest in sorted(prerequisite_sha256s.items()):
        paper_row = paper_items.get(name)
        library_row = library_items.get(name)
        paper_match = (
            isinstance(paper_row, Mapping)
            and paper_row.get("paper_declaration") == name
            and paper_row.get("paper_semantic_target_sha256") == digest
            and paper_row.get("paper_semantic_target_protocol")
            == review_surface.PAPER_PREREQUISITE_TARGET_PROTOCOL
        )
        library_match = (
            isinstance(library_row, Mapping)
            and library_row.get("library_declaration") == name
            and library_row.get("library_semantic_target_sha256") == digest
            and library_row.get("library_semantic_target_protocol")
            == review_surface.LIBRARY_SEMANTIC_TARGET_PROTOCOL
        )
        # Projection metadata exists only after the exact ledger row was
        # authenticated against its accepted source-judgment issuance.
        if name not in authenticated_metadata or paper_match == library_match:
            unresolved.append(name)
        elif paper_match:
            paper_names.add(name)
        else:
            library_names.add(name)
    if unresolved:
        raise ValueError(
            "accepted graph display recovery cannot establish current ledger "
            "ownership for: " + ", ".join(unresolved)
        )
    return paper_names, library_names, paper_items, library_items


def write_packet_lean_cache_from_accepted_graph(
    paper_dir: Path,
    *,
    source_map: Mapping[str, Any],
    projection: object,
) -> Path:
    """Materialize a presentation cache from exact accepted display bytes."""

    review_surface = _review_surface_module()
    claim_sha256s = dict(
        getattr(projection, "claim_semantic_target_sha256s_by_specification", {})
    )
    prerequisite_sha256s = dict(
        getattr(
            projection,
            "prerequisite_semantic_target_sha256s_by_declaration",
            {},
        )
    )
    try:
        specifications = sorted(
            EvidenceRouteSet.from_source_map(source_map).result_specifications()
        )
    except ObligationRouteError as exc:
        raise ValueError("invalid typed source route surface") from exc
    if (
        not getattr(projection, "reviewed_display_surface_complete", False)
        or set(claim_sha256s) != set(specifications)
        or not review_surface._recorded_graph_source_cards_current(
            source_map, projection
        )
    ):
        raise ValueError(
            "accepted graph display recovery requires its exact current source "
            "cards and specification names"
        )

    candidates, cached_source_modules = _retained_review_material_display_candidates(
        paper_dir
    )
    claims = _recover_accepted_displays(
        claim_sha256s, candidates, label="claim"
    )
    prerequisites = _recover_accepted_displays(
        prerequisite_sha256s, candidates, label="prerequisite"
    )
    paper_names, library_names, paper_items, library_items = (
        _accepted_prerequisite_locations(
            paper_dir, prerequisite_sha256s, projection
        )
    )

    semantic_targets = {
        name: {
            "display": claims[name],
            "display_sha256": claim_sha256s[name],
            "semantic_target_kind": "spec_proposition",
            "lean_target_protocol": V11_LEAN_TARGET_PROTOCOL,
        }
        for name in specifications
    }
    paper_targets = {
        name: {
            "display": prerequisites[name],
            "display_sha256": prerequisite_sha256s[name],
        }
        for name in sorted(paper_names)
    }
    paper_support = {
        name: str(
            paper_items[name].get("semantic_supporting_declarations_sha256") or ""
        ).strip().lower()
        for name in sorted(paper_names)
    }
    if any(
        digest and not re.fullmatch(r"[0-9a-f]{64}", digest)
        for digest in paper_support.values()
    ):
        raise ValueError(
            "accepted graph display recovery has malformed paper review-support identity"
        )

    library_targets: dict[str, dict[str, Any]] = {}
    missing_modules: list[str] = []
    ambiguous_modules: list[str] = []
    from scripts.lean_import_closure import module_name_for_path

    for name in sorted(library_names):
        digest = prerequisite_sha256s[name]
        target = {
            "display": prerequisites[name],
            "display_sha256": digest,
        }
        source_modules = set(cached_source_modules.get((name, digest), set()))
        ledger_source_path = str(
            library_items[name].get("library_source_path") or ""
        ).strip()
        ledger_module = module_name_for_path(ledger_source_path)
        if ledger_module:
            source_modules.add(ledger_module)
        if len(source_modules) > 1:
            ambiguous_modules.append(name)
            source_module = ""
        else:
            source_module = next(iter(source_modules), "")
        if (
            name.startswith("AppliedModelingLib.")
            and not source_module
            and name not in ambiguous_modules
        ):
            missing_modules.append(name)
        elif source_module:
            target["source_module"] = source_module
        library_targets[name] = target
    if ambiguous_modules:
        raise ValueError(
            "accepted graph display recovery has ambiguous source-module "
            "transport for: " + ", ".join(ambiguous_modules)
        )
    if missing_modules:
        raise ValueError(
            "accepted graph display recovery lacks retained source-module "
            "transport for: " + ", ".join(missing_modules)
        )
    module_sha256 = review_surface._library_semantic_source_modules_sha256(
        library_targets
    )
    if module_sha256 is None:
        raise ValueError(
            "accepted graph display recovery cannot validate retained library "
            "source-module transport"
        )

    payload = {
        "schema": review_surface.PACKET_LEAN_CACHE_SCHEMA,
        "paper": paper_dir.name,
        "display_protocols": review_surface._current_packet_display_protocols(),
        "specifications": specifications,
        "semantic_targets": semantic_targets,
        "paper_prerequisite_targets": paper_targets,
        "paper_prerequisite_supporting_declarations_sha256": paper_support,
        "library_semantic_targets": library_targets,
        "library_semantic_target_errors": {},
        "library_semantic_source_modules_sha256": module_sha256,
    }
    if not review_surface._recorded_graph_packet_cache_current(
        payload, specifications, projection
    ):
        raise ValueError("accepted graph rejected the recovered packet display cache")
    review_surface._packet_lean_cache_path(paper_dir).write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    return review_surface._packet_lean_cache_path(paper_dir)


def write_packet_lean_cache_from_elaborated_graph(
    paper_dir: Path,
    *,
    semantic_targets: Mapping[str, Mapping[str, Any]],
    paper_prerequisite_targets: Mapping[str, Mapping[str, Any]],
    paper_prerequisite_supporting_declarations_sha256: Mapping[str, str],
    library_semantic_targets: Mapping[str, Mapping[str, Any]],
    library_declaration_sources: Mapping[str, Mapping[str, Any]],
    library_semantic_target_errors: Mapping[str, str] | None = None,
) -> Path:
    """Materialize packet transport data from one complete Lean graph."""

    review_surface = _review_surface_module()

    def json_material(value: object) -> object:
        if isinstance(value, Mapping):
            return {str(key): json_material(item) for key, item in value.items()}
        if isinstance(value, (list, tuple)):
            return [json_material(item) for item in value]
        return value

    source_map = review_surface._read_json(paper_dir / review_surface.SOURCE_MAP_NAME)
    try:
        routes = EvidenceRouteSet.from_source_map(source_map)
        specifications = sorted(routes.result_specifications())
        semantic_roots = set(routes.source_semantic_declarations())
    except ObligationRouteError as exc:
        raise ValueError("invalid typed source route surface") from exc
    if set(semantic_targets) != set(specifications):
        raise ValueError("unified Lean graph omits a selected packet Spec")

    required_paper = {
        str(name).strip()
        for target in semantic_targets.values()
        for name in target.get("prerequisite_declarations", ())
        if str(name).strip()
    }
    required_paper.update(
        str(name).strip()
        for target in paper_prerequisite_targets.values()
        for name in target.get("direct_paper_declarations", ())
        if str(name).strip()
    )
    if not required_paper.issubset(paper_prerequisite_targets):
        raise ValueError("unified Lean graph omits a paper prerequisite")
    try:
        paper_review_targets = selected_paper_semantic_prerequisite_targets(
            source_map, paper_prerequisite_targets
        )
    except ValueError as exc:
        raise ValueError(
            "unified Lean graph has an invalid paper source-boundary review surface: "
            + str(exc)
        ) from exc

    paper_support = {
        str(name).strip(): str(digest or "").strip().lower()
        for name, digest in paper_prerequisite_supporting_declarations_sha256.items()
        if str(name).strip()
    }
    if set(paper_support) != set(paper_prerequisite_targets) or any(
        digest and not re.fullmatch(r"[0-9a-f]{64}", digest)
        for digest in paper_support.values()
    ):
        raise ValueError(
            "unified Lean graph omits a paper-prerequisite review-support identity"
        )
    paper_review_support = {
        name: paper_support[name] for name in paper_review_targets
    }

    required_library = {
        str(name).strip()
        for target in [*semantic_targets.values(), *paper_prerequisite_targets.values()]
        for name in target.get(
            "library_declarations", target.get("direct_library_declarations", ())
        )
        if str(name).strip()
    }
    required_library.update(
        str(name).strip()
        for target in library_semantic_targets.values()
        for name in target.get("direct_library_declarations", ())
        if str(name).strip()
    )
    errors = {
        str(name).strip(): str(error).strip()
        for name, error in (library_semantic_target_errors or {}).items()
        if str(name).strip() and str(error).strip()
    }
    if not required_library.issubset(library_semantic_targets) or (
        required_library & set(errors)
    ):
        raise ValueError("unified Lean graph omits a library prerequisite")
    if set(library_declaration_sources) != set(library_semantic_targets):
        raise ValueError(
            "unified Lean graph omits an exact reusable declaration source"
        )
    if not semantic_roots.issubset(
        set(paper_prerequisite_targets) | set(library_semantic_targets)
    ):
        raise ValueError(
            "unified Lean graph omits an explicitly routed semantic declaration"
        )
    try:
        library_review_targets = selected_library_semantic_prerequisite_targets(
            source_map, library_semantic_targets
        )
    except ValueError as exc:
        raise ValueError(
            "unified Lean graph has an invalid reusable-library source-boundary "
            "review surface: " + str(exc)
        ) from exc
    library_review_sources = {
        name: library_declaration_sources[name] for name in library_review_targets
    }
    library_review_errors = {
        name: error for name, error in errors.items() if name in library_review_targets
    }

    payload = {
        "schema": review_surface.PACKET_LEAN_CACHE_SCHEMA,
        "paper": paper_dir.name,
        "paper_lean_tree_sha256": review_surface._paper_lean_tree_sha256(paper_dir),
        "library_lean_tree_sha256": _lean_source_tree_sha256(
            ROOT / "AppliedModelingLib"
        ),
        "lean_display_engine_sha256": (
            review_surface._packet_lean_display_engine_sha256()
        ),
        "display_protocols": review_surface._current_packet_display_protocols(),
        "specifications": specifications,
        "semantic_targets": {
            name: json_material(target)
            for name, target in sorted(semantic_targets.items())
        },
        "paper_prerequisite_targets": {
            name: json_material(target)
            for name, target in sorted(paper_prerequisite_targets.items())
        },
        "paper_prerequisite_supporting_declarations_sha256": dict(
            sorted(paper_support.items())
        ),
        "paper_semantic_review_targets": {
            name: json_material(target)
            for name, target in sorted(paper_review_targets.items())
        },
        "paper_semantic_review_supporting_declarations_sha256": dict(
            sorted(paper_review_support.items())
        ),
        "library_semantic_targets": {
            name: json_material(target)
            for name, target in sorted(library_review_targets.items())
        },
        "library_declaration_sources": {
            name: json_material(source)
            for name, source in sorted(library_review_sources.items())
        },
        "library_semantic_target_errors": dict(sorted(library_review_errors.items())),
    }
    _write_packet_lean_cache(paper_dir, payload)
    return review_surface._packet_lean_cache_path(paper_dir)


def _only_lean_import_source_bytes_changed(error: ValueError) -> bool:
    """Recognize one stale operational graph without hiding other failures."""

    lines = str(error).splitlines()
    if not lines:
        return False
    header = re.fullmatch(
        r"Lean import-closure source validation found ([1-9][0-9]*) problem\(s\):",
        lines[0],
    )
    if header is None or int(header.group(1)) != len(lines) - 1:
        return False
    prefix = "- Lean import-closure source bytes changed: "
    for line in lines[1:]:
        if not line.startswith(prefix):
            return False
        raw_path = line.removeprefix(prefix)
        parts = raw_path.split("/")
        path = PurePosixPath(raw_path)
        if (
            not raw_path
            or raw_path != raw_path.strip()
            or "\\" in raw_path
            or "\0" in raw_path
            or path.is_absolute()
            or path.suffix != ".lean"
            or any(part in {"", ".", ".."} for part in parts)
        ):
            return False
    return True


def write_packet_lean_cache_from_current_v11_graph(
    paper_dir: Path, *, repository_root: Path | None = None
) -> Path:
    """Project a current graph, or exact current-source accepted displays."""

    review_surface = _review_surface_module()

    root = (repository_root or ROOT).resolve()
    status_path = paper_dir / "status.json"
    source_map_path = paper_dir / review_surface.SOURCE_MAP_NAME
    status = review_surface._read_json(status_path) if status_path.is_file() else {}
    source_map = (
        review_surface._read_json(source_map_path) if source_map_path.is_file() else {}
    )
    if not raw_source_spec_screening_requested(status, source_map, folder=paper_dir):
        raise ValueError(
            "packet Lean-cache preparation requires a current typed v11 paper"
        )
    try:
        projection = review_surface.load_current_v11_review_graph_projection(
            root, paper_dir
        )
    except ValueError as exc:
        if not _only_lean_import_source_bytes_changed(exc):
            raise
        # The source-aware reader rejects an invalid current graph before
        # considering accepted displays. Do not write an accepted-only cache
        # that this same reader cannot use, or claim preparation succeeded.
        raise ValueError(
            str(exc)
            + "\nRefresh the current import carrier and operational graph before "
            "preparing packet displays:\n"
            f"python3 scripts/final_closure_receipt.py --paper {paper_dir.name} "
            "--record-current-lean-import-closure\n"
            f"python3 scripts/closeout_reuse_plan.py --paper {paper_dir.name} "
            "--prepare-v11-lean-review-graph"
        ) from exc
    if projection is None:
        graph_selected, recorded_projection = (
            review_surface._recorded_graph_packet_projection(paper_dir)
        )
        if graph_selected and recorded_projection is not None:
            return write_packet_lean_cache_from_accepted_graph(
                paper_dir,
                source_map=source_map,
                projection=recorded_projection,
            )
        raise ValueError(
            "selected v11 paper has no exact current Lean review graph or "
            "recoverable current-source accepted display graph; run "
            f"python3 scripts/closeout_reuse_plan.py --paper {paper_dir.name} "
            "--prepare-v11-lean-review-graph"
        )
    _support, _names_by_root, support_digests = (
        projection.paper_prerequisite_review_support(
            projection.paper_prerequisite_targets
        )
    )
    return write_packet_lean_cache_from_elaborated_graph(
        paper_dir,
        semantic_targets=projection.semantic_targets,
        paper_prerequisite_targets=projection.paper_prerequisite_targets,
        paper_prerequisite_supporting_declarations_sha256=support_digests,
        library_semantic_targets=projection.library_semantic_targets,
        library_declaration_sources=projection.library_declaration_sources,
        library_semantic_target_errors=projection.library_semantic_target_errors,
    )


def prepare_packet_lean_cache(paper: str, *, stage: str) -> str:
    """Project the already-checkpointed current graph for packet presentation."""

    paper_dir = ROOT / "papers" / paper
    if not paper_dir.is_dir():
        raise ValueError(f"unknown paper: {paper}")
    if stage not in {"specifications", "paper-prerequisites", "library"}:
        raise ValueError(f"unknown packet Lean-cache stage: {stage}")
    write_packet_lean_cache_from_current_v11_graph(
        paper_dir, repository_root=ROOT
    )
    return f"{paper}: projected complete packet Lean cache from authenticated review graph"


def public_arxiv_tex_source_error(paper: str) -> str:
    """Return why a paper cannot expose its source excerpts publicly."""

    review_surface = _review_surface_module()
    paper_dir = ROOT / "papers" / paper
    try:
        source_map = review_surface._read_json(
            paper_dir / review_surface.SOURCE_MAP_NAME
        )
    except ValueError as exc:
        return str(exc)
    url = str(source_map.get("source_url") or "").strip().lower()
    raw_path = str(source_map.get("source_artifact_path") or "").strip()
    digest = str(source_map.get("source_artifact_sha256") or "").strip().lower()
    if not re.match(r"https?://(?:export\.)?arxiv\.org/(?:abs|e-print)/", url):
        return "the canonical source map does not cite an official arXiv source URL"
    candidate = Path(raw_path)
    if (
        not raw_path
        or candidate.is_absolute()
        or ".." in candidate.parts
        or candidate.suffix.lower() != ".tex"
    ):
        return "the canonical source artifact is not a paper-local .tex file"
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        return "the canonical source map has no valid source-artifact SHA-256"
    return ""


def sanitize_existing_packet(paper: str, tex_path: Path) -> str:
    """Project an already-rendered packet without recomputing Lean displays."""

    if not tex_path.is_file():
        raise ValueError(f"existing packet TeX does not exist: {tex_path}")
    rendered = packet_renderer._public_packet_presentation_tex(
        tex_path.read_text(encoding="utf-8"), paper=paper
    )
    return rendered.replace(
        "The dashboard records saved annotations in this paper's local\nreview trace.",
        "The dashboard records saved annotations in this paper's\n"
        "reviewer-owned review record.",
    )


def _resolve_output_dir(paper: str, raw_output: str) -> Path:
    paper_dir = (ROOT / "papers" / paper).resolve()
    output_dir = Path(raw_output) if raw_output else paper_dir / "docs"
    if not output_dir.is_absolute():
        output_dir = (ROOT / output_dir).resolve()
    try:
        output_dir.relative_to(paper_dir)
    except ValueError as exc:
        raise ValueError("--out-dir must remain inside the paper folder") from exc
    return output_dir


def _compile(tex_path: Path) -> None:
    completed = subprocess.run(
        [
            "latexmk", "-xelatex", "-interaction=nonstopmode",
            "-halt-on-error", tex_path.name,
        ],
        cwd=tex_path.parent,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(f"LaTeX compilation failed for {tex_path}")
    log_path = tex_path.with_suffix(".log")
    try:
        log_text = log_path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        raise RuntimeError(
            f"LaTeX compilation produced no readable log for {tex_path}"
        ) from exc
    if "Missing character:" in log_text:
        raise RuntimeError(
            f"LaTeX compilation omitted one or more exact review glyphs for {tex_path}"
        )


def main() -> int:
    review_surface = _review_surface_module()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True, help="paper folder id")
    parser.add_argument(
        "--out-dir", default="",
        help="paper-local output directory (default: papers/<paper>/docs)",
    )
    parser.add_argument("--write", action="store_true", help="write the TeX packet")
    parser.add_argument(
        "--compile", action="store_true", help="compile the written packet to PDF"
    )
    parser.add_argument(
        "--sanitize-existing", action="store_true",
        help=(
            "rewrite only public presentation locators in an existing packet; "
            "does not recompute Lean displays or audit evidence"
        ),
    )
    parser.add_argument(
        "--prepare-lean-cache", action="store_true",
        help="project the current Lean graph checkpoint for packet rendering",
    )
    parser.add_argument(
        "--stage", choices=("specifications", "paper-prerequisites", "library"),
        default="specifications",
        help="accepted packet-cache stage; every stage projects the full graph",
    )
    parser.add_argument(
        "--draft", action="store_true",
        help="allow a visibly incomplete diagnostic when v11 preparation is not active",
    )
    args = parser.parse_args()
    if args.compile and not (args.write or args.sanitize_existing):
        parser.error("--compile requires --write")
    if args.prepare_lean_cache and (
        args.write or args.compile or args.sanitize_existing
    ):
        parser.error("--prepare-lean-cache does not write or compile a packet")
    if args.sanitize_existing and args.write:
        parser.error("--sanitize-existing rewrites the existing TeX; omit --write")
    try:
        if args.prepare_lean_cache:
            print(prepare_packet_lean_cache(args.paper, stage=args.stage))
            return 0
        output_dir = _resolve_output_dir(args.paper, args.out_dir)
        if args.sanitize_existing:
            tex_path = output_dir / f"{PACKET_NAME}.tex"
            sanitized = sanitize_existing_packet(args.paper, tex_path)
            normalized = "\n".join(
                line.rstrip(" \t") for line in sanitized.split("\n")
            )
            tex_path.write_text(normalized, encoding="utf-8")
            print(f"sanitized {tex_path.relative_to(ROOT)}")
            if args.compile:
                _compile(tex_path)
                print(f"wrote {tex_path.with_suffix('.pdf').relative_to(ROOT)}")
            return 0
        surface = review_surface.prepared_review_surface(
            args.paper, allow_draft=args.draft
        )
        rendered = packet_renderer.render_packet(
            surface,
            template=TEMPLATE_PATH.read_text(encoding="utf-8"),
            generated_date=dt.date.today().isoformat(),
        )
        if not args.write:
            print(rendered)
            return 0
        output_dir.mkdir(parents=True, exist_ok=True)
        tex_path = output_dir / f"{PACKET_NAME}.tex"
        normalized = "\n".join(
            line.rstrip(" \t") for line in rendered.split("\n")
        )
        tex_path.write_text(normalized, encoding="utf-8")
        print(f"wrote {tex_path.relative_to(ROOT)}")
        if args.compile:
            _compile(tex_path)
            print(f"wrote {tex_path.with_suffix('.pdf').relative_to(ROOT)}")
    except (OSError, RuntimeError, ValueError) as exc:
        print(f"review-dashboard-packet: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
