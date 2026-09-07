"""Strict transport validation for Lean-owned semantic review rows.

The declaration-graph producer lives in ``lean_signature_manifest``.  This
module owns only the schema and post-acquisition validation of Lean-emitted JSON
rows.  It never reads or parses Lean source, invokes Lean, discovers a
declaration, or decides semantic materiality.  Producers and every accepting
consumer therefore share one fail-closed transport validator without making
the producer module part of the consumer dependency graph.
"""

from __future__ import annotations

import hashlib
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any


TRANSPARENT_PAPER_SPEC_DISPLAY_SENTINEL = "LEAN_TRANSPARENT_PAPER_SPEC_DISPLAY:"
TRANSPARENT_PAPER_SPEC_DISPLAY_SCHEMA = 2
TRANSPARENT_PAPER_DECLARATION_DISPLAY_SENTINEL = (
    "LEAN_TRANSPARENT_PAPER_DECLARATION_DISPLAY:"
)
TRANSPARENT_PAPER_DECLARATION_DISPLAY_SCHEMA = 2
TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SENTINEL = (
    "LEAN_TRANSPARENT_LIBRARY_DECLARATION_DISPLAY:"
)
TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SCHEMA = 3


def _requested_names(values: Iterable[str]) -> list[str]:
    return sorted({str(value).strip() for value in values if str(value).strip()})


def _normalized_declaration_names(value: object) -> tuple[str, ...] | None:
    if not isinstance(value, list) or any(
        not isinstance(item, str) or not item.strip() for item in value
    ):
        return None
    normalized = tuple(item.strip() for item in value)
    return normalized if list(normalized) == sorted(set(normalized)) else None


def lean_source_range_text(content: bytes, raw_range: object) -> str | None:
    """Apply one Lean-owned source range to authenticated UTF-8 bytes.

    Lean reports source columns as Unicode character offsets rather than UTF-8
    byte offsets.  This transport helper validates and applies that coordinate;
    it performs no declaration parsing or range discovery.
    """

    if not isinstance(raw_range, Mapping) or set(raw_range) != {
        "line_start",
        "column_start",
        "line_end",
        "column_end",
    }:
        return None
    values = tuple(
        raw_range[field]
        for field in ("line_start", "column_start", "line_end", "column_end")
    )
    if any(not isinstance(value, int) or isinstance(value, bool) for value in values):
        return None
    line_start, column_start, line_end, column_end = values
    try:
        lines = content.decode("utf-8").splitlines(keepends=True)
    except UnicodeDecodeError:
        return None
    if not (
        1 <= line_start <= line_end <= len(lines)
        and column_start >= 0
        and column_end >= 0
    ):
        return None
    first = lines[line_start - 1]
    last = lines[line_end - 1]
    if column_start > len(first) or column_end > len(last):
        return None
    if line_start == line_end:
        if column_end < column_start:
            return None
        selected = first[column_start:column_end]
    else:
        selected = "".join(
            [
                first[column_start:],
                *lines[line_start : line_end - 1],
                last[:column_end],
            ]
        )
    text = selected.strip()
    return text or None


def project_transparent_paper_spec_display_section(
    payload: object,
    requested_specifications: Iterable[str],
) -> dict[str, dict[str, Any]]:
    """Validate one decoded Lean transparent-Spec display section."""

    requested = _requested_names(requested_specifications)
    if not isinstance(payload, Mapping) or set(payload) != {"schema", "items"}:
        return {}
    if payload.get("schema") != str(TRANSPARENT_PAPER_SPEC_DISPLAY_SCHEMA):
        return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, list) or len(raw_items) != len(requested):
        return {}
    parsed: dict[str, dict[str, Any]] = {}
    for raw in raw_items:
        if not isinstance(raw, Mapping) or set(raw) != {
            "specification",
            "complete",
            "expansion_count",
            "expanded_declarations",
            "prerequisite_declarations",
            "library_declarations",
            "erased_proof_declarations",
            "blocked_declarations",
            "display",
        }:
            return {}
        specification = str(raw.get("specification") or "").strip()
        complete = raw.get("complete")
        expansion_count = raw.get("expansion_count")
        expanded = raw.get("expanded_declarations")
        prerequisites = raw.get("prerequisite_declarations")
        libraries = raw.get("library_declarations")
        erased_proofs = _normalized_declaration_names(
            raw.get("erased_proof_declarations")
        )
        blocked = raw.get("blocked_declarations")
        display = raw.get("display")
        if (
            not specification
            or specification in parsed
            or complete is not True
            or not isinstance(expansion_count, str)
            or not expansion_count.isdigit()
            or not isinstance(expanded, list)
            or not isinstance(prerequisites, list)
            or not isinstance(libraries, list)
            or erased_proofs is None
            or not isinstance(blocked, list)
            or blocked
            or not isinstance(display, str)
            or not display.strip()
            or any(
                not isinstance(value, str) or not value.strip()
                for value in expanded
            )
            or any(
                not isinstance(value, str) or not value.strip()
                for value in prerequisites
            )
            or any(
                not isinstance(value, str) or not value.strip()
                for value in libraries
            )
        ):
            return {}
        normalized_expanded = [str(value).strip() for value in expanded]
        normalized_prerequisites = [str(value).strip() for value in prerequisites]
        normalized_libraries = [str(value).strip() for value in libraries]
        if (
            normalized_expanded != sorted(set(normalized_expanded))
            or normalized_prerequisites != sorted(set(normalized_prerequisites))
            or normalized_libraries != sorted(set(normalized_libraries))
        ):
            return {}
        parsed[specification] = {
            "display": display,
            "display_sha256": hashlib.sha256(display.encode("utf-8")).hexdigest(),
            "expansion_count": int(expansion_count),
            "expanded_declarations": tuple(normalized_expanded),
            "prerequisite_declarations": tuple(normalized_prerequisites),
            "library_declarations": tuple(normalized_libraries),
            "erased_proof_declarations": erased_proofs,
        }
    return parsed if sorted(parsed) == requested else {}


def project_transparent_paper_declaration_display_section(
    payload: object,
    requested_declarations: Iterable[str],
) -> dict[str, dict[str, Any]]:
    """Validate one decoded Lean paper-prerequisite display section."""

    requested = _requested_names(requested_declarations)
    if not isinstance(payload, Mapping) or set(payload) != {"schema", "items"}:
        return {}
    if payload.get("schema") != str(TRANSPARENT_PAPER_DECLARATION_DISPLAY_SCHEMA):
        return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, list) or len(raw_items) < len(requested):
        return {}
    parsed: dict[str, dict[str, Any]] = {}
    allowed_kinds = {"definition", "opaque_definition", "non_definition"}
    for raw in raw_items:
        if not isinstance(raw, Mapping) or set(raw) != {
            "declaration",
            "declaration_kind",
            "root_expanded",
            "direct_paper_declarations",
            "direct_library_declarations",
            "erased_proof_declarations",
            "display",
        }:
            return {}
        declaration = str(raw.get("declaration") or "").strip()
        kind = str(raw.get("declaration_kind") or "").strip()
        root_expanded = raw.get("root_expanded")
        paper_dependencies = raw.get("direct_paper_declarations")
        library_dependencies = raw.get("direct_library_declarations")
        erased_proofs = _normalized_declaration_names(
            raw.get("erased_proof_declarations")
        )
        display = raw.get("display")
        if (
            not declaration
            or declaration in parsed
            or kind not in allowed_kinds
            or not isinstance(root_expanded, bool)
            or (kind == "definition") != root_expanded
            or not isinstance(paper_dependencies, list)
            or not isinstance(library_dependencies, list)
            or erased_proofs is None
            or not isinstance(display, str)
            or not display.strip()
        ):
            return {}
        normalized_paper = [str(value).strip() for value in paper_dependencies]
        normalized_library = [str(value).strip() for value in library_dependencies]
        if (
            any(
                not isinstance(value, str) or not value.strip()
                for value in paper_dependencies
            )
            or normalized_paper != sorted(set(normalized_paper))
            or declaration in normalized_paper
            or any(
                not isinstance(value, str) or not value.strip()
                for value in library_dependencies
            )
            or normalized_library != sorted(set(normalized_library))
        ):
            return {}
        parsed[declaration] = {
            "display": display,
            "display_sha256": hashlib.sha256(display.encode("utf-8")).hexdigest(),
            "declaration_kind": kind,
            "root_expanded": root_expanded,
            "direct_paper_declarations": tuple(normalized_paper),
            "direct_library_declarations": tuple(normalized_library),
            "erased_proof_declarations": erased_proofs,
        }
    return parsed if set(requested).issubset(parsed) else {}


def project_transparent_library_declaration_display_section(
    payload: object,
    requested_declarations: Iterable[str],
) -> dict[str, dict[str, Any]]:
    """Validate one decoded Lean reusable-prerequisite display section."""

    requested = _requested_names(requested_declarations)
    if not isinstance(payload, Mapping) or set(payload) != {"schema", "items"}:
        return {}
    if payload.get("schema") != str(TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SCHEMA):
        return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, list) or len(raw_items) < len(requested):
        return {}
    parsed: dict[str, dict[str, Any]] = {}
    allowed_kinds = {"definition", "opaque_definition", "non_definition"}
    for raw in raw_items:
        if not isinstance(raw, Mapping) or set(raw) != {
            "declaration",
            "review_owner_declaration",
            "source_module",
            "source_line_start",
            "source_column_start",
            "source_line_end",
            "source_column_end",
            "declaration_kind",
            "root_expanded",
            "direct_library_declarations",
            "erased_proof_declarations",
            "display",
        }:
            return {}
        declaration = str(raw.get("declaration") or "").strip()
        review_owner = str(raw.get("review_owner_declaration") or "").strip()
        source_module = str(raw.get("source_module") or "").strip()
        source_line_start = raw.get("source_line_start")
        source_column_start = raw.get("source_column_start")
        source_line_end = raw.get("source_line_end")
        source_column_end = raw.get("source_column_end")
        kind = str(raw.get("declaration_kind") or "").strip()
        root_expanded = raw.get("root_expanded")
        dependencies = raw.get("direct_library_declarations")
        erased_proofs = _normalized_declaration_names(
            raw.get("erased_proof_declarations")
        )
        display = raw.get("display")
        if (
            not declaration
            or review_owner != declaration
            or not source_module
            or not isinstance(source_line_start, int)
            or not isinstance(source_column_start, int)
            or not isinstance(source_line_end, int)
            or not isinstance(source_column_end, int)
            or source_line_start <= 0
            or source_column_start < 0
            or source_line_end < source_line_start
            or source_column_end < 0
            or declaration in parsed
            or kind not in allowed_kinds
            or not isinstance(root_expanded, bool)
            or (kind == "definition") != root_expanded
            or not isinstance(dependencies, list)
            or erased_proofs is None
            or not isinstance(display, str)
            or not display.strip()
        ):
            return {}
        normalized_dependencies = [str(value).strip() for value in dependencies]
        if (
            any(
                not isinstance(value, str)
                or not value.strip()
                or value.strip() == declaration
                for value in dependencies
            )
            or normalized_dependencies != sorted(set(normalized_dependencies))
        ):
            return {}
        parsed[declaration] = {
            "display": display,
            "display_sha256": hashlib.sha256(display.encode("utf-8")).hexdigest(),
            "declaration_kind": kind,
            "root_expanded": root_expanded,
            "review_owner_declaration": review_owner,
            "source_module": source_module,
            "source_line_start": source_line_start,
            "source_column_start": source_column_start,
            "source_line_end": source_line_end,
            "source_column_end": source_column_end,
            "direct_library_declarations": tuple(normalized_dependencies),
            "erased_proof_declarations": erased_proofs,
        }
    return parsed if set(requested).issubset(parsed) else {}


@dataclass(frozen=True)
class LeanSemanticReviewDisplaySurface:
    """One exact projection of the three Lean-owned review-display sections."""

    specifications: Mapping[str, Mapping[str, Any]]
    paper_declarations: Mapping[str, Mapping[str, Any]]
    library_declarations: Mapping[str, Mapping[str, Any]]


def semantic_review_display_surface_from_inventory(
    payload: object,
    *,
    expected_specifications: Iterable[str],
    expected_paper_declarations: Iterable[str],
    expected_library_declarations: Iterable[str],
) -> LeanSemanticReviewDisplaySurface:
    """Validate and project one exact Lean-owned semantic review surface."""

    if not isinstance(payload, Mapping):
        raise ValueError("Lean declaration inventory is malformed")
    expectations = {
        "transparent_spec_displays": tuple(
            _requested_names(expected_specifications)
        ),
        "paper_prerequisite_displays": tuple(
            _requested_names(expected_paper_declarations)
        ),
        "library_prerequisite_displays": tuple(
            _requested_names(expected_library_declarations)
        ),
    }
    projectors = {
        "transparent_spec_displays": project_transparent_paper_spec_display_section,
        "paper_prerequisite_displays": (
            project_transparent_paper_declaration_display_section
        ),
        "library_prerequisite_displays": (
            project_transparent_library_declaration_display_section
        ),
    }
    schemas = {
        "transparent_spec_displays": str(TRANSPARENT_PAPER_SPEC_DISPLAY_SCHEMA),
        "paper_prerequisite_displays": str(
            TRANSPARENT_PAPER_DECLARATION_DISPLAY_SCHEMA
        ),
        "library_prerequisite_displays": str(
            TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SCHEMA
        ),
    }
    projected: dict[str, Mapping[str, Mapping[str, Any]]] = {}
    for section_name, expected in expectations.items():
        section = payload.get(section_name)
        rows = section.get("items") if isinstance(section, Mapping) else None
        if (
            not isinstance(section, Mapping)
            or set(section) != {"schema", "items"}
            or section.get("schema") != schemas[section_name]
            or not isinstance(rows, list)
            or len(rows) != len(expected)
        ):
            raise ValueError(
                f"Lean declaration inventory has malformed {section_name}"
            )
        parsed = projectors[section_name](section, expected)
        if set(parsed) != set(expected):
            raise ValueError(
                f"Lean declaration inventory {section_name} differs from "
                "the selected review surface"
            )
        projected[section_name] = MappingProxyType(parsed)
    return LeanSemanticReviewDisplaySurface(
        specifications=projected["transparent_spec_displays"],
        paper_declarations=projected["paper_prerequisite_displays"],
        library_declarations=projected["library_prerequisite_displays"],
    )


def lean_owned_semantic_review_display_surface_from_inventory(
    payload: object,
    *,
    expected_specifications: Iterable[str],
) -> LeanSemanticReviewDisplaySurface:
    """Project the complete prerequisite denominator named by Lean itself.

    Result specifications remain fixed by the typed paper source routes.
    Paper-local and reusable prerequisite declarations are outputs of Lean's
    elaborated dependency graph.  Derive those two exact name sets only from
    the corresponding typed inventory sections, then pass them through the
    ordinary strict transport validator.  Missing, extra, blank, duplicate,
    or malformed rows therefore still fail closed; Python does not rediscover
    declarations from source text, ledger keys, or namespaces.
    """

    if not isinstance(payload, Mapping):
        raise ValueError("Lean declaration inventory is malformed")

    def declarations(section_name: str) -> tuple[str, ...]:
        section = payload.get(section_name)
        rows = section.get("items") if isinstance(section, Mapping) else None
        if not isinstance(rows, list):
            raise ValueError(
                f"Lean declaration inventory has malformed {section_name}"
            )
        return tuple(
            sorted(
                str(row.get("declaration") or "").strip()
                for row in rows
                if isinstance(row, Mapping)
                and str(row.get("declaration") or "").strip()
            )
        )

    return semantic_review_display_surface_from_inventory(
        payload,
        expected_specifications=expected_specifications,
        expected_paper_declarations=declarations("paper_prerequisite_displays"),
        expected_library_declarations=declarations(
            "library_prerequisite_displays"
        ),
    )
