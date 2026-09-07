#!/usr/bin/env python3
"""Typed current-closeout projections of declarations already discovered by Lean.

This module performs no source discovery and never opens or parses a Lean
file.  It only indexes and resolves records emitted by the Lean-owned graph.
Legacy diagnostics may construct the same record type from their isolated text
parser, but current acceptance requires ``qualified_name`` to be present in the
Lean projection.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path

from scripts.lean_review_surface import lean_source_range_text


@dataclass(frozen=True)
class LeanDeclaration:
    path: Path
    line: int
    kind: str
    name: str
    source: str
    qualified_name: str = ""
    identity_authority: str = "legacy_source_diagnostic"


_LEAN_INVENTORY_DECLARATION_KIND = {
    "axiom": "axiom",
    "definition": "def",
    "theorem": "theorem",
    "opaque": "opaque",
    "quotient": "quotient",
    "inductive": "inductive",
    "constructor": "constructor",
    "recursor": "recursor",
}


def declaration_key(declaration: LeanDeclaration) -> tuple[Path, int, str]:
    """Return the source-coordinate identity used to deduplicate one record."""

    return (declaration.path, declaration.line, declaration.name)


def resolve_declaration_name(
    declaration_index: dict[str, list[LeanDeclaration]], name: object
) -> list[LeanDeclaration]:
    """Resolve an exact qualified name or a unique short-name candidate."""

    target = str(name or "").strip()
    if not target:
        return []
    candidates: list[LeanDeclaration] = []
    if target in declaration_index:
        candidates.extend(declaration_index[target])
    elif "." not in target:
        candidates.extend(declaration_index.get(target.rsplit(".", 1)[-1], []))
    seen: set[tuple[Path, int, str]] = set()
    resolved: list[LeanDeclaration] = []
    for declaration in candidates:
        key = declaration_key(declaration)
        if key in seen:
            continue
        seen.add(key)
        resolved.append(declaration)
    return resolved


def unique_declarations(
    declaration_index: dict[str, list[LeanDeclaration]],
) -> list[LeanDeclaration]:
    """Return declaration records without qualified/short-name duplicates."""

    seen: set[tuple[Path, int, str]] = set()
    declarations: list[LeanDeclaration] = []
    for candidates in declaration_index.values():
        for declaration in candidates:
            key = declaration_key(declaration)
            if key in seen:
                continue
            seen.add(key)
            declarations.append(declaration)
    return declarations


def typed_qualified_declaration_identity(declaration: LeanDeclaration) -> str:
    """Return the Lean-emitted FQN, or empty when the typed record is invalid.

    A legacy diagnostic parser can happen to reconstruct the same spelling,
    but that does not make it an accepting identity.  Current closeout accepts
    only a name explicitly projected from the elaborated Lean environment.
    """

    if declaration.identity_authority != "lean_environment":
        return ""
    return declaration.qualified_name.strip()


def declaration_index_from_inventory(
    payload: object,
    module_sources: Mapping[str, tuple[Path, bytes]],
    *,
    source_presented_only: bool = True,
    paper_owned_only: bool = True,
) -> dict[str, list[LeanDeclaration]]:
    """Project Lean-owned declarations over their authenticated source bytes.

    Lean owns declaration identity, kind, module, generated owner, and source
    range.  This function only validates those records, applies Lean's range to
    the already retained bytes, and constructs the lookup shape used by the
    current proof and axiom gates.  The default is the presented paper-owned
    source-review surface; an exact configured support declaration may instead
    request the broader Lean-emitted inventory, but the caller must still bind
    it to its exact configured source file.  It performs no declaration
    discovery or Lean parsing.
    """

    if not isinstance(payload, Mapping):
        return {}
    raw_nodes = payload.get("declarations")
    if not isinstance(raw_nodes, list):
        return {}
    names = {
        str(node.get("declaration") or "").strip()
        for node in raw_nodes
        if isinstance(node, Mapping)
        and (node.get("paper_owned") is True if paper_owned_only else True)
        and (
            node.get("source_presented") is True
            if source_presented_only
            else True
        )
        and node.get("generated_from_owner") is False
        and str(node.get("module") or "").strip() in module_sources
        and str(node.get("declaration") or "").strip()
        == str(node.get("review_owner_declaration") or "").strip()
    }
    if not names:
        return {}
    nodes = {
        str(node.get("declaration") or "").strip(): node
        for node in raw_nodes
        if isinstance(node, Mapping)
        and str(node.get("declaration") or "").strip() in names
    }
    if set(nodes) != names:
        return {}

    declarations: dict[str, list[LeanDeclaration]] = {}
    for qualified_name in sorted(names):
        node = nodes[qualified_name]
        module = str(node.get("module") or "").strip()
        module_source = module_sources.get(module)
        kind = _LEAN_INVENTORY_DECLARATION_KIND.get(
            str(node.get("declaration_kind") or "").strip()
        )
        if module_source is None or kind is None:
            continue
        path, content = module_source
        declaration_source = lean_source_range_text(
            content, node.get("source_range")
        )
        raw_range = node.get("source_range")
        if declaration_source is None or not isinstance(raw_range, Mapping):
            continue
        line = raw_range.get("line_start")
        if not isinstance(line, int) or isinstance(line, bool):
            continue
        short_name = qualified_name.rsplit(".", 1)[-1]
        declaration = LeanDeclaration(
            path=path,
            line=line,
            kind=kind,
            name=short_name,
            source=declaration_source,
            qualified_name=qualified_name,
            identity_authority="lean_environment",
        )
        declarations.setdefault(qualified_name, []).append(declaration)
        declarations.setdefault(short_name, []).append(declaration)
    return declarations


def declaration_index_from_source_records(
    records: object,
) -> dict[str, list[LeanDeclaration]]:
    """Project Lean-selected source records into the typed lookup shape."""

    if not isinstance(records, Mapping):
        return {}
    declarations: dict[str, list[LeanDeclaration]] = {}
    for raw_name, raw in sorted(records.items(), key=lambda item: str(item[0])):
        if not isinstance(raw, Mapping):
            return {}
        qualified_name = str(raw_name or "").strip()
        path = raw.get("source_path")
        source = str(raw.get("source") or "")
        raw_range = raw.get("source_range")
        raw_kind = str(raw.get("declaration_kind") or "").strip()
        line = raw_range.get("line_start") if isinstance(raw_range, Mapping) else None
        if (
            not qualified_name
            or not isinstance(path, Path)
            or not source
            or not isinstance(line, int)
            or isinstance(line, bool)
            or not raw_kind
        ):
            return {}
        kind = _LEAN_INVENTORY_DECLARATION_KIND.get(raw_kind, raw_kind)
        short_name = qualified_name.rsplit(".", 1)[-1]
        declaration = LeanDeclaration(
            path=path,
            line=line,
            kind=kind,
            name=short_name,
            source=source,
            qualified_name=qualified_name,
            identity_authority="lean_environment",
        )
        declarations.setdefault(qualified_name, []).append(declaration)
        declarations.setdefault(short_name, []).append(declaration)
    return declarations
