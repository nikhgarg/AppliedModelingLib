#!/usr/bin/env python3
"""Snapshot and compare module-owned declarations using Lean's environment.

This is a reorganization tool, not a second Lean parser and not closeout
authority.  Lean identifies the declarations owned by the selected modules and
emits each declaration's canonical, name-independent semantic signature.  The
portable snapshot excludes module routing, paths, and line coordinates; a
separate routing digest is retained only for diagnostics.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Any

try:
    from scripts.lean_signature_manifest import (
        RepositoryBuildInputSnapshotProvider,
        run_lean_declaration_inventory,
        semantic_signature_sha256s_from_inventory,
    )
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from lean_signature_manifest import (
        RepositoryBuildInputSnapshotProvider,
        run_lean_declaration_inventory,
        semantic_signature_sha256s_from_inventory,
    )


ROOT = Path(__file__).resolve().parents[1]
SNAPSHOT_SCHEMA = "applied-modeling-lib.module-semantic-snapshot/v1"


def _canonical_sha256(value: object) -> str:
    payload = json.dumps(
        value,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _portable_declaration_name(name: str, project_root: str) -> str:
    """Remove only the project spelling and private module-routing prefix."""

    public_prefix = project_root + "."
    if name.startswith(public_prefix):
        return "$PROJECT." + name[len(public_prefix) :]
    if name.startswith("_private."):
        marker = "." + public_prefix
        index = name.rfind(marker)
        if index >= 0:
            return "_private.$PROJECT." + name[index + len(marker) :]
    return name


def build_snapshot(
    root: Path,
    import_module: str,
    inventory_modules: tuple[str, ...],
    *,
    timeout_seconds: int,
    build_timeout_seconds: int,
) -> dict[str, Any]:
    """Ask Lean for one complete portable declaration snapshot."""

    project_root = import_module.partition(".")[0]
    if not project_root:
        raise ValueError("the import module has no project root")
    provider = RepositoryBuildInputSnapshotProvider(
        root,
        lean_graph_timeout_seconds=build_timeout_seconds,
    )
    source_snapshot = provider.repository_source_snapshot(import_module)
    workspace_modules = tuple(
        sorted(module for module, _path, _content, _digest in source_snapshot)
    )
    if not workspace_modules or not set(inventory_modules).issubset(workspace_modules):
        raise ValueError(
            "Lean returned no complete project semantic workspace for the move batch"
        )
    discovery = run_lean_declaration_inventory(
        root,
        import_module,
        inventory_modules=inventory_modules,
        paper_modules=inventory_modules,
        workspace_module_names=workspace_modules,
        semantic_manifest_modules=workspace_modules,
        include_semantic_displays=False,
        include_axiom_closure=False,
        timeout_seconds=timeout_seconds,
        build_timeout_seconds=build_timeout_seconds,
        build_input_provider=provider,
    )
    raw_names = discovery.get("source_declarations")
    if (
        not isinstance(raw_names, list)
        or any(not isinstance(name, str) or not name for name in raw_names)
        or raw_names != sorted(set(raw_names))
    ):
        raise ValueError("Lean returned no complete source-declaration inventory")
    names = tuple(raw_names)

    signed = run_lean_declaration_inventory(
        root,
        import_module,
        inventory_modules=inventory_modules,
        paper_modules=inventory_modules,
        workspace_module_names=workspace_modules,
        semantic_manifest_modules=workspace_modules,
        semantic_signature_declaration_names=names,
        include_semantic_displays=False,
        include_axiom_closure=False,
        timeout_seconds=timeout_seconds,
        build_timeout_seconds=build_timeout_seconds,
        build_input_provider=provider,
        require_build=False,
    )
    try:
        signatures = semantic_signature_sha256s_from_inventory(
            signed,
            expected_declarations=names,
        )
    except ValueError as exc:
        section = signed.get("semantic_signatures")
        errors = section.get("errors") if isinstance(section, Mapping) else None
        detail = (
            "; ".join(str(error) for error in errors[:20])
            if isinstance(errors, list) and errors
            else ""
        )
        raise ValueError(
            "Lean returned incomplete signatures for the selected move batch"
            + (f": {detail}" if detail else "")
        ) from exc
    raw_nodes = signed.get("declarations")
    if not isinstance(raw_nodes, list):
        raise TypeError("Lean returned no complete declaration nodes")
    nodes: dict[str, Mapping[str, Any]] = {}
    for value in raw_nodes:
        if not isinstance(value, Mapping):
            raise TypeError("Lean returned a malformed declaration node")
        name = str(value.get("declaration") or "").strip()
        if name in signatures:
            if name in nodes:
                raise ValueError(f"Lean returned duplicate declaration `{name}`")
            nodes[name] = value
    if set(nodes) != set(names):
        raise ValueError("Lean declaration nodes differ from the source inventory")

    semantic_items: list[dict[str, str]] = []
    routing_items: list[dict[str, str]] = []
    for name in names:
        node = nodes[name]
        kind = str(node.get("declaration_kind") or "").strip()
        module = str(node.get("module") or "").strip()
        if (
            not kind
            or module not in inventory_modules
            or node.get("source_presented") is not True
            or node.get("generated_from_owner") is not False
            or str(node.get("review_owner_declaration") or "").strip() != name
        ):
            raise ValueError(f"Lean returned no unique source owner for `{name}`")
        semantic_items.append(
            {
                "portable_name": _portable_declaration_name(name, project_root),
                "declaration_kind": kind,
                "semantic_signature_sha256": signatures[name],
            }
        )
        routing_items.append(
            {
                "qualified_name": name,
                "source_module": module,
            }
        )

    semantic_items.sort(
        key=lambda item: (
            item["portable_name"],
            item["declaration_kind"],
            item["semantic_signature_sha256"],
        )
    )
    portable_names = [item["portable_name"] for item in semantic_items]
    if len(portable_names) != len(set(portable_names)):
        raise ValueError(
            "project-relative declaration names are ambiguous; split the module batch"
        )

    result = {
        "schema": SNAPSHOT_SCHEMA,
        "import_module": import_module,
        "inventory_modules": list(inventory_modules),
        "source_declaration_count": len(semantic_items),
        "portable_semantic_sha256": _canonical_sha256(semantic_items),
        "routing_sha256": _canonical_sha256(routing_items),
        "semantic_items": semantic_items,
        "routing_items": routing_items,
    }
    if not provider.finalize_unchanged():
        raise ValueError("project semantic workspace changed during the snapshot")
    return result


def _load_snapshot(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict) or value.get("schema") != SNAPSHOT_SCHEMA:
        raise ValueError(f"{path} is not a supported semantic snapshot")
    items = value.get("semantic_items")
    if (
        not isinstance(items, list)
        or value.get("source_declaration_count") != len(items)
        or value.get("portable_semantic_sha256") != _canonical_sha256(items)
    ):
        raise ValueError(f"{path} has a stale semantic snapshot digest")
    return value


def _comparison_error(before: Mapping[str, Any], after: Mapping[str, Any]) -> str:
    before_items = before.get("semantic_items")
    after_items = after.get("semantic_items")
    if before_items == after_items:
        return ""
    before_by_name = {
        str(item.get("portable_name") or ""): item
        for item in before_items
        if isinstance(item, Mapping)
    }
    after_by_name = {
        str(item.get("portable_name") or ""): item
        for item in after_items
        if isinstance(item, Mapping)
    }
    missing = sorted(set(before_by_name) - set(after_by_name))
    added = sorted(set(after_by_name) - set(before_by_name))
    changed = sorted(
        name
        for name in set(before_by_name) & set(after_by_name)
        if before_by_name[name] != after_by_name[name]
    )
    return (
        "module semantics changed: "
        f"missing={missing[:20]}, added={added[:20]}, changed={changed[:20]}"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--import-module", required=True)
    parser.add_argument(
        "--inventory-module",
        action="append",
        required=True,
        dest="inventory_modules",
    )
    parser.add_argument("--output", type=Path)
    parser.add_argument("--compare", type=Path)
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--build-timeout-seconds", type=int, default=1800)
    args = parser.parse_args()

    modules = tuple(sorted(set(args.inventory_modules)))
    snapshot = build_snapshot(
        args.root.resolve(),
        args.import_module,
        modules,
        timeout_seconds=args.timeout_seconds,
        build_timeout_seconds=args.build_timeout_seconds,
    )
    encoded = json.dumps(snapshot, ensure_ascii=True, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        sys.stdout.write(encoded)
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded, encoding="utf-8")

    if args.compare is not None:
        before = _load_snapshot(args.compare)
        error = _comparison_error(before, snapshot)
        if error:
            print(error, file=sys.stderr)
            return 1
        print(
            "semantic snapshot matches: "
            f"{snapshot['source_declaration_count']} declarations, "
            f"{snapshot['portable_semantic_sha256']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
