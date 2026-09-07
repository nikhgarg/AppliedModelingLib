#!/usr/bin/env python3
"""Compute the portable identity of the raw source-record producer.

The identity is deliberately derived from an exact candidate source view.  It
follows the marker-owned fresh-generation statements through repository Python
imports, while excluding unrelated presentation and cache-consumer code.  All
paths in the normalized payload are repository-relative, so identical commits
have identical identities in different clones and worktrees.
"""

from __future__ import annotations

import ast
import hashlib
import json
from pathlib import PurePosixPath
from typing import Any, Callable


SOURCE_RECORD_RAW_PRODUCER_CODE_IDENTITY_SCHEMA = 1
SOURCE_RECORD_RAW_PRODUCER_BEGIN_MARKER = "# SOURCE_RECORD_RAW_PRODUCER_BEGIN"
SOURCE_RECORD_RAW_PRODUCER_END_MARKER = "# SOURCE_RECORD_RAW_PRODUCER_END"
SOURCE_RECORD_RAW_PRODUCER_ENTRY_PATH = (
    "skills/econcs-formalizer/scripts/source_record_audit.py"
)
SOURCE_RECORD_RAW_PRODUCER_DISPLAY_PATH = (
    SOURCE_RECORD_RAW_PRODUCER_ENTRY_PATH + "#fresh-raw-generation"
)
SOURCE_RECORD_RAW_PRODUCER_EXTERNAL_CODE_PATHS = (
    "scripts/lean_signature_manifest_helper.lean",
)

SourceReader = Callable[[str], bytes | None]


def _normalized_path(value: str) -> str | None:
    path = PurePosixPath(value)
    if (
        not value
        or path.is_absolute()
        or "\\" in value
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        return None
    return path.as_posix()


def _file_identity(
    read_bytes: SourceReader,
    path: str,
    *,
    display_path: str | None = None,
) -> dict[str, str]:
    content = read_bytes(path)
    if content is None:
        return {
            "path": display_path or path,
            "sha256": "",
            "status": "missing",
        }
    return {
        "path": display_path or path,
        "sha256": hashlib.sha256(content).hexdigest(),
        "status": "present",
    }


def raw_generation_code_identity(
    read_bytes: SourceReader,
    *,
    entry_path: str = SOURCE_RECORD_RAW_PRODUCER_ENTRY_PATH,
    display_path: str = SOURCE_RECORD_RAW_PRODUCER_DISPLAY_PATH,
) -> dict[str, str]:
    """Hash the transitive repository-Python fresh-generation closure.

    ``read_bytes`` is the only source authority.  It may read a filesystem, a
    Git index, or an immutable Git tree; the digest never incorporates the
    checkout's absolute location.
    """

    normalized_entry = _normalized_path(entry_path)
    if normalized_entry is None:
        return {"path": display_path, "sha256": "", "status": "unavailable"}

    parsed: dict[str, dict[str, Any]] = {}
    unresolved: set[str] = set()
    import_routes: set[tuple[str, str, str]] = set()

    def repository_module_path(module: str) -> str | None:
        if not module or any(not part for part in module.split(".")):
            return None
        module_candidates = [module]
        # Historical modules support both direct-file ``from helper`` and
        # package ``from scripts.helper`` execution.  Both spellings name the
        # same repository module; resolve them to one path before deciding
        # whether a guarded fallback import is ambiguous.
        if "." not in module:
            module_candidates.append("scripts." + module)
        for candidate_module in module_candidates:
            relative = PurePosixPath(*candidate_module.split("."))
            for candidate in (
                relative.with_suffix(".py").as_posix(),
                (relative / "__init__.py").as_posix(),
            ):
                if read_bytes(candidate) is not None:
                    return candidate
        return None

    def canonical_module_name(path: str) -> str:
        pure = PurePosixPath(path)
        if pure.name == "__init__.py":
            pure = pure.parent
        else:
            pure = pure.with_suffix("")
        return ".".join(pure.parts)

    def parse_module(path: str) -> dict[str, Any] | None:
        normalized = _normalized_path(path)
        if normalized is None:
            unresolved.add(f"invalid-path:{path}")
            return None
        if normalized in parsed:
            return parsed[normalized]
        content = read_bytes(normalized)
        try:
            if content is None:
                raise OSError("missing source")
            source = content.decode("utf-8")
            tree = ast.parse(source, filename=normalized)
        except (OSError, SyntaxError, UnicodeDecodeError):
            unresolved.add(f"unparseable:{normalized}")
            return None
        definitions: dict[str, ast.AST] = {}
        constants: dict[str, ast.AST] = {}
        imported_names: dict[str, set[tuple[str, str]]] = {}
        imported_modules: dict[str, set[str]] = {}

        def import_statements(statement: ast.stmt) -> list[ast.stmt]:
            if isinstance(statement, (ast.Import, ast.ImportFrom)):
                return [statement]
            if isinstance(statement, ast.Try):
                branches = [
                    statement.body,
                    statement.orelse,
                    statement.finalbody,
                    *(handler.body for handler in statement.handlers),
                ]
            else:
                return []
            return [
                imported
                for branch in branches
                for child in branch
                for imported in import_statements(child)
            ]

        for statement in tree.body:
            if isinstance(
                statement, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
            ):
                definitions[statement.name] = statement
            elif isinstance(statement, (ast.Assign, ast.AnnAssign)):
                targets = (
                    statement.targets
                    if isinstance(statement, ast.Assign)
                    else [statement.target]
                )
                for target in targets:
                    if isinstance(target, ast.Name):
                        constants[target.id] = statement
            for imported_statement in import_statements(statement):
                if isinstance(imported_statement, ast.ImportFrom):
                    if imported_statement.level:
                        unresolved.add(
                            f"relative-import:{normalized}:{imported_statement.lineno}"
                        )
                        continue
                    module = str(imported_statement.module or "")
                    for alias in imported_statement.names:
                        if alias.name == "*":
                            unresolved.add(
                                f"star-import:{normalized}:{imported_statement.lineno}"
                            )
                            continue
                        local_name = alias.asname or alias.name
                        # ``from package import child`` imports a module when
                        # ``package.child`` is a repository module. Record it
                        # as such so later ``child.member`` traversal follows
                        # the child file rather than looking for a variable in
                        # the package ``__init__``.
                        child_module = f"{module}.{alias.name}" if module else ""
                        if child_module and repository_module_path(child_module):
                            imported_modules.setdefault(local_name, set()).add(
                                child_module
                            )
                        else:
                            imported_names.setdefault(local_name, set()).add(
                                (module, alias.name)
                            )
                else:
                    assert isinstance(imported_statement, ast.Import)
                    for alias in imported_statement.names:
                        imported_modules.setdefault(
                            alias.asname or alias.name.split(".")[0], set()
                        ).add(alias.name)
        info = {
            "tree": tree,
            "definitions": definitions,
            "constants": constants,
            "imported_names": imported_names,
            "imported_modules": imported_modules,
        }
        parsed[normalized] = info
        return info

    entry = parse_module(normalized_entry)
    try:
        if entry is None:
            raise ValueError("entry module unavailable")
        entry_bytes = read_bytes(normalized_entry)
        if entry_bytes is None:
            raise ValueError("entry source unavailable")
        source_lines = entry_bytes.decode("utf-8").splitlines()
        begin_lines = [
            index + 1
            for index, line in enumerate(source_lines)
            if line.strip() == SOURCE_RECORD_RAW_PRODUCER_BEGIN_MARKER
        ]
        end_lines = [
            index + 1
            for index, line in enumerate(source_lines)
            if line.strip() == SOURCE_RECORD_RAW_PRODUCER_END_MARKER
        ]
        if (
            len(begin_lines) != 1
            or len(end_lines) != 1
            or begin_lines[0] >= end_lines[0]
        ):
            raise ValueError("raw-producer markers are missing or malformed")
        run_audit = entry["definitions"].get("_run_audit")
        if not isinstance(run_audit, (ast.FunctionDef, ast.AsyncFunctionDef)):
            raise ValueError("_run_audit declaration is unavailable")
        fresh_statements = [
            statement
            for statement in run_audit.body
            if statement.lineno > begin_lines[0]
            and getattr(statement, "end_lineno", statement.lineno) < end_lines[0]
        ]
        if not fresh_statements:
            raise ValueError("raw-producer marker block is empty")

        pending: list[tuple[str, str, str]] = []
        reached: dict[str, dict[tuple[str, str], ast.AST]] = {}
        resolving_imports: set[tuple[str, str]] = set()

        def enqueue_symbol(module_path: str, symbol: str) -> bool:
            info = parse_module(module_path)
            if info is None:
                return False
            if symbol in info["definitions"]:
                pending.append((module_path, "definition", symbol))
                return True
            if symbol in info["constants"]:
                pending.append((module_path, "constant", symbol))
                return True
            imported_candidates = info["imported_names"].get(symbol)
            if not imported_candidates:
                return False
            resolved_candidates = {
                (target_path, imported_symbol)
                for imported_module, imported_symbol in imported_candidates
                if (target_path := repository_module_path(imported_module)) is not None
            }
            if not resolved_candidates:
                return False
            if len(resolved_candidates) != 1:
                unresolved.add(f"ambiguous-imported-symbol:{module_path}:{symbol}")
                return False
            target_path, imported_symbol = next(iter(resolved_candidates))
            import_routes.add(
                (module_path, canonical_module_name(target_path), imported_symbol)
            )
            resolution_key = (module_path, symbol)
            if resolution_key in resolving_imports:
                unresolved.add(f"cyclic-imported-symbol:{module_path}:{symbol}")
                return False
            resolving_imports.add(resolution_key)
            try:
                return enqueue_symbol(target_path, imported_symbol)
            finally:
                resolving_imports.remove(resolution_key)

        def resolve_loaded_names(module_path: str, syntax: ast.AST) -> None:
            info = parse_module(module_path)
            if info is None:
                return
            for node in ast.walk(syntax):
                if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
                    name = node.id
                    if enqueue_symbol(module_path, name):
                        continue
                    imported_candidates = info["imported_names"].get(name)
                    if not imported_candidates:
                        continue
                    resolved_candidates = {
                        (target_path, imported_symbol)
                        for imported_module, imported_symbol in imported_candidates
                        if (target_path := repository_module_path(imported_module))
                        is not None
                    }
                    if not resolved_candidates:
                        continue
                    if len(resolved_candidates) != 1:
                        unresolved.add(
                            f"ambiguous-imported-symbol:{module_path}:{name}"
                        )
                        continue
                    target_path, imported_symbol = next(iter(resolved_candidates))
                    import_routes.add(
                        (
                            module_path,
                            canonical_module_name(target_path),
                            imported_symbol,
                        )
                    )
                    if not enqueue_symbol(target_path, imported_symbol):
                        unresolved.add(
                            "missing-imported-symbol:"
                            f"{target_path}:{imported_symbol}"
                        )
                elif isinstance(node, ast.Attribute) and isinstance(
                    node.value, ast.Name
                ):
                    imported_candidates = info["imported_modules"].get(
                        node.value.id
                    )
                    if not imported_candidates:
                        continue
                    resolved_candidates = {
                        target_path
                        for imported_module in imported_candidates
                        if (target_path := repository_module_path(imported_module))
                        is not None
                    }
                    if not resolved_candidates:
                        continue
                    if len(resolved_candidates) != 1:
                        unresolved.add(
                            "ambiguous-imported-module:"
                            f"{module_path}:{node.value.id}"
                        )
                        continue
                    target_path = next(iter(resolved_candidates))
                    import_routes.add(
                        (module_path, canonical_module_name(target_path), node.attr)
                    )
                    if not enqueue_symbol(target_path, node.attr):
                        unresolved.add(
                            "missing-imported-attribute:"
                            f"{target_path}:{node.attr}"
                        )

        for statement in fresh_statements:
            resolve_loaded_names(normalized_entry, statement)
        seen: set[tuple[str, str, str]] = set()
        while pending:
            module_path, kind, symbol = pending.pop(0)
            key = (module_path, kind, symbol)
            if key in seen:
                continue
            seen.add(key)
            info = parse_module(module_path)
            if info is None:
                continue
            table = (
                info["definitions"] if kind == "definition" else info["constants"]
            )
            syntax = table.get(symbol)
            if syntax is None:
                unresolved.add(f"missing-reached-symbol:{module_path}:{symbol}")
                continue
            reached.setdefault(module_path, {})[(kind, symbol)] = syntax
            resolve_loaded_names(module_path, syntax)

        normalized = {
            "schema": SOURCE_RECORD_RAW_PRODUCER_CODE_IDENTITY_SCHEMA,
            "fresh_generation_statements": [
                ast.dump(statement, annotate_fields=True, include_attributes=False)
                for statement in fresh_statements
            ],
            "repository_import_routes": sorted(import_routes),
            "modules": [
                {
                    "path": module_path,
                    "members": [
                        {
                            "kind": kind,
                            "name": name,
                            "syntax": ast.dump(
                                syntax,
                                annotate_fields=True,
                                include_attributes=False,
                            ),
                        }
                        for (kind, name), syntax in sorted(members.items())
                    ],
                }
                for module_path, members in sorted(reached.items())
            ],
        }
        encoded = json.dumps(
            normalized, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
    except (OSError, SyntaxError, UnicodeDecodeError, ValueError):
        return {"path": display_path, "sha256": "", "status": "unavailable"}
    if unresolved:
        return {"path": display_path, "sha256": "", "status": "unavailable"}
    return {
        "path": display_path,
        "sha256": hashlib.sha256(encoded).hexdigest(),
        "status": "present",
    }


def raw_producer_code_identities(
    read_bytes: SourceReader,
    *,
    entry_path: str = SOURCE_RECORD_RAW_PRODUCER_ENTRY_PATH,
    display_path: str = SOURCE_RECORD_RAW_PRODUCER_DISPLAY_PATH,
    external_paths: tuple[str, ...] = SOURCE_RECORD_RAW_PRODUCER_EXTERNAL_CODE_PATHS,
) -> list[dict[str, str]]:
    """Return the complete deterministic raw-producer identity set."""

    identities = [
        raw_generation_code_identity(
            read_bytes,
            entry_path=entry_path,
            display_path=display_path,
        )
    ]
    identities.extend(_file_identity(read_bytes, path) for path in external_paths)
    return sorted(identities, key=lambda identity: identity["path"])
