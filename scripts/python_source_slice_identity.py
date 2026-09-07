#!/usr/bin/env python3
"""Content identities for transitive top-level Python source slices."""

from __future__ import annotations

import ast
import hashlib
import json
import os
from pathlib import Path
from typing import Iterable


SOURCE_SLICE_IDENTITY_SCHEMA = 2
_DYNAMIC_NAMESPACE_NAMES = frozenset(
    {"__import__", "eval", "exec", "globals"}
)
_DYNAMIC_NAMESPACE_ATTRIBUTES = frozenset({"__dict__", "__globals__"})
_PROJECT_ROOT_MARKERS = (".git", "pyproject.toml", "setup.cfg", "setup.py")


def _canonical_json_sha256(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def _target_names(target: ast.expr) -> set[str]:
    if isinstance(target, ast.Name):
        return {target.id}
    if isinstance(target, (ast.List, ast.Tuple)):
        return {
            name
            for element in target.elts
            for name in _target_names(element)
        }
    return set()


def _package_import_fallback_names(statement: ast.stmt) -> set[str]:
    """Recognize one semantically identical package/direct import fallback.

    Repository CLIs may be imported as ``scripts.module`` or executed from the
    ``scripts`` directory.  The conventional ``if __package__`` form names the
    same sibling module and imports the same symbols in both branches.  Treat
    that exact form as one deterministic provider.  Every other conditional
    definition remains hidden and therefore fails closed.
    """

    if (
        not isinstance(statement, ast.If)
        or not isinstance(statement.test, ast.Name)
        or statement.test.id != "__package__"
        or not isinstance(statement.test.ctx, ast.Load)
        or len(statement.body) != 1
        or len(statement.orelse) != 1
        or not isinstance(statement.body[0], ast.ImportFrom)
        or not isinstance(statement.orelse[0], ast.ImportFrom)
    ):
        return set()
    package_import = statement.body[0]
    direct_import = statement.orelse[0]
    if (
        package_import.level != 1
        or direct_import.level != 0
        or not package_import.module
        or package_import.module != direct_import.module
    ):
        return set()
    package_aliases = tuple(
        (alias.name, alias.asname) for alias in package_import.names
    )
    direct_aliases = tuple((alias.name, alias.asname) for alias in direct_import.names)
    if (
        not package_aliases
        or package_aliases != direct_aliases
        or any(name == "*" for name, _alias in package_aliases)
    ):
        return set()
    return {alias or name for name, alias in package_aliases}


def _provided_names(statement: ast.stmt) -> set[str]:
    if isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {statement.name}
    if isinstance(statement, ast.Import):
        return {
            alias.asname or alias.name.split(".", 1)[0]
            for alias in statement.names
        }
    if isinstance(statement, ast.ImportFrom):
        if any(alias.name == "*" for alias in statement.names):
            return set()
        return {alias.asname or alias.name for alias in statement.names}
    if isinstance(statement, ast.Assign):
        return {
            name
            for target in statement.targets
            for name in _target_names(target)
        }
    if isinstance(statement, (ast.AnnAssign, ast.AugAssign)):
        return _target_names(statement.target)
    package_fallback = _package_import_fallback_names(statement)
    if package_fallback:
        return package_fallback
    return set()


def _has_hidden_top_level_provider(statement: ast.stmt) -> bool:
    """Reject conditional providers that the static index cannot disambiguate."""

    if isinstance(statement, ast.Pass):
        return False
    if isinstance(statement, ast.Expr):
        return not (
            isinstance(statement.value, ast.Constant)
            and isinstance(statement.value.value, str)
        )
    provider_nodes = (
        ast.FunctionDef,
        ast.AsyncFunctionDef,
        ast.ClassDef,
        ast.Import,
        ast.ImportFrom,
        ast.Assign,
        ast.AnnAssign,
        ast.AugAssign,
    )
    return any(
        child is not statement and isinstance(child, provider_nodes)
        for child in ast.walk(statement)
    )


def _source_slice_has_dynamic_namespace_access(statement: ast.AST) -> bool:
    import_module_aliases = {
        alias.asname or alias.name
        for node in ast.walk(statement)
        if isinstance(node, ast.ImportFrom)
        and node.level == 0
        and node.module == "importlib"
        for alias in node.names
        if alias.name == "import_module"
    }
    importlib_aliases = {
        alias.asname or alias.name
        for node in ast.walk(statement)
        if isinstance(node, ast.Import)
        for alias in node.names
        if alias.name == "importlib"
    }
    for node in ast.walk(statement):
        if (
            isinstance(node, ast.Name)
            and isinstance(node.ctx, ast.Load)
            and node.id in _DYNAMIC_NAMESPACE_NAMES
        ):
            return True
        if (
            isinstance(node, ast.Attribute)
            and node.attr in _DYNAMIC_NAMESPACE_ATTRIBUTES
        ):
            return True
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in import_module_aliases
        ):
            return True
        if (
            isinstance(node, ast.Attribute)
            and node.attr == "modules"
            and isinstance(node.value, ast.Name)
            and node.value.id == "sys"
        ):
            return True
        if (
            isinstance(node, ast.Attribute)
            and node.attr == "import_module"
            and isinstance(node.value, ast.Name)
            and node.value.id in importlib_aliases
        ):
            return True
    return False


def _local_import_roots(source_path: Path) -> tuple[Path, ...]:
    """Return deterministic source-tree roots for sibling/absolute imports."""

    try:
        source_parent = source_path.resolve().parent
    except OSError:
        return ()
    roots = [source_parent]
    for candidate in (source_parent, *source_parent.parents):
        if any((candidate / marker).exists() for marker in _PROJECT_ROOT_MARKERS):
            roots.append(candidate)
            break
    return tuple(dict.fromkeys(roots))


def _module_file_candidates(base: Path, parts: tuple[str, ...]) -> set[Path]:
    """Return existing Python implementations for one local module coordinate."""

    target = base.joinpath(*parts)
    candidates = (
        (target / "__init__.py",)
        if not parts
        else (target.with_suffix(".py"), target / "__init__.py")
    )
    resolved: set[Path] = set()
    for candidate in candidates:
        try:
            path = candidate.resolve()
        except OSError:
            continue
        if path.is_file():
            resolved.add(path)
    return resolved


def _module_implementation_files(
    base: Path, parts: tuple[str, ...]
) -> tuple[set[Path], bool]:
    """Return one module implementation plus executed parent package files."""

    primary = _module_file_candidates(base, parts)
    if len(primary) > 1:
        return set(), True
    if not primary:
        return set(), False
    implementations = set(primary)
    for index in range(1, len(parts)):
        try:
            initializer = (
                base.joinpath(*parts[:index]) / "__init__.py"
            ).resolve()
        except OSError:
            return set(), True
        if initializer.is_file():
            implementations.add(initializer)
    return implementations, False


def _absolute_local_module_files(
    module_name: str,
    local_roots: tuple[Path, ...],
) -> tuple[set[Path], bool]:
    """Resolve an absolute import within the source tree, rejecting ambiguity."""

    parts = tuple(part for part in module_name.split(".") if part)
    if not parts or ".".join(parts) != module_name:
        return set(), True
    found: set[Path] = set()
    primary_files: set[Path] = set()
    for root in local_roots:
        primary = _module_file_candidates(root, parts)
        implementations, ambiguous = _module_implementation_files(root, parts)
        if ambiguous:
            return set(), True
        primary_files.update(primary)
        found.update(implementations)
    return (found, len(primary_files) > 1)


def _relative_import_base(
    current_path: Path,
    level: int,
    local_roots: tuple[Path, ...],
) -> Path | None:
    """Resolve a relative import package base without escaping the source tree."""

    if level < 1:
        return None
    try:
        base = current_path.resolve().parent
        for _index in range(level - 1):
            base = base.parent
        resolved_roots = tuple(root.resolve() for root in local_roots)
    except OSError:
        return None
    if not any(base == root or base.is_relative_to(root) for root in resolved_roots):
        return None
    return base


def _resolved_local_import_files(
    statement: ast.Import | ast.ImportFrom,
    current_path: Path,
    local_roots: tuple[Path, ...],
) -> tuple[set[Path], bool]:
    """Resolve local implementations for one import; boolean means fail closed."""

    resolved: set[Path] = set()
    if isinstance(statement, ast.Import):
        for alias in statement.names:
            found, ambiguous = _absolute_local_module_files(alias.name, local_roots)
            if ambiguous:
                return set(), True
            resolved.update(found)
        return resolved, False

    if statement.module == "__future__" and statement.level == 0:
        return set(), False
    alias_names = tuple(
        alias.name for alias in statement.names if alias.name != "*"
    )
    if statement.level:
        base = _relative_import_base(current_path, statement.level, local_roots)
        if base is None:
            return set(), True
        prefix = tuple(statement.module.split(".")) if statement.module else ()
        module_files, ambiguous = _module_implementation_files(base, prefix)
        if ambiguous:
            return set(), True
        if not prefix:
            try:
                module_files.discard(current_path.resolve(strict=True))
            except OSError:
                return set(), True
        resolved.update(module_files)
        for alias_name in alias_names:
            child_files, child_ambiguous = _module_implementation_files(
                base, (*prefix, *alias_name.split("."))
            )
            if child_ambiguous:
                return set(), True
            resolved.update(child_files)
        # A relative import cannot be delegated to an unrelated external
        # package. Missing local implementation evidence therefore fails.
        if not resolved:
            return set(), True
        return resolved, False

    if not statement.module:
        return set(), True
    module_files, ambiguous = _absolute_local_module_files(
        statement.module, local_roots
    )
    if ambiguous:
        return set(), True
    resolved.update(module_files)
    for alias_name in alias_names:
        child_files, child_ambiguous = _absolute_local_module_files(
            f"{statement.module}.{alias_name}", local_roots
        )
        if child_ambiguous:
            return set(), True
        resolved.update(child_files)
    return resolved, False


def _transitive_local_import_identities(
    source_path: Path,
    reached_statements: Iterable[ast.stmt],
) -> list[dict[str, str]] | None:
    """Bind recursively imported source-tree modules by their complete bytes."""

    local_roots = _local_import_roots(source_path)
    if not local_roots:
        return None
    try:
        initial_path = source_path.resolve(strict=True)
    except OSError:
        return None
    pending: list[Path] = []
    for reached in reached_statements:
        for statement in ast.walk(reached):
            if not isinstance(statement, (ast.Import, ast.ImportFrom)):
                continue
            found, failed = _resolved_local_import_files(
                statement, initial_path, local_roots
            )
            if failed:
                return None
            pending.extend(found)

    identities: dict[Path, dict[str, str]] = {}
    while pending:
        raw_path = pending.pop()
        try:
            path = raw_path.resolve(strict=True)
        except OSError:
            return None
        if path == initial_path:
            # A local import cycle back into the partially initialized root
            # module cannot be represented by a root-only provider slice.
            return None
        if path in identities:
            continue
        try:
            content = path.read_bytes()
            imported_module = ast.parse(
                content.decode("utf-8"), filename=str(path)
            )
        except (OSError, SyntaxError, UnicodeError):
            return None
        if _source_slice_has_dynamic_namespace_access(imported_module):
            return None
        identities[path] = {
            "path": Path(
                os.path.relpath(path, start=initial_path.parent)
            ).as_posix(),
            "sha256": hashlib.sha256(content).hexdigest(),
        }
        for statement in ast.walk(imported_module):
            if not isinstance(statement, (ast.Import, ast.ImportFrom)):
                continue
            found, failed = _resolved_local_import_files(
                statement, path, local_roots
            )
            if failed:
                return None
            pending.extend(found)
    return sorted(identities.values(), key=lambda item: item["path"])


def transitive_top_level_source_slice_identity(
    source_path: Path,
    roots: Iterable[str],
) -> dict[str, str] | None:
    """Hash exactly the top-level AST providers reachable from ``roots``.

    The result is fail-closed. Duplicate or conditionally defined providers,
    wildcard imports, missing roots, and dynamic module-namespace access do
    not receive an identity. References to ordinary local variables and
    builtins remain outside the top-level provider graph.
    """

    root_names = tuple(sorted(set(roots)))
    if not root_names or any(not name.isidentifier() for name in root_names):
        return None
    try:
        source = source_path.read_text(encoding="utf-8")
        module = ast.parse(source, filename=str(source_path))
        builder_sha256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    except (OSError, SyntaxError, UnicodeError):
        return None

    providers: dict[str, ast.stmt] = {}
    provider_names_by_node: dict[int, set[str]] = {}
    statement_order = {
        id(statement): index for index, statement in enumerate(module.body)
    }
    future_features = [
        ast.dump(
            statement,
            annotate_fields=True,
            include_attributes=False,
        )
        for statement in module.body
        if isinstance(statement, ast.ImportFrom)
        and statement.level == 0
        and statement.module == "__future__"
    ]
    for statement in module.body:
        names = _provided_names(statement)
        if isinstance(statement, ast.ImportFrom) and any(
            alias.name == "*" for alias in statement.names
        ):
            return None
        if not names:
            if _has_hidden_top_level_provider(statement):
                return None
            continue
        for name in names:
            prior = providers.get(name)
            if prior is not None and prior is not statement:
                return None
            providers[name] = statement
        provider_names_by_node.setdefault(id(statement), set()).update(names)

    if any(root not in providers for root in root_names):
        return None

    pending = list(reversed(root_names))
    reached_nodes: dict[int, ast.stmt] = {}
    while pending:
        symbol = pending.pop()
        statement = providers[symbol]
        statement_id = id(statement)
        if statement_id in reached_nodes:
            continue
        if _source_slice_has_dynamic_namespace_access(statement):
            return None
        reached_nodes[statement_id] = statement
        dependencies = sorted(
            {
                node.id
                for node in ast.walk(statement)
                if isinstance(node, ast.Name)
                and isinstance(node.ctx, ast.Load)
                and node.id in providers
            },
            reverse=True,
        )
        pending.extend(dependencies)

    reached_module = ast.Module(
        body=list(reached_nodes.values()), type_ignores=[]
    )
    if _source_slice_has_dynamic_namespace_access(reached_module):
        return None
    local_import_identities = _transitive_local_import_identities(
        source_path, reached_nodes.values()
    )
    if local_import_identities is None:
        return None
    entries = [
            {
                "symbols": sorted(provider_names_by_node[id(statement)]),
                "ast": ast.dump(
                    statement,
                    annotate_fields=True,
                    include_attributes=False,
                ),
            }
            for statement in sorted(
                reached_nodes.values(), key=lambda item: statement_order[id(item)]
            )
    ]
    reached_symbols = sorted(
        symbol
        for statement_id in reached_nodes
        for symbol in provider_names_by_node[statement_id]
    )
    payload = {
        "schema": SOURCE_SLICE_IDENTITY_SCHEMA,
        "roots": list(root_names),
        "future_features": future_features,
        "providers": entries,
        "local_imports": local_import_identities,
    }
    return {
        "schema": str(SOURCE_SLICE_IDENTITY_SCHEMA),
        "identity_builder_sha256": builder_sha256,
        "roots_sha256": _canonical_json_sha256(list(root_names)),
        "symbols_sha256": _canonical_json_sha256(reached_symbols),
        "symbol_count": str(len(reached_symbols)),
        "local_imports_sha256": _canonical_json_sha256(
            local_import_identities
        ),
        "local_import_count": str(len(local_import_identities)),
        "source_slice_sha256": _canonical_json_sha256(payload),
    }
