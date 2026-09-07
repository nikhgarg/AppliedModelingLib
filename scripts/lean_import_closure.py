#!/usr/bin/env python3
"""Validate Lean imports and identify exact worktree dependency closures.

The source parser below is a diagnostic check for candidate-tree omissions.
Credited closure membership instead comes from Lean's loaded module header after
Lake builds and Lean imports one exact entrypoint. Python only maps those
Lean-emitted module identities to unique tracked worktree paths, rejects dirty
or ambiguous ownership, hashes exact bytes and controls, and memoizes results.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Callable, Iterable, Mapping

try:
    from scripts.tomllib_compat import tomllib
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from tomllib_compat import tomllib


ROOT = Path(__file__).resolve().parents[1]
IMPORT_LINE_RE = re.compile(r"^[ \t]*import[ \t]+([^\r\n]+)$", re.MULTILINE)
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
EXTERNAL_MODULE_PREFIXES = frozenset(
    {
        # Lean core plus the package roots pinned by lake-manifest.json.
        "Init",
        "Lean",
        "Std",
        "Lake",
        "Mathlib",
        "Cslib",
        "Plausible",
        "LeanSearchClient",
        "ImportGraph",
        "ProofWidgets",
        "Aesop",
        "Qq",
        "Batteries",
        "Cli",
        # Immutable direct Lake dependency; attribution and Apache-2.0 audit
        # are recorded in docs/UPSTREAM_LEAN_SOURCES.md.
        "Vlasov",
    }
)
LEAN_IMPORT_GRAPH_HELPER = "scripts/lean_import_graph_helper.lean"
WORKTREE_IDENTITY_CONTROL_PATHS = (
    "lean-toolchain",
    "lake-manifest.json",
)
LEGACY_WORKTREE_IDENTITY_CONTROL_PATHS = (
    *WORKTREE_IDENTITY_CONTROL_PATHS,
    LEAN_IMPORT_GRAPH_HELPER,
)
WORKTREE_IDENTITY_SCHEMA = "econcslib.lean-loaded-import-closure/v2"
LEAN_IMPORT_CLOSURE_RECEIPT_SCHEMA = 1
LEAN_IMPORT_GRAPH_MARKER = "APPLIEDMODELINGLIB_LEAN_IMPORT_CLOSURE "
LEAN_IMPORT_GRAPH_SCHEMA = "econcslib.lean-loaded-module-closure/v1"
DEFAULT_LEAN_GRAPH_TIMEOUT_SECONDS = 600
LAKE_ROUTING_SCHEMA = "econcslib.entry-module-lake-routing/v2"
LAKE_ADMINISTRATIVE_PACKAGE_FIELDS = frozenset(
    {
        "defaultTargets",
        "description",
        "homepage",
        "keywords",
        "license",
        "licenseFiles",
        "readmeFile",
        "reservoir",
        "version",
    }
)


@dataclass(frozen=True)
class ImportClosureIssue:
    entrypoint: str
    importer: str
    imported_module: str
    dependency_path: str
    reason: str

    def format(self) -> str:
        dependency = f" ({self.dependency_path})" if self.dependency_path else ""
        return (
            f"{self.entrypoint}: {self.importer} imports {self.imported_module}"
            f"{dependency}: {self.reason}"
        )


@dataclass(frozen=True)
class ExternalArtifactFileState:
    """Runtime-only mutation guard for one exactly hashed external artifact."""

    module: str
    path: Path
    device: int
    inode: int
    byte_length: int
    mtime_ns: int
    ctime_ns: int

    @classmethod
    def from_stat(
        cls,
        module: str,
        path: Path,
        value: os.stat_result,
    ) -> "ExternalArtifactFileState":
        return cls(
            module=module,
            path=path,
            device=value.st_dev,
            inode=value.st_ino,
            byte_length=value.st_size,
            mtime_ns=value.st_mtime_ns,
            ctime_ns=value.st_ctime_ns,
        )

    def current_problem(self) -> str:
        try:
            current = ExternalArtifactFileState.from_stat(
                self.module,
                self.path,
                self.path.stat(),
            )
        except OSError as exc:
            return (
                "loaded external module artifact cannot be restated: "
                f"{self.module}: {exc}"
            )
        if current != self:
            return (
                "loaded external module artifact changed after exact hashing: "
                + self.module
            )
        return ""


@dataclass(frozen=True)
class ExternalModuleArtifactSnapshot:
    """Exact content identities plus a non-serialized transaction guard."""

    module_records: tuple[tuple[str, int, str], ...]
    file_states: tuple[ExternalArtifactFileState, ...]

    def records(self) -> list[dict[str, object]]:
        return [
            {"module": module, "byte_length": byte_length, "sha256": sha256}
            for module, byte_length, sha256 in self.module_records
        ]

    def current_problem(
        self,
        *,
        search_snapshot: ExternalArtifactSearchSnapshot | None = None,
    ) -> str:
        if search_snapshot is not None:
            expected_paths_by_module: dict[str, list[Path]] = {}
            for state in self.file_states:
                expected_paths_by_module.setdefault(state.module, []).append(
                    state.path
                )
            for module, _byte_length, _sha256 in self.module_records:
                current_paths = tuple(
                    sorted(
                        path
                        for _role, path in search_snapshot.candidates(module)
                    )
                )
                if current_paths != tuple(
                    sorted(expected_paths_by_module.get(module, []))
                ):
                    return (
                        "loaded external module artifact candidate set changed: "
                        + module
                    )
        for state in self.file_states:
            problem = state.current_problem()
            if problem:
                return problem
        return ""


@dataclass(frozen=True)
class ExternalArtifactSearchSnapshot:
    """One bounded inventory of possible external artifact namespace roots."""

    roots: tuple[
        tuple[str, Path, frozenset[str], frozenset[str]], ...
    ]

    def candidates(self, module: str) -> tuple[tuple[str, Path], ...]:
        if not MODULE_RE.fullmatch(module):
            return ()
        parts = module.split(".")
        candidates: list[tuple[str, Path]] = []
        for role, root, direct_modules, prefixes in self.roots:
            if len(parts) == 1:
                if parts[0] in direct_modules:
                    candidates.append((role, root / f"{parts[0]}.olean"))
                continue
            if parts[0] not in prefixes:
                continue
            candidate = root.joinpath(*parts).with_suffix(".olean")
            if candidate.is_file():
                candidates.append((role, candidate))
        return tuple(candidates)


@dataclass(frozen=True)
class ImportClosureIdentityProblem:
    """Structured reason why a worktree closure identity is unavailable."""

    code: str
    entrypoint: str
    importer: str
    imported_module: str = ""
    dependency_path: str = ""
    reason: str = ""

    def format(self) -> str:
        subject = self.importer
        if self.imported_module:
            subject += f" imports {self.imported_module}"
        if self.dependency_path:
            subject += f" ({self.dependency_path})"
        return f"{self.entrypoint}: {subject}: {self.reason} [{self.code}]"


class ImportClosureIdentityError(RuntimeError):
    """Raised when a strict caller requests an unavailable closure identity."""

    def __init__(self, problem: ImportClosureIdentityProblem) -> None:
        self.problem = problem
        super().__init__(problem.format())


def _stable_sha256(value: object) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def validated_lean_import_closure_payload(value: object) -> dict[str, object]:
    """Validate and canonicalize one closure emitted under Lean authority."""

    expected = {
        "schema",
        "entrypoint",
        "entry_module",
        "lean_loaded_modules",
        "sources",
        "external_import_modules",
        "external_module_artifacts_sha256",
        "build_controls",
        "lake_routing",
    }
    if not isinstance(value, Mapping) or set(value) != expected:
        raise ValueError("Lean import-closure payload fields are malformed")
    if value.get("schema") != WORKTREE_IDENTITY_SCHEMA:
        raise ValueError("Lean import-closure payload schema is unsupported")
    entrypoint = str(value.get("entrypoint") or "").strip()
    entry_module = str(value.get("entry_module") or "").strip()
    if module_name_for_path(entrypoint) != entry_module:
        raise ValueError("Lean import-closure entrypoint association is invalid")

    raw_modules = value.get("lean_loaded_modules")
    if not isinstance(raw_modules, list):
        raise ValueError("Lean import-closure module set is malformed")
    modules = [str(module).strip() for module in raw_modules]
    module_set = set(modules)
    if (
        not modules
        or modules != sorted(modules)
        or len(modules) != len(module_set)
        or any(not MODULE_RE.fullmatch(module) for module in modules)
        or entry_module not in modules
    ):
        raise ValueError("Lean import-closure module set is invalid")

    raw_sources = value.get("sources")
    if not isinstance(raw_sources, list):
        raise ValueError("Lean import-closure source association is malformed")
    sources: list[dict[str, object]] = []
    seen_source_modules: set[str] = set()
    seen_source_paths: set[str] = set()
    for index, raw in enumerate(raw_sources):
        if not isinstance(raw, Mapping) or set(raw) != {
            "module",
            "path",
            "byte_length",
            "sha256",
        }:
            raise ValueError(f"Lean import-closure source {index} is malformed")
        module = str(raw.get("module") or "").strip()
        path = str(raw.get("path") or "").strip()
        digest = str(raw.get("sha256") or "").strip().lower()
        byte_length = raw.get("byte_length")
        if (
            module not in module_set
            or module_name_for_path(path) != module
            or module in seen_source_modules
            or path in seen_source_paths
            or not isinstance(byte_length, int)
            or byte_length < 0
            or not re.fullmatch(r"[0-9a-f]{64}", digest)
        ):
            raise ValueError(
                f"Lean import-closure source {index} association is invalid"
            )
        seen_source_modules.add(module)
        seen_source_paths.add(path)
        sources.append(
            {
                "module": module,
                "path": path,
                "byte_length": byte_length,
                "sha256": digest,
            }
        )
    sources.sort(key=lambda item: str(item["path"]))
    if value.get("sources") != sources:
        raise ValueError("Lean import-closure source association is not canonical")
    if entry_module not in seen_source_modules or entrypoint not in seen_source_paths:
        raise ValueError("Lean import-closure omits its repository entrypoint source")

    raw_external = value.get("external_import_modules")
    if not isinstance(raw_external, list):
        raise ValueError("Lean import-closure external module set is malformed")
    external = [str(module).strip() for module in raw_external]
    external_set = set(external)
    if (
        external != sorted(external)
        or len(external) != len(external_set)
        or not external_set.issubset(module_set)
        or seen_source_modules.intersection(external_set)
        or module_set != seen_source_modules.union(external_set)
    ):
        raise ValueError("Lean import-closure module ownership partition is invalid")

    external_artifact_sha256 = (
        str(value.get("external_module_artifacts_sha256") or "").strip().lower()
    )
    if not re.fullmatch(r"[0-9a-f]{64}", external_artifact_sha256):
        raise ValueError("Lean import-closure external artifact identity is invalid")

    raw_controls = value.get("build_controls")
    if not isinstance(raw_controls, list):
        raise ValueError("Lean import-closure build controls are malformed")
    raw_control_paths = tuple(
        str(raw.get("path") or "") if isinstance(raw, Mapping) else ""
        for raw in raw_controls
    )
    if raw_control_paths not in {
        WORKTREE_IDENTITY_CONTROL_PATHS,
        LEGACY_WORKTREE_IDENTITY_CONTROL_PATHS,
    }:
        raise ValueError("Lean import-closure build controls are malformed")
    controls: list[dict[str, object]] = []
    for expected_path, raw in zip(raw_control_paths, raw_controls):
        if not isinstance(raw, Mapping):
            raise ValueError("Lean import-closure build control is malformed")
        path_kind = str(raw.get("path_kind") or "")
        expected_fields = {
            "path",
            "tracked_in_index",
            "untracked",
            "path_kind",
            "byte_length",
            "sha256",
        }
        if set(raw) != expected_fields:
            raise ValueError("Lean import-closure build control fields are malformed")
        digest = str(raw.get("sha256") or "").strip().lower()
        if (
            raw.get("path") != expected_path
            or raw.get("tracked_in_index") is not True
            or raw.get("untracked") is not False
            or path_kind != "file"
            or not isinstance(raw.get("byte_length"), int)
            or isinstance(raw.get("byte_length"), bool)
            or int(raw["byte_length"]) < 0
            or not re.fullmatch(r"[0-9a-f]{64}", digest)
        ):
            raise ValueError("Lean import-closure build control is invalid")
        controls.append(dict(raw))

    lake_routing = value.get("lake_routing")
    if (
        not isinstance(lake_routing, Mapping)
        or lake_routing.get("schema") != LAKE_ROUTING_SCHEMA
    ):
        raise ValueError("Lean import-closure Lake routing projection is malformed")
    routing_kind = lake_routing.get("kind")
    if routing_kind == "toml":
        if set(lake_routing) != {
            "schema",
            "kind",
            "package_configuration",
            "lean_library",
        }:
            raise ValueError("Lean import-closure TOML routing fields are malformed")
        package_configuration = lake_routing.get("package_configuration")
        if (
            not isinstance(package_configuration, Mapping)
            or not isinstance(package_configuration.get("name"), str)
            or not str(package_configuration["name"]).strip()
            or not isinstance(lake_routing.get("lean_library"), Mapping)
            or lake_routing["lean_library"].get("name") != entry_module.split(".", 1)[0]
        ):
            raise ValueError("Lean import-closure TOML routing association is invalid")
    elif routing_kind == "lean":
        if set(lake_routing) != {"schema", "kind", "sha256", "byte_length"}:
            raise ValueError("Lean import-closure dynamic routing fields are malformed")
        if (
            not isinstance(lake_routing.get("byte_length"), int)
            or int(lake_routing["byte_length"]) < 0
            or not re.fullmatch(r"[0-9a-f]{64}", str(lake_routing.get("sha256") or ""))
        ):
            raise ValueError("Lean import-closure dynamic routing identity is invalid")
    else:
        raise ValueError("Lean import-closure Lake routing kind is unsupported")
    canonical_routing = json.loads(
        json.dumps(lake_routing, sort_keys=True, separators=(",", ":"))
    )

    return {
        "schema": WORKTREE_IDENTITY_SCHEMA,
        "entrypoint": entrypoint,
        "entry_module": entry_module,
        "lean_loaded_modules": modules,
        "sources": sources,
        "external_import_modules": external,
        "external_module_artifacts_sha256": external_artifact_sha256,
        "build_controls": controls,
        "lake_routing": canonical_routing,
    }


def durable_lean_build_control_records(
    controls: object,
) -> list[dict[str, object]]:
    """Project validated controls onto paper-semantic build inputs.

    Early v2 receipts included the Lean graph reporter itself.  Preserve that
    exact legacy record for receipt authentication, but never let its current
    bytes reopen paper evidence or enter a new operational input snapshot.
    """

    if not isinstance(controls, list):
        raise ValueError("Lean import-closure build controls are malformed")
    return [
        dict(raw)
        for raw in controls
        if isinstance(raw, Mapping)
        and str(raw.get("path") or "") in WORKTREE_IDENTITY_CONTROL_PATHS
    ]


def durable_lake_routing_projection(routing: object) -> dict[str, object]:
    """Remove only retired administrative TOML fields from routing identity.

    Early v2 receipts retained package presentation metadata. Preserve those
    raw receipt bytes and hashes, but compare saved and current routing through
    the same semantic projection. Dynamic Lake files remain exact-byte inputs.
    """

    if not isinstance(routing, Mapping):
        raise ValueError("Lean import-closure Lake routing projection is malformed")
    projection = dict(routing)
    if projection.get("kind") == "toml":
        package = projection.get("package_configuration")
        if not isinstance(package, Mapping):
            raise ValueError("Lean import-closure TOML routing fields are malformed")
        projection["package_configuration"] = {
            str(key): value
            for key, value in package.items()
            if str(key) not in LAKE_ADMINISTRATIVE_PACKAGE_FIELDS
        }
    try:
        return json.loads(
            json.dumps(projection, sort_keys=True, separators=(",", ":"))
        )
    except (TypeError, ValueError) as exc:
        raise ValueError("Lean import-closure Lake routing is not canonical JSON") from exc


def lean_import_closure_payload_sha256(value: object) -> str:
    return _stable_sha256(validated_lean_import_closure_payload(value))


def lean_import_closure_source_only_recovery_problem(
    accepted: object,
    current: object,
) -> str:
    """Explain why two closures differ by more than repository source bytes."""

    accepted_closure = validated_lean_import_closure_payload(accepted)
    current_closure = validated_lean_import_closure_payload(current)
    immutable_fields = (
        "schema",
        "entrypoint",
        "entry_module",
        "lean_loaded_modules",
        "external_import_modules",
        "external_module_artifacts_sha256",
        "build_controls",
        "lake_routing",
    )
    for field in immutable_fields:
        if accepted_closure[field] != current_closure[field]:
            return f"Lean import-closure {field} changed"
    accepted_sources = [
        {"module": row["module"], "path": row["path"]}
        for row in accepted_closure["sources"]
    ]
    current_sources = [
        {"module": row["module"], "path": row["path"]}
        for row in current_closure["sources"]
    ]
    if accepted_sources != current_sources:
        return "Lean import-closure repository source ownership changed"
    return ""


def lean_import_closure_receipt_payload(
    paper: str, closure: object
) -> dict[str, object]:
    """Wrap one Lean-owned closure in its portable non-accepting carrier."""

    paper_id = str(paper).strip()
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", paper_id):
        raise ValueError("Lean import-closure receipt paper identity is malformed")
    validated = validated_lean_import_closure_payload(closure)
    actual_entrypoint = str(validated.get("entrypoint") or "").strip()
    allowed_entrypoints = {
        f"papers/{paper_id}.lean",
        f"papers/{paper_id}/PaperInterface.lean",
        f"papers/{paper_id}/ProofInterface.lean",
    }
    if actual_entrypoint not in allowed_entrypoints:
        raise ValueError("Lean import-closure receipt entrypoint is for another paper")
    return {
        "schema": LEAN_IMPORT_CLOSURE_RECEIPT_SCHEMA,
        "paper": paper_id,
        "acceptance_credential": False,
        "entrypoint": actual_entrypoint,
        "lean_import_closure_sha256": lean_import_closure_payload_sha256(
            validated
        ),
        "lean_import_closure": validated,
    }


def validated_lean_import_closure_receipt_payload(
    value: object, *, paper: str
) -> dict[str, object]:
    """Validate the exact portable carrier for one paper's Lean closure."""

    expected_fields = {
        "schema",
        "paper",
        "acceptance_credential",
        "entrypoint",
        "lean_import_closure_sha256",
        "lean_import_closure",
    }
    if not isinstance(value, Mapping) or set(value) != expected_fields:
        raise ValueError("Lean import-closure receipt fields are malformed")
    canonical = lean_import_closure_receipt_payload(
        paper, value.get("lean_import_closure")
    )
    if value != canonical:
        raise ValueError("Lean import-closure receipt identity is invalid")
    return canonical


def _git(repo: Path, args: list[str]) -> bytes:
    result = subprocess.run(
        ["git", *args],
        cwd=repo,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        error = result.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"git {' '.join(args)} failed: {error}")
    return result.stdout


def _nul_paths(raw: bytes) -> set[str]:
    return {
        item.decode("utf-8", errors="surrogateescape")
        for item in raw.split(b"\0")
        if item
    }


def index_paths(repo: Path) -> set[str]:
    return _nul_paths(_git(repo, ["ls-files", "-z"]))


def untracked_lean_paths(repo: Path) -> set[str]:
    return _nul_paths(
        _git(repo, ["ls-files", "--others", "--exclude-standard", "-z", "--", "*.lean"])
    )


def untracked_paths(repo: Path) -> set[str]:
    return _nul_paths(_git(repo, ["ls-files", "--others", "--exclude-standard", "-z"]))


def unstaged_paths(repo: Path) -> set[str]:
    return _nul_paths(_git(repo, ["diff", "--name-only", "-z"]))


def staged_paths(repo: Path) -> set[str]:
    return _nul_paths(
        _git(repo, ["diff", "--cached", "--name-only", "--diff-filter=ACMR", "-z"])
    )


def tree_paths(repo: Path, treeish: str) -> set[str]:
    return {
        line
        for line in _git(repo, ["ls-tree", "-r", "--name-only", "-z", treeish])
        .decode("utf-8", errors="surrogateescape")
        .split("\0")
        if line
    }


def module_name_for_path(path: str) -> str | None:
    """Map a repository Lean source path to its Lake module identity."""

    pure = PurePosixPath(path)
    if pure.suffix != ".lean":
        return None
    parts = list(pure.with_suffix("").parts)
    if parts and parts[0] == "papers":
        parts = parts[1:]
    if not parts or any(not MODULE_RE.fullmatch(part) for part in parts):
        return None
    return ".".join(parts)


def module_map(
    paths: Iterable[str],
) -> tuple[dict[str, str], dict[str, tuple[str, ...]]]:
    grouped: dict[str, list[str]] = {}
    for path in sorted(paths):
        module = module_name_for_path(path)
        if module is not None:
            grouped.setdefault(module, []).append(path)
    unique = {
        module: values[0] for module, values in grouped.items() if len(values) == 1
    }
    ambiguous = {
        module: tuple(values) for module, values in grouped.items() if len(values) > 1
    }
    return unique, ambiguous


def repository_module_candidate_map(
    tracked_paths: Iterable[str], untracked_paths: Iterable[str]
) -> dict[str, tuple[str, ...]]:
    """Return every current repository source candidate by Lean module.

    Callers compare only modules that participated in a Lean-owned receipt.
    The map may scan Git's inventories, but unrelated module additions never
    become invalidations; a same-module addition remains an ambiguity.
    """

    grouped: dict[str, set[str]] = {}
    for path in set(tracked_paths) | set(untracked_paths):
        module = module_name_for_path(path)
        if module is not None:
            grouped.setdefault(module, set()).add(path)
    return {module: tuple(sorted(paths)) for module, paths in grouped.items()}


@dataclass(frozen=True)
class RepositoryModuleOwnershipSnapshot:
    """One bounded filesystem routing snapshot for many Lean module names.

    Most modules loaded by Lean come from Mathlib or the toolchain. Probing
    both possible repository paths separately for tens of thousands of those
    modules adds no assurance when neither top-level namespace exists locally.
    Inventory those routing prefixes once, then perform exact path checks only
    for prefixes which can resolve in this repository. A closeout transaction
    takes a fresh snapshot again at finalization, so a concurrently added local
    owner still fails.
    """

    root: Path
    root_direct_modules: frozenset[str]
    root_prefixes: frozenset[str]
    papers_direct_modules: frozenset[str]
    papers_prefixes: frozenset[str]

    def candidates(self, module: str) -> tuple[Path, ...]:
        if not MODULE_RE.fullmatch(module):
            return ()
        parts = module.split(".")
        candidates: list[Path] = []
        if len(parts) == 1:
            if parts[0] in self.root_direct_modules:
                candidates.append(self.root / f"{parts[0]}.lean")
            if parts[0] in self.papers_direct_modules:
                candidates.append(self.root / "papers" / f"{parts[0]}.lean")
        else:
            if parts[0] in self.root_prefixes:
                candidate = self.root.joinpath(*parts).with_suffix(".lean")
                if candidate.is_file():
                    candidates.append(candidate)
            if parts[0] in self.papers_prefixes:
                candidate = (self.root / "papers").joinpath(*parts).with_suffix(
                    ".lean"
                )
                if candidate.is_file():
                    candidates.append(candidate)
        return tuple(sorted({path.resolve() for path in candidates}))


def repository_module_ownership_snapshot(
    root: Path,
) -> RepositoryModuleOwnershipSnapshot:
    """Capture repository namespace prefixes used for exact module routing."""

    root = root.resolve()
    papers = root / "papers"
    try:
        root_entries = tuple(root.iterdir())
        paper_entries = tuple(papers.iterdir()) if papers.is_dir() else ()
    except OSError as exc:
        raise ValueError(
            "repository module-ownership inventory is unavailable"
        ) from exc

    def direct_modules(entries: Iterable[Path]) -> frozenset[str]:
        return frozenset(
            path.stem
            for path in entries
            if path.suffix == ".lean"
            and path.is_file()
            and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", path.stem)
        )

    def prefixes(entries: Iterable[Path]) -> frozenset[str]:
        return frozenset(
            path.name
            for path in entries
            if path.is_dir() and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", path.name)
        )

    return RepositoryModuleOwnershipSnapshot(
        root=root,
        root_direct_modules=direct_modules(root_entries),
        root_prefixes=prefixes(root_entries),
        papers_direct_modules=direct_modules(paper_entries),
        papers_prefixes=prefixes(paper_entries),
    )


def lake_routing_projection(
    root: Path, entry_module: str
) -> tuple[dict[str, object] | None, str]:
    """Project only Lake semantics that route and elaborate one module.

    TOML default targets and unrelated ``lean_lib`` entries are deliberately
    excluded, which keeps a receipt portable between private and public trees.
    Every other top-level package setting is retained conservatively: options
    such as ``moreLeanArgs`` and ``weakLeanArgs`` can change discovery or
    elaboration, and an unknown setting is not assumed administrative. A
    dynamic ``lakefile.lean`` cannot be safely sliced, so its exact bytes are
    conservatively bound instead.
    """

    toml_path = root / "lakefile.toml"
    lean_path = root / "lakefile.lean"
    if toml_path.exists() and lean_path.exists():
        return None, "both lakefile.toml and lakefile.lean are present"
    if lean_path.is_file():
        try:
            content = lean_path.read_bytes()
        except OSError as exc:
            return None, f"dynamic Lake configuration cannot be read: {exc}"
        return {
            "schema": LAKE_ROUTING_SCHEMA,
            "kind": "lean",
            "byte_length": len(content),
            "sha256": hashlib.sha256(content).hexdigest(),
        }, ""
    if not toml_path.is_file():
        return None, "lakefile.toml is unavailable"
    try:
        payload = tomllib.loads(toml_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as exc:
        return None, f"Lake TOML configuration cannot be parsed: {exc}"
    root_module = entry_module.split(".", 1)[0]
    libraries = payload.get("lean_lib")
    if not isinstance(libraries, list):
        return None, "Lake TOML has no lean_lib routing table"
    matches = [
        library
        for library in libraries
        if isinstance(library, dict) and library.get("name") == root_module
    ]
    if len(matches) != 1:
        return None, "entry module has no unique Lake lean_lib routing table"
    package_name = payload.get("name")
    if not isinstance(package_name, str) or not package_name.strip():
        return None, "Lake TOML package name is malformed"
    package_configuration = {
        key: value
        for key, value in payload.items()
        if key not in LAKE_ADMINISTRATIVE_PACKAGE_FIELDS | {"lean_lib"}
    }
    projection: dict[str, object] = {
        "schema": LAKE_ROUTING_SCHEMA,
        "kind": "toml",
        "package_configuration": package_configuration,
        "lean_library": matches[0],
    }
    try:
        return json.loads(
            json.dumps(projection, sort_keys=True, separators=(",", ":"))
        ), ""
    except (TypeError, ValueError) as exc:
        return None, f"Lake TOML routing projection is not canonical JSON: {exc}"


def imported_modules(source: str) -> list[str]:
    source = _without_lean_comments(source)
    modules: list[str] = []
    for match in IMPORT_LINE_RE.finditer(source):
        statement = match.group(1).split("--", 1)[0]
        for token in statement.split():
            if MODULE_RE.fullmatch(token):
                modules.append(token)
    return modules


def _without_lean_comments(source: str) -> str:
    """Remove nested block and line comments while preserving line breaks."""

    output: list[str] = []
    index = 0
    block_depth = 0
    while index < len(source):
        if source.startswith("/-", index):
            block_depth += 1
            output.extend("  ")
            index += 2
            continue
        if block_depth and source.startswith("-/", index):
            block_depth -= 1
            output.extend("  ")
            index += 2
            continue
        if block_depth:
            output.append("\n" if source[index] == "\n" else " ")
            index += 1
            continue
        if source.startswith("--", index):
            newline = source.find("\n", index)
            if newline < 0:
                output.extend(" " * (len(source) - index))
                break
            output.extend(" " * (newline - index))
            output.append("\n")
            index = newline + 1
            continue
        output.append(source[index])
        index += 1
    return "".join(output)


def _index_text(repo: Path, path: str) -> str:
    return _git(repo, ["show", f":{path}"]).decode("utf-8", errors="replace")


def _worktree_text(repo: Path, path: str) -> str:
    return (repo / path).read_text(encoding="utf-8")


def _tree_text(repo: Path, treeish: str, path: str) -> str:
    return _git(repo, ["show", f"{treeish}:{path}"]).decode("utf-8", errors="replace")


def _candidate_blob_ids(
    repo: Path, *, candidate: str, treeish: str | None
) -> dict[str, str]:
    if candidate == "index":
        raw = _git(repo, ["ls-files", "--stage", "-z"])
        blobs: dict[str, str] = {}
        for record in raw.split(b"\0"):
            if not record or b"\t" not in record:
                continue
            metadata, raw_path = record.split(b"\t", 1)
            fields = metadata.split()
            if len(fields) != 3 or fields[2] != b"0":
                continue
            path = raw_path.decode("utf-8", errors="surrogateescape")
            if path.endswith(".lean"):
                blobs[path] = fields[1].decode("ascii")
        return blobs
    if candidate == "tree":
        raw = _git(repo, ["ls-tree", "-r", "-z", str(treeish)])
        blobs = {}
        for record in raw.split(b"\0"):
            if not record or b"\t" not in record:
                continue
            metadata, raw_path = record.split(b"\t", 1)
            fields = metadata.split()
            if len(fields) != 3 or fields[1] != b"blob":
                continue
            path = raw_path.decode("utf-8", errors="surrogateescape")
            if path.endswith(".lean"):
                blobs[path] = fields[2].decode("ascii")
        return blobs
    return {}


def _batch_blob_texts(repo: Path, blob_ids: Iterable[str]) -> dict[str, str]:
    """Read candidate sources through one Git process instead of one per file."""

    ordered = sorted(set(blob_ids))
    if not ordered:
        return {}
    result = subprocess.run(
        ["git", "cat-file", "--batch"],
        cwd=repo,
        input=("\n".join(ordered) + "\n").encode("ascii"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        error = result.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"git cat-file --batch failed: {error}")
    output = result.stdout
    offset = 0
    texts: dict[str, str] = {}
    for expected in ordered:
        newline = output.find(b"\n", offset)
        if newline < 0:
            raise RuntimeError("git cat-file --batch returned a truncated header")
        header = output[offset:newline].split()
        if len(header) != 3 or header[0].decode("ascii") != expected:
            raise RuntimeError("git cat-file --batch returned an unexpected object")
        size = int(header[2])
        start = newline + 1
        end = start + size
        if end >= len(output):
            raise RuntimeError("git cat-file --batch returned a truncated object")
        texts[expected] = output[start:end].decode("utf-8", errors="replace")
        offset = end + 1
    return texts


def default_entrypoints(indexed: set[str], changed: set[str]) -> set[str]:
    roots = {
        path
        for path in indexed
        if path.endswith("/PaperInterface.lean")
        or path == "AppliedModelingLib.lean"
        or (
            path.startswith("papers/")
            and path.count("/") == 1
            and path.endswith(".lean")
        )
    }
    roots.update(path for path in changed if path in indexed and path.endswith(".lean"))
    return roots


LeanModuleGraphLoader = Callable[[Path, str, int], tuple[tuple[str, ...] | None, str]]


def single_threaded_lean_build_environment() -> dict[str, str]:
    """Bound native Lake/Lean build concurrency without changing build inputs."""

    return {**os.environ, "LEAN_NUM_THREADS": "1"}


def run_owned_lean_process(
    command: list[str], *, cwd: Path, timeout: int,
    env: Mapping[str, str] | None = None,
) -> subprocess.CompletedProcess[bytes]:
    """Run one native command; clean owned descendants on failure or cancellation."""

    process = subprocess.Popen(
        command, cwd=cwd, env=env, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except BaseException as exc:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        except OSError:
            # Cleanup must not hide the original failure. Even when group
            # termination fails, try to terminate and reap the owned parent.
            try:
                process.kill()
            except OSError:
                pass
        try:
            stdout, stderr = process.communicate(timeout=1)
            if isinstance(exc, subprocess.TimeoutExpired):
                exc.output, exc.stderr = stdout, stderr
        except (OSError, subprocess.TimeoutExpired):
            pass
        raise
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


def lean_loaded_module_closure(
    root: Path,
    entry_module: str,
    timeout_seconds: int = DEFAULT_LEAN_GRAPH_TIMEOUT_SECONDS,
    *,
    build_entry_module: bool = True,
) -> tuple[tuple[str, ...] | None, str]:
    """Ask Lean for the exact modules loaded by one entry module.

    By default this first builds the forced entry-module target, so callers can
    use the result as part of a build-backed closure identity.  Advisory
    callers that only need Lean's already-available loaded-module graph may
    pass ``build_entry_module=False``.  That graph-only mode deliberately does
    not certify that the entry module's source currently builds; it imports
    against the artifacts already available in the Lake environment.
    """

    if not MODULE_RE.fullmatch(entry_module):
        return None, "entry module name is invalid"
    helper_path = root / LEAN_IMPORT_GRAPH_HELPER
    try:
        helper = helper_path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        return None, f"Lean import-graph helper is unavailable: {exc}"
    if build_entry_module:
        try:
            build = run_owned_lean_process(
                ["lake", "build", f"+{entry_module}:olean"],
                cwd=root,
                env=single_threaded_lean_build_environment(),
                timeout=timeout_seconds,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            return None, f"Lake could not build the entry module: {exc}"
        if build.returncode != 0:
            error = (
                build.stdout.decode("utf-8", errors="replace")
                + "\n"
                + build.stderr.decode("utf-8", errors="replace")
            ).strip()
            return None, "Lake could not build the entry module: " + error[-4000:]

    script = (
        f"import {entry_module}\n"
        "import Lean\n\n"
        f"{helper.rstrip()}\n\n"
        "#econcslib_import_closure\n"
    )
    with tempfile.TemporaryDirectory() as temporary:
        driver = Path(temporary) / "AppliedModelingLibImportClosure.lean"
        driver.write_text(script, encoding="utf-8")
        try:
            result = run_owned_lean_process(
                ["lake", "env", "lean", str(driver)],
                cwd=root,
                timeout=timeout_seconds,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            return None, f"Lean import-graph command failed: {exc}"
    if result.returncode != 0:
        error = (
            result.stdout.decode("utf-8", errors="replace")
            + "\n"
            + result.stderr.decode("utf-8", errors="replace")
        ).strip()
        return None, "Lean import-graph command failed: " + error[-4000:]
    payloads: list[dict[str, object]] = []
    for line in result.stdout.decode("utf-8", errors="replace").splitlines():
        if not line.startswith(LEAN_IMPORT_GRAPH_MARKER):
            continue
        try:
            payload = json.loads(line[len(LEAN_IMPORT_GRAPH_MARKER) :])
        except json.JSONDecodeError:
            return None, "Lean import-graph command emitted malformed JSON"
        if isinstance(payload, dict):
            payloads.append(payload)
    if len(payloads) != 1:
        return None, "Lean import-graph command did not emit exactly one payload"
    payload = payloads[0]
    raw_modules = payload.get("modules")
    if payload.get("schema") != LEAN_IMPORT_GRAPH_SCHEMA or not isinstance(
        raw_modules, list
    ):
        return None, "Lean import-graph payload schema is invalid"
    modules = tuple(str(value).strip() for value in raw_modules)
    if (
        not modules
        or any(not MODULE_RE.fullmatch(module) for module in modules)
        or len(modules) != len(set(modules))
    ):
        return None, "Lean import-graph payload has invalid or duplicate modules"
    return tuple(sorted(modules)), ""


def external_module_artifact_search_roots(
    root: Path,
    *,
    timeout_seconds: int = 60,
) -> tuple[list[tuple[str, Path]] | None, str]:
    """Reconstruct path-labeled artifact roots without launching ``lake env``.

    The labels are stable Lake/toolchain roles, not filesystem locations. They
    may be retained in operational stat caches without making those caches
    checkout- or machine-path dependent.
    """

    manifest_path = root / "lake-manifest.json"
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        return None, f"Lake manifest cannot reconstruct artifact roots: {exc}"
    packages = manifest.get("packages") if isinstance(manifest, Mapping) else None
    if not isinstance(packages, list):
        return None, "Lake manifest has no package inventory"
    package_locations: list[tuple[str, tuple[str, ...]]] = []
    for package in packages:
        if not isinstance(package, Mapping):
            continue
        name = str(package.get("name") or "").strip()
        raw_subdir = package.get("subDir")
        subdir = str(raw_subdir or "").strip()
        if subdir:
            subdir_path = PurePosixPath(subdir)
            subdir_parts = subdir_path.parts
            if (
                subdir_path.is_absolute()
                or not subdir_parts
                or any(part in {"", ".", ".."} for part in subdir_parts)
            ):
                return None, "Lake manifest package subdirectory is malformed"
        else:
            subdir_parts = ()
        package_locations.append((name, tuple(subdir_parts)))
    package_names = [name for name, _subdir_parts in package_locations]
    if (
        any(
            not name or "/" in name or "\\" in name or name in {".", ".."}
            for name in package_names
        )
        or len(set(package_names)) != len(package_names)
    ):
        return None, "Lake manifest package inventory is malformed"
    try:
        prefix_result = subprocess.run(
            ["lean", "--print-prefix"],
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=timeout_seconds,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return None, f"Lean could not expose its toolchain prefix: {exc}"
    if prefix_result.returncode != 0:
        error = prefix_result.stderr.decode("utf-8", errors="replace").strip()
        return None, "Lean could not expose its toolchain prefix: " + error
    prefix = Path(
        prefix_result.stdout.decode("utf-8", errors="replace").strip()
    ).resolve()
    candidates = [
        (
            f"lake-package:{name}",
            root
            / ".lake"
            / "packages"
            / name
            / Path(*subdir_parts)
            / ".lake"
            / "build"
            / "lib"
            / "lean",
        )
        for name, subdir_parts in package_locations
    ]
    candidates.extend(
        (
            ("repository-build", root / ".lake" / "build" / "lib" / "lean"),
            ("toolchain", prefix / "lib" / "lean"),
        )
    )
    search_paths: list[tuple[str, Path]] = []
    seen: set[Path] = set()
    for role, candidate in candidates:
        resolved = candidate.resolve()
        if resolved.is_dir() and resolved not in seen:
            search_paths.append((role, resolved))
            seen.add(resolved)
    if not search_paths:
        return None, "Lake exposed an empty Lean artifact search path"
    return search_paths, ""


def external_artifact_search_snapshot(
    root: Path,
    *,
    timeout_seconds: int = 60,
) -> tuple[ExternalArtifactSearchSnapshot | None, str]:
    """Inventory top-level artifact namespaces once for one transaction pass."""

    search_roots, error = external_module_artifact_search_roots(
        root, timeout_seconds=timeout_seconds
    )
    if search_roots is None:
        return None, error
    records: list[tuple[str, Path, frozenset[str], frozenset[str]]] = []
    for role, search_root in search_roots:
        try:
            entries = tuple(search_root.iterdir())
        except OSError as exc:
            return None, f"Lean artifact root cannot be inventoried: {role}: {exc}"
        direct_modules = frozenset(
            path.stem
            for path in entries
            if path.suffix == ".olean"
            and path.is_file()
            and MODULE_RE.fullmatch(path.stem)
        )
        prefixes = frozenset(
            path.name
            for path in entries
            if path.is_dir() and MODULE_RE.fullmatch(path.name)
        )
        records.append((role, search_root, direct_modules, prefixes))
    return ExternalArtifactSearchSnapshot(tuple(records)), ""


def external_module_artifact_snapshot(
    root: Path,
    modules: Iterable[str],
    *,
    timeout_seconds: int = 60,
) -> tuple[ExternalModuleArtifactSnapshot | None, str]:
    """Hash external ``.olean`` bytes once and retain a mutation guard.

    The exact package set comes from the pinned Lake manifest and the Lean core
    root comes from the cwd-selected toolchain.  We deliberately do not launch
    ``lake env`` merely to print ``LEAN_PATH``: Lake can consume close to a GiB
    before one byte is hashed.  Paths are navigation only.  A module must have
    one artifact byte identity across every reconstructed candidate root; a
    conflicting duplicate fails closed instead of relying on search order.
    """

    requested = tuple(sorted(str(module).strip() for module in modules))
    if not requested:
        return ExternalModuleArtifactSnapshot((), ()), ""
    search_snapshot, root_error = external_artifact_search_snapshot(
        root,
        timeout_seconds=timeout_seconds,
    )
    if search_snapshot is None:
        return None, root_error

    module_records: list[tuple[str, int, str]] = []
    file_states: list[ExternalArtifactFileState] = []
    for module in requested:
        if not MODULE_RE.fullmatch(module):
            return None, f"loaded external module has invalid identity: {module}"
        artifact_candidates = tuple(
            path for _role, path in search_snapshot.candidates(module)
        )
        if not artifact_candidates:
            return (
                None,
                f"loaded external module has no resolvable .olean artifact: {module}",
            )
        artifact_identities: set[tuple[int, str]] = set()
        for artifact in artifact_candidates:
            try:
                digest = hashlib.sha256()
                with artifact.open("rb") as stream:
                    before = os.fstat(stream.fileno())
                    for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                        digest.update(chunk)
                    after = os.fstat(stream.fileno())
                if (
                    before.st_size != after.st_size
                    or before.st_mtime_ns != after.st_mtime_ns
                    or before.st_ctime_ns != after.st_ctime_ns
                    or before.st_ino != after.st_ino
                    or before.st_dev != after.st_dev
                ):
                    return (
                        None,
                        f"loaded external module artifact changed while hashed: {module}",
                    )
            except OSError as exc:
                return (
                    None,
                    f"loaded external module artifact cannot be read: {module}: {exc}",
                )
            artifact_identities.add((after.st_size, digest.hexdigest()))
            file_states.append(
                ExternalArtifactFileState.from_stat(module, artifact, after)
            )
        if len(artifact_identities) != 1:
            return (
                None,
                f"loaded external module has conflicting .olean artifacts: {module}",
            )
        byte_length, artifact_sha256 = next(iter(artifact_identities))
        module_records.append((module, byte_length, artifact_sha256))
    snapshot = ExternalModuleArtifactSnapshot(
        tuple(module_records),
        tuple(file_states),
    )
    mutation_problem = snapshot.current_problem()
    if mutation_problem:
        return None, mutation_problem
    return snapshot, ""


def external_module_artifact_records(
    root: Path,
    modules: Iterable[str],
    *,
    timeout_seconds: int = 60,
) -> tuple[list[dict[str, object]] | None, str]:
    """Return portable exact-byte records for loaded external modules."""

    snapshot, problem = external_module_artifact_snapshot(
        root,
        modules,
        timeout_seconds=timeout_seconds,
    )
    return (snapshot.records() if snapshot is not None else None), problem


def external_module_artifacts_sha256(records: Iterable[Mapping[str, object]]) -> str:
    """Compactly bind the canonical module/content identities resolved above."""

    canonical = sorted(
        (dict(record) for record in records), key=lambda item: str(item["module"])
    )
    return _stable_sha256({"external_module_artifacts": canonical})


class WorktreeImportClosureProvider:
    """Memoized identity provider for Lean-emitted loaded-module closures.

    Construction snapshots Git status and module ownership. The default policy
    requires tracked, staged repository sources for release-style identities.
    A caller auditing the current proof worktree may explicitly allow uniquely
    owned dirty sources; those receipts bind the exact current bytes and retain
    the same mutation finalization. Live receipt issuance can eagerly snapshot
    tracked Lean bytes before invoking Lean. The ordinary saved-receipt path may
    opt into lazy source reads, in which case it reads and memoizes only the
    Lean-owned paths in validated saved closures. A caller sharing one provider
    across several receipts must call
    :meth:`finalization_problems` before crediting the results. That final check
    rereads every input that authorized a successful identity; memoization is
    never itself authority after the worktree changes.
    """

    def __init__(
        self,
        root: Path | str,
        *,
        module_graph_loader: LeanModuleGraphLoader = lean_loaded_module_closure,
        graph_timeout_seconds: int = DEFAULT_LEAN_GRAPH_TIMEOUT_SECONDS,
        eager_source_snapshot: bool = True,
        allow_dirty_worktree_sources: bool = False,
    ) -> None:
        self.root = Path(root).resolve()
        self._module_graph_loader = module_graph_loader
        self._graph_timeout_seconds = graph_timeout_seconds
        self._allow_dirty_worktree_sources = allow_dirty_worktree_sources
        self._inventory_problem: ImportClosureIdentityProblem | None = None
        try:
            self._tracked_paths = frozenset(index_paths(self.root))
            self._unstaged_paths = frozenset(unstaged_paths(self.root))
            self._untracked_paths = frozenset(untracked_paths(self.root))
        except (OSError, RuntimeError) as exc:
            # A provider may be constructed by a diagnostic or scaffold over a
            # synthetic tree.  Such a tree has no authoritative candidate
            # inventory: retain that as a fail-closed result instead of either
            # crashing the caller or inferring module ownership from files.
            self._tracked_paths = frozenset()
            self._unstaged_paths = frozenset()
            self._untracked_paths = frozenset()
            self._inventory_problem = ImportClosureIdentityProblem(
                code="git_inventory_unavailable",
                entrypoint="",
                importer="",
                reason=f"Git candidate path inventory cannot be read: {exc}",
            )
        tracked_lean_paths = sorted(
            path for path in self._tracked_paths if path.endswith(".lean")
        )
        self._sources: dict[str, bytes | None] = {}
        self._source_read_errors: dict[str, str] = {}
        if eager_source_snapshot:
            for relative in tracked_lean_paths:
                self._snapshot_source(relative)

        self._modules, self._ambiguous_modules = module_map(tracked_lean_paths)
        untracked_lean = sorted(
            path for path in self._untracked_paths if path.endswith(".lean")
        )
        self._untracked_modules, self._ambiguous_untracked_modules = module_map(
            untracked_lean
        )
        self._repository_prefixes = frozenset(
            module.split(".", 1)[0]
            for module in (
                *self._modules,
                *self._ambiguous_modules,
                *self._untracked_modules,
                *self._ambiguous_untracked_modules,
            )
        )
        self._control_records: tuple[dict[str, object], ...] = tuple(
            self._snapshot_control(relative)
            for relative in WORKTREE_IDENTITY_CONTROL_PATHS
        )
        self._control_problem: ImportClosureIdentityProblem | None = None
        for record in self._control_records:
            relative = str(record["path"])
            read_error = record.get("read_error")
            if isinstance(read_error, str):
                self._control_problem = ImportClosureIdentityProblem(
                    code="control_file_unreadable",
                    entrypoint="",
                    importer=str(record["path"]),
                    dependency_path=str(record["path"]),
                    reason=f"build-control file cannot be read: {read_error}",
                )
                break
            if (
                record.get("tracked_in_index") is not True
                or record.get("untracked") is True
            ):
                self._control_problem = ImportClosureIdentityProblem(
                    code="control_file_untracked",
                    entrypoint="",
                    importer=relative,
                    dependency_path=relative,
                    reason="build-control file is not tracked in the candidate index",
                )
                break
            if record.get("path_kind") != "file":
                self._control_problem = ImportClosureIdentityProblem(
                    code="control_file_unavailable",
                    entrypoint="",
                    importer=relative,
                    dependency_path=relative,
                    reason="required build-control path is not a readable regular file",
                )
                break
            if (
                relative in self._unstaged_paths
                and not self._allow_dirty_worktree_sources
            ):
                self._control_problem = ImportClosureIdentityProblem(
                    code="control_file_unstaged",
                    entrypoint="",
                    importer=relative,
                    dependency_path=relative,
                    reason="build-control file has unstaged changes",
                )
                break
        self._record_cache: dict[
            str, tuple[dict[str, object] | None, ImportClosureIdentityProblem | None]
        ] = {}
        self._external_artifact_snapshots: dict[
            tuple[str, ...], tuple[list[dict[str, object]] | None, str]
        ] = {}
        self._validated_entrypoints: set[str] = set()
        self._watched_sources: dict[tuple[str, int, str], tuple[str, str]] = {}
        self._watched_lake_routing: dict[tuple[str, str, str], str] = {}
        self._watched_external_artifacts: dict[
            tuple[tuple[str, ...], tuple[tuple[str, int, str], ...]], str
        ] = {}

    def _snapshot_source(self, relative: str) -> bytes | None:
        if relative in self._sources:
            return self._sources[relative]
        try:
            source = (self.root / relative).read_bytes()
        except OSError as exc:
            source = None
            self._source_read_errors[relative] = str(exc)
        self._sources[relative] = source
        return source

    def _external_artifacts(
        self, modules: Iterable[str], *, refresh: bool = False
    ) -> tuple[list[dict[str, object]] | None, str]:
        """Snapshot one exact external artifact set once per provider/sync."""

        key = tuple(sorted(str(module) for module in modules))
        if not refresh and key in self._external_artifact_snapshots:
            return self._external_artifact_snapshots[key]
        result = external_module_artifact_records(
            self.root,
            key,
            timeout_seconds=min(self._graph_timeout_seconds, 60),
        )
        self._external_artifact_snapshots[key] = result
        return result

    def _snapshot_control(
        self,
        relative: str,
        *,
        tracked_paths: frozenset[str] | None = None,
        untracked_paths: frozenset[str] | None = None,
    ) -> dict[str, object]:
        path = self.root / relative
        current_tracked = (
            self._tracked_paths if tracked_paths is None else tracked_paths
        )
        current_untracked = (
            self._untracked_paths if untracked_paths is None else untracked_paths
        )
        record: dict[str, object] = {
            "path": relative,
            "tracked_in_index": relative in current_tracked,
            "untracked": relative in current_untracked,
        }
        try:
            if path.is_file():
                content = path.read_bytes()
                record.update(
                    {
                        "path_kind": "file",
                        "byte_length": len(content),
                        "sha256": hashlib.sha256(content).hexdigest(),
                    }
                )
            elif path.exists():
                record["path_kind"] = "non_file"
            else:
                record["path_kind"] = "absent"
        except OSError as exc:
            record.update({"path_kind": "unreadable", "read_error": str(exc)})
        return record

    @staticmethod
    def _canonical_external_artifacts(
        records: Iterable[Mapping[str, object]],
    ) -> tuple[tuple[str, int, str], ...]:
        return tuple(
            sorted(
                (
                    str(record["module"]),
                    int(record["byte_length"]),
                    str(record["sha256"]),
                )
                for record in records
            )
        )

    def _watch_successful_identity(
        self,
        *,
        entrypoint: str,
        payload: Mapping[str, object],
        external_artifacts: Iterable[Mapping[str, object]],
    ) -> None:
        """Bind finalization to only the inputs that authorized one identity."""

        entry_module = str(payload["entry_module"])
        lake_routing = payload["lake_routing"]
        assert isinstance(lake_routing, Mapping)
        routing_path = (
            "lakefile.lean" if lake_routing.get("kind") == "lean" else "lakefile.toml"
        )
        self._validated_entrypoints.add(entrypoint)
        self._watched_lake_routing[
            (
                entrypoint,
                entry_module,
                _stable_sha256(durable_lake_routing_projection(lake_routing)),
            )
        ] = routing_path
        raw_sources = payload["sources"]
        assert isinstance(raw_sources, list)
        for raw in raw_sources:
            assert isinstance(raw, Mapping)
            self._watched_sources.setdefault(
                (
                    str(raw["path"]),
                    int(raw["byte_length"]),
                    str(raw["sha256"]),
                ),
                (entrypoint, str(raw["module"])),
            )
        raw_external_modules = payload["external_import_modules"]
        assert isinstance(raw_external_modules, list)
        modules = tuple(sorted(str(module) for module in raw_external_modules))
        expected_artifacts = self._canonical_external_artifacts(external_artifacts)
        self._watched_external_artifacts.setdefault(
            (modules, expected_artifacts),
            entrypoint,
        )

    def finalization_problems(self) -> tuple[ImportClosureIdentityProblem, ...]:
        """Revalidate every input used by successful identities in this provider.

        Saved-closure reuse intentionally snapshots exact source and artifact
        bytes once. This method is the transaction boundary that makes sharing
        those snapshots safe: callers run it after their last reuse and discard
        every result if any problem is returned. It performs fresh filesystem,
        Git, Lake-routing, and external-artifact reads and does not populate an
        authorization cache.
        """

        if not self._validated_entrypoints:
            return ()
        entrypoint = sorted(self._validated_entrypoints)[0]
        problems: list[ImportClosureIdentityProblem] = []

        try:
            current_tracked_paths = frozenset(index_paths(self.root))
            current_untracked_paths = frozenset(untracked_paths(self.root))
            current_unstaged_paths = frozenset(unstaged_paths(self.root))
        except Exception as exc:
            problems.append(
                ImportClosureIdentityProblem(
                    code="closure_finalization_inventory_unavailable",
                    entrypoint=entrypoint,
                    importer=entrypoint,
                    reason=f"current Git path inventory cannot be read: {exc}",
                )
            )
            return tuple(problems)

        current_repository_candidates = repository_module_candidate_map(
            current_tracked_paths, current_untracked_paths
        )

        current_controls = tuple(
            self._snapshot_control(
                relative,
                tracked_paths=current_tracked_paths,
                untracked_paths=current_untracked_paths,
            )
            for relative in WORKTREE_IDENTITY_CONTROL_PATHS
        )
        controls_have_forbidden_unstaged_changes = (
            not self._allow_dirty_worktree_sources
            and any(
                relative in current_unstaged_paths
                for relative in WORKTREE_IDENTITY_CONTROL_PATHS
            )
        )
        if (
            current_controls != self._control_records
            or controls_have_forbidden_unstaged_changes
        ):
            problems.append(
                ImportClosureIdentityProblem(
                    code="closure_finalization_controls_changed",
                    entrypoint=entrypoint,
                    importer=entrypoint,
                    reason="build-control identity changed after closure validation",
                )
            )

        for (
            watched_entrypoint,
            entry_module,
            expected_sha256,
        ), routing_path in sorted(self._watched_lake_routing.items()):
            routing, error = lake_routing_projection(self.root, entry_module)
            routing_association_changed = (
                routing_path not in current_tracked_paths
                or routing_path in current_untracked_paths
                or (
                    not self._allow_dirty_worktree_sources
                    and routing_path in current_unstaged_paths
                )
            )
            if (
                routing_association_changed
                or routing is None
                or _stable_sha256(durable_lake_routing_projection(routing))
                != expected_sha256
            ):
                problems.append(
                    ImportClosureIdentityProblem(
                        code="closure_finalization_lake_routing_changed",
                        entrypoint=watched_entrypoint,
                        importer=routing_path,
                        imported_module=entry_module,
                        dependency_path=routing_path,
                        reason=error
                        or "entrypoint-relevant Lake routing changed after closure validation",
                    )
                )

        current_sources: dict[str, tuple[bytes | None, str]] = {}
        for (
            path,
            expected_length,
            expected_sha256,
        ), (watched_entrypoint, module) in sorted(self._watched_sources.items()):
            candidates = current_repository_candidates.get(module, ())
            if candidates != (path,):
                problems.append(
                    ImportClosureIdentityProblem(
                        code="closure_finalization_source_association_changed",
                        entrypoint=watched_entrypoint,
                        importer=watched_entrypoint,
                        imported_module=module,
                        dependency_path=", ".join(candidates),
                        reason=(
                            "Lean-loaded module no longer has the same unique "
                            "repository source"
                        ),
                    )
                )
            elif (
                not self._allow_dirty_worktree_sources
                and path in current_unstaged_paths
            ):
                problems.append(
                    ImportClosureIdentityProblem(
                        code="closure_finalization_source_git_state_changed",
                        entrypoint=watched_entrypoint,
                        importer=watched_entrypoint,
                        imported_module=module,
                        dependency_path=path,
                        reason=(
                            "Lean-loaded source acquired unstaged changes after "
                            "closure validation"
                        ),
                    )
                )
            if path not in current_sources:
                try:
                    current_sources[path] = ((self.root / path).read_bytes(), "")
                except OSError as exc:
                    current_sources[path] = (None, str(exc))
            content, detail = current_sources[path]
            if content is None or (
                len(content) != expected_length
                or hashlib.sha256(content).hexdigest() != expected_sha256
            ):
                problems.append(
                    ImportClosureIdentityProblem(
                        code="closure_finalization_source_changed",
                        entrypoint=watched_entrypoint,
                        importer=watched_entrypoint,
                        imported_module=module,
                        dependency_path=path,
                        reason=detail
                        or "Lean-loaded source bytes changed after closure validation",
                    )
                )

        external_modules = tuple(
            sorted(
                {
                    module
                    for modules, _expected in self._watched_external_artifacts
                    for module in modules
                }
            )
        )
        external_entrypoints: dict[str, str] = {}
        for (modules, _expected), watched_entrypoint in sorted(
            self._watched_external_artifacts.items()
        ):
            for module in modules:
                external_entrypoints.setdefault(module, watched_entrypoint)
        for module, watched_entrypoint in sorted(external_entrypoints.items()):
            candidates = current_repository_candidates.get(module, ())
            if candidates:
                problems.append(
                    ImportClosureIdentityProblem(
                        code="closure_finalization_external_association_changed",
                        entrypoint=watched_entrypoint,
                        importer=watched_entrypoint,
                        imported_module=module,
                        dependency_path=", ".join(candidates),
                        reason=(
                            "Lean-loaded external module now has a repository "
                            "source candidate"
                        ),
                    )
                )
        current_external, external_error = self._external_artifacts(
            external_modules, refresh=True
        )
        current_external_by_module = (
            {
                str(record["module"]): (
                    str(record["module"]),
                    int(record["byte_length"]),
                    str(record["sha256"]),
                )
                for record in current_external
            }
            if current_external is not None
            else {}
        )
        for (modules, expected), watched_entrypoint in sorted(
            self._watched_external_artifacts.items()
        ):
            current = tuple(
                current_external_by_module[module]
                for module in modules
                if module in current_external_by_module
            )
            if current_external is None or current != expected:
                problems.append(
                    ImportClosureIdentityProblem(
                        code="closure_finalization_external_artifacts_changed",
                        entrypoint=watched_entrypoint,
                        importer=watched_entrypoint,
                        reason=external_error
                        or "loaded external module artifacts changed after closure validation",
                    )
                )

        return tuple(problems)

    @staticmethod
    def _normalized_entrypoint(entrypoint: str) -> str | None:
        pure = PurePosixPath(entrypoint)
        if pure.is_absolute() or ".." in pure.parts or not pure.parts:
            return None
        normalized = pure.as_posix()
        if normalized in {"", "."} or not normalized.endswith(".lean"):
            return None
        return normalized

    def _problem(
        self,
        *,
        code: str,
        entrypoint: str,
        importer: str,
        imported_module: str = "",
        dependency_path: str = "",
        reason: str,
    ) -> tuple[None, ImportClosureIdentityProblem]:
        return None, ImportClosureIdentityProblem(
            code=code,
            entrypoint=entrypoint,
            importer=importer,
            imported_module=imported_module,
            dependency_path=dependency_path,
            reason=reason,
        )

    def identity_for_entrypoint(
        self, entrypoint: str
    ) -> tuple[str | None, ImportClosureIdentityProblem | None]:
        """Return the exact closure digest, or one structured fail-closed problem."""

        record, problem = self.record_for_entrypoint(entrypoint)
        if record is None:
            return None, problem
        return lean_import_closure_payload_sha256(record), None

    def record_for_entrypoint(
        self, entrypoint: str
    ) -> tuple[dict[str, object] | None, ImportClosureIdentityProblem | None]:
        """Run Lean once and return its exact loaded-module closure record."""

        normalized = self._normalized_entrypoint(entrypoint)
        if normalized is None:
            return self._problem(
                code="invalid_entrypoint",
                entrypoint=entrypoint,
                importer=entrypoint,
                reason="entrypoint must be a repository-relative .lean path",
            )
        cached = self._record_cache.get(normalized)
        if cached is not None:
            return cached
        result = self._record_for_entrypoint_uncached(normalized)
        self._record_cache[normalized] = result
        return result

    def _record_for_entrypoint_uncached(
        self, entrypoint: str
    ) -> tuple[dict[str, object] | None, ImportClosureIdentityProblem | None]:
        if self._inventory_problem is not None:
            problem = self._inventory_problem
            return None, ImportClosureIdentityProblem(
                code=problem.code,
                entrypoint=entrypoint,
                importer=entrypoint,
                reason=problem.reason,
            )
        if entrypoint not in self._tracked_paths and not (
            self._allow_dirty_worktree_sources and entrypoint in self._untracked_paths
        ):
            return self._problem(
                code="entrypoint_not_tracked",
                entrypoint=entrypoint,
                importer=entrypoint,
                dependency_path=entrypoint,
                reason="entrypoint is not tracked in the Git index",
            )
        if (
            entrypoint in self._unstaged_paths
            and not self._allow_dirty_worktree_sources
        ):
            return self._problem(
                code="unstaged_entrypoint",
                entrypoint=entrypoint,
                importer=entrypoint,
                dependency_path=entrypoint,
                reason="entrypoint has unstaged changes",
            )
        if self._control_problem is not None:
            problem = self._control_problem
            return None, ImportClosureIdentityProblem(
                code=problem.code,
                entrypoint=entrypoint,
                importer=problem.importer,
                dependency_path=problem.dependency_path,
                reason=problem.reason,
            )

        entry_module = module_name_for_path(entrypoint)
        if entry_module is None:
            return self._problem(
                code="entrypoint_has_no_module_identity",
                entrypoint=entrypoint,
                importer=entrypoint,
                dependency_path=entrypoint,
                reason="entrypoint path has no valid Lake module identity",
            )
        lake_routing, routing_error = lake_routing_projection(self.root, entry_module)
        if lake_routing is None:
            return self._problem(
                code="lake_routing_unavailable",
                entrypoint=entrypoint,
                importer=entrypoint,
                imported_module=entry_module,
                reason=routing_error,
            )
        routing_path = (
            "lakefile.lean" if lake_routing.get("kind") == "lean" else "lakefile.toml"
        )
        if (
            routing_path not in self._tracked_paths
            or routing_path in self._untracked_paths
        ):
            return self._problem(
                code="lake_routing_untracked",
                entrypoint=entrypoint,
                importer=routing_path,
                dependency_path=routing_path,
                reason="effective Lake routing file is not tracked in the candidate index",
            )
        if (
            routing_path in self._unstaged_paths
            and not self._allow_dirty_worktree_sources
        ):
            return self._problem(
                code="lake_routing_unstaged",
                entrypoint=entrypoint,
                importer=routing_path,
                dependency_path=routing_path,
                reason="effective Lake routing file has unstaged changes",
            )
        modules, graph_error = self._module_graph_loader(
            self.root,
            entry_module,
            self._graph_timeout_seconds,
        )
        if modules is None:
            return self._problem(
                code="lean_module_graph_unavailable",
                entrypoint=entrypoint,
                importer=entrypoint,
                imported_module=entry_module,
                reason=graph_error or "Lean emitted no loaded-module closure",
            )
        if entry_module not in modules:
            return self._problem(
                code="lean_module_graph_missing_entrypoint",
                entrypoint=entrypoint,
                importer=entrypoint,
                imported_module=entry_module,
                reason="Lean's loaded-module closure omits the requested entry module",
            )

        source_records: list[dict[str, object]] = []
        external_modules: list[str] = []
        for module in modules:
            tracked_collisions = self._ambiguous_modules.get(module, ())
            untracked_path = self._untracked_modules.get(module)
            untracked_collisions = self._ambiguous_untracked_modules.get(module, ())
            if tracked_collisions:
                return self._problem(
                    code="ambiguous_repository_import",
                    entrypoint=entrypoint,
                    importer=entrypoint,
                    imported_module=module,
                    dependency_path=", ".join(tracked_collisions),
                    reason="Lean-loaded module resolves to multiple tracked sources",
                )
            dependency = self._modules.get(module)
            loose_paths = tuple(
                path
                for path in (
                    (untracked_path,) if untracked_path else untracked_collisions
                )
                if path
            )
            if dependency is not None and loose_paths:
                return self._problem(
                    code="ambiguous_repository_import",
                    entrypoint=entrypoint,
                    importer=entrypoint,
                    imported_module=module,
                    dependency_path=", ".join((dependency, *loose_paths)),
                    reason="Lean-loaded module also resolves to untracked source",
                )
            if dependency is None:
                if loose_paths:
                    if self._allow_dirty_worktree_sources and len(loose_paths) == 1:
                        dependency = loose_paths[0]
                    else:
                        return self._problem(
                            code="untracked_repository_import",
                            entrypoint=entrypoint,
                            importer=entrypoint,
                            imported_module=module,
                            dependency_path=", ".join(loose_paths),
                            reason=(
                                "Lean loaded a module that exists only as "
                                "untracked source"
                            ),
                        )
                if (
                    dependency is None
                    and module.split(".", 1)[0] in self._repository_prefixes
                ):
                    return self._problem(
                        code="unresolved_repository_import",
                        entrypoint=entrypoint,
                        importer=entrypoint,
                        imported_module=module,
                        reason="Lean-loaded repository module has no unique source",
                    )
                if dependency is None:
                    external_modules.append(module)
                    continue
            if (
                dependency in self._unstaged_paths
                and not self._allow_dirty_worktree_sources
            ):
                return self._problem(
                    code="unstaged_imported_module",
                    entrypoint=entrypoint,
                    importer=entrypoint,
                    imported_module=module,
                    dependency_path=dependency,
                    reason="Lean-loaded repository module has unstaged changes",
                )
            source = self._snapshot_source(dependency)
            if source is None:
                detail = self._source_read_errors.get(
                    dependency, "file is absent from the worktree"
                )
                return self._problem(
                    code="source_unreadable",
                    entrypoint=entrypoint,
                    importer=entrypoint,
                    imported_module=module,
                    dependency_path=dependency,
                    reason=f"repository Lean source cannot be read: {detail}",
                )
            source_records.append(
                {
                    "module": module,
                    "path": dependency,
                    "byte_length": len(source),
                    "sha256": hashlib.sha256(source).hexdigest(),
                }
            )

        external_artifacts, artifact_error = self._external_artifacts(external_modules)
        if external_artifacts is None:
            return self._problem(
                code="external_module_artifact_unavailable",
                entrypoint=entrypoint,
                importer=entrypoint,
                reason=artifact_error,
            )

        # Lean/Lake may run for several minutes. Re-snapshot every authority
        # input after graph extraction so a concurrent edit cannot pair the
        # loaded graph with bytes or routing captured before that edit. Compare
        # only modules and controls that authorized this receipt: an unrelated
        # agent creating a scratch module must not discard a long Lean run.
        try:
            current_tracked_paths = frozenset(index_paths(self.root))
            current_untracked_paths = frozenset(untracked_paths(self.root))
            current_unstaged_paths = frozenset(unstaged_paths(self.root))
        except Exception as exc:
            return self._problem(
                code="worktree_changed_during_lean_graph",
                entrypoint=entrypoint,
                importer=entrypoint,
                reason=f"current Git path inventory cannot be read: {exc}",
            )
        current_repository_candidates = repository_module_candidate_map(
            current_tracked_paths, current_untracked_paths
        )
        association_changes: list[str] = []
        for record in source_records:
            module = str(record["module"])
            path = str(record["path"])
            candidates = current_repository_candidates.get(module, ())
            if candidates != (path,):
                association_changes.append(
                    f"{module} source association is {', '.join(candidates) or '<none>'}"
                )
            elif (
                not self._allow_dirty_worktree_sources
                and path in current_unstaged_paths
            ):
                association_changes.append(f"{module} acquired unstaged changes")
        for module in external_modules:
            candidates = current_repository_candidates.get(module, ())
            if candidates:
                association_changes.append(
                    f"external {module} acquired repository source "
                    + ", ".join(candidates)
                )
        current_controls = tuple(
            self._snapshot_control(
                relative,
                tracked_paths=current_tracked_paths,
                untracked_paths=current_untracked_paths,
            )
            for relative in WORKTREE_IDENTITY_CONTROL_PATHS
        )
        controls_changed = current_controls != self._control_records or (
            not self._allow_dirty_worktree_sources
            and any(
                relative in current_unstaged_paths
                for relative in WORKTREE_IDENTITY_CONTROL_PATHS
            )
        )
        if association_changes or controls_changed:
            details = list(association_changes)
            if controls_changed:
                details.append("build-control identity changed")
            return self._problem(
                code="worktree_changed_during_lean_graph",
                entrypoint=entrypoint,
                importer=entrypoint,
                reason="; ".join(details),
            )
        current_routing, current_routing_error = lake_routing_projection(
            self.root, entry_module
        )
        routing_association_changed = (
            routing_path not in current_tracked_paths
            or routing_path in current_untracked_paths
            or (
                not self._allow_dirty_worktree_sources
                and routing_path in current_unstaged_paths
            )
        )
        if (
            routing_association_changed
            or current_routing is None
            or durable_lake_routing_projection(current_routing)
            != durable_lake_routing_projection(lake_routing)
        ):
            return self._problem(
                code="worktree_changed_during_lean_graph",
                entrypoint=entrypoint,
                importer=routing_path,
                dependency_path=routing_path,
                reason=current_routing_error
                or "entrypoint-relevant Lake routing changed during Lean graph extraction",
            )
        for record in source_records:
            path = str(record["path"])
            try:
                current_source = (self.root / path).read_bytes()
            except OSError:
                current_source = None
            if current_source is None or (
                len(current_source) != record["byte_length"]
                or hashlib.sha256(current_source).hexdigest() != record["sha256"]
            ):
                return self._problem(
                    code="worktree_changed_during_lean_graph",
                    entrypoint=entrypoint,
                    importer=entrypoint,
                    imported_module=str(record["module"]),
                    dependency_path=path,
                    reason="Lean-loaded source bytes changed during graph extraction",
                )
        final_external_artifacts, final_artifact_error = self._external_artifacts(
            external_modules,
            refresh=True,
        )
        if final_external_artifacts != external_artifacts:
            return self._problem(
                code="worktree_changed_during_lean_graph",
                entrypoint=entrypoint,
                importer=entrypoint,
                reason=final_artifact_error
                or "loaded external module artifacts changed during graph extraction",
            )

        payload = {
            "schema": WORKTREE_IDENTITY_SCHEMA,
            "entrypoint": entrypoint,
            "entry_module": entry_module,
            "lean_loaded_modules": list(modules),
            "sources": sorted(source_records, key=lambda item: str(item["path"])),
            "external_import_modules": external_modules,
            "external_module_artifacts_sha256": external_module_artifacts_sha256(
                external_artifacts
            ),
            "build_controls": list(self._control_records),
            "lake_routing": lake_routing,
        }
        validated = validated_lean_import_closure_payload(payload)
        self._watch_successful_identity(
            entrypoint=entrypoint,
            payload=validated,
            external_artifacts=external_artifacts,
        )
        return validated, None

    def identity_from_saved_closure(
        self,
        entrypoint: str,
        saved_closure: object,
    ) -> tuple[str | None, ImportClosureIdentityProblem | None]:
        """Rehash a prior Lean-owned closure without rerunning Lean.

        This path is valid only while every saved source association, exact
        source byte sequence, and build control remains unchanged. Since every
        importer is itself in the saved set, any import edit invalidates reuse
        and requires a new Lean-authored receipt.
        """

        normalized = self._normalized_entrypoint(entrypoint)
        if normalized is None:
            return self._problem(
                code="invalid_entrypoint",
                entrypoint=entrypoint,
                importer=entrypoint,
                reason="entrypoint must be a repository-relative .lean path",
            )
        try:
            baseline = validated_lean_import_closure_payload(saved_closure)
        except ValueError as exc:
            return self._problem(
                code="saved_lean_closure_invalid",
                entrypoint=normalized,
                importer=normalized,
                reason=str(exc),
            )
        if baseline["entrypoint"] != normalized:
            return self._problem(
                code="saved_lean_closure_entrypoint_changed",
                entrypoint=normalized,
                importer=normalized,
                reason="saved Lean closure belongs to a different entrypoint",
            )
        if normalized not in self._tracked_paths and not (
            self._allow_dirty_worktree_sources and normalized in self._untracked_paths
        ):
            return self._problem(
                code="entrypoint_not_tracked",
                entrypoint=normalized,
                importer=normalized,
                dependency_path=normalized,
                reason="entrypoint is not tracked in the Git index",
            )
        if (
            normalized in self._unstaged_paths
            and not self._allow_dirty_worktree_sources
        ):
            return self._problem(
                code="unstaged_entrypoint",
                entrypoint=normalized,
                importer=normalized,
                dependency_path=normalized,
                reason="entrypoint has unstaged changes",
            )
        if self._control_problem is not None:
            problem = self._control_problem
            return None, ImportClosureIdentityProblem(
                code=problem.code,
                entrypoint=normalized,
                importer=problem.importer,
                dependency_path=problem.dependency_path,
                reason=problem.reason,
            )
        if list(self._control_records) != durable_lean_build_control_records(
            baseline["build_controls"]
        ):
            return self._problem(
                code="saved_lean_closure_controls_changed",
                entrypoint=normalized,
                importer=normalized,
                reason="build-control identity changed since Lean emitted the closure",
            )
        entry_module = str(baseline["entry_module"])
        lake_routing, routing_error = lake_routing_projection(self.root, entry_module)
        if lake_routing is None:
            return self._problem(
                code="lake_routing_unavailable",
                entrypoint=normalized,
                importer=normalized,
                imported_module=entry_module,
                reason=routing_error,
            )
        routing_path = (
            "lakefile.lean" if lake_routing.get("kind") == "lean" else "lakefile.toml"
        )
        if (
            routing_path not in self._tracked_paths
            or routing_path in self._untracked_paths
        ):
            return self._problem(
                code="lake_routing_untracked",
                entrypoint=normalized,
                importer=routing_path,
                dependency_path=routing_path,
                reason="effective Lake routing file is not tracked in the candidate index",
            )
        if (
            routing_path in self._unstaged_paths
            and not self._allow_dirty_worktree_sources
        ):
            return self._problem(
                code="lake_routing_unstaged",
                entrypoint=normalized,
                importer=routing_path,
                dependency_path=routing_path,
                reason="effective Lake routing file has unstaged changes",
            )
        if durable_lake_routing_projection(
            lake_routing
        ) != durable_lake_routing_projection(baseline["lake_routing"]):
            return self._problem(
                code="saved_lean_closure_routing_changed",
                entrypoint=normalized,
                importer=routing_path,
                dependency_path=routing_path,
                reason="entrypoint-relevant Lake routing semantics changed",
            )

        for raw in baseline["sources"]:
            assert isinstance(raw, dict)
            module = str(raw["module"])
            path = str(raw["path"])
            tracked_collisions = self._ambiguous_modules.get(module, ())
            untracked_path = self._untracked_modules.get(module)
            untracked_collisions = self._ambiguous_untracked_modules.get(module, ())
            loose_paths = tuple(
                candidate
                for candidate in (
                    (untracked_path,) if untracked_path else untracked_collisions
                )
                if candidate
            )
            current_path = self._modules.get(module)
            if (
                current_path is None
                and self._allow_dirty_worktree_sources
                and len(loose_paths) == 1
            ):
                current_path = loose_paths[0]
                loose_paths = ()
            if tracked_collisions or loose_paths or current_path != path:
                associations = tuple(
                    candidate
                    for candidate in (current_path, *tracked_collisions, *loose_paths)
                    if candidate
                )
                return self._problem(
                    code="saved_lean_closure_association_changed",
                    entrypoint=normalized,
                    importer=normalized,
                    imported_module=module,
                    dependency_path=", ".join(associations),
                    reason="saved Lean module no longer has the same unique repository source",
                )
            if path in self._unstaged_paths and not self._allow_dirty_worktree_sources:
                return self._problem(
                    code="unstaged_imported_module",
                    entrypoint=normalized,
                    importer=normalized,
                    imported_module=module,
                    dependency_path=path,
                    reason="Lean-loaded repository module has unstaged changes",
                )
            source = self._snapshot_source(path)
            if source is None:
                return self._problem(
                    code="source_unreadable",
                    entrypoint=normalized,
                    importer=normalized,
                    imported_module=module,
                    dependency_path=path,
                    reason="saved Lean source cannot be read from the current worktree",
                )
            if (
                len(source) != raw["byte_length"]
                or hashlib.sha256(source).hexdigest() != raw["sha256"]
            ):
                return self._problem(
                    code="saved_lean_closure_source_changed",
                    entrypoint=normalized,
                    importer=normalized,
                    imported_module=module,
                    dependency_path=path,
                    reason="saved Lean source bytes changed since closure extraction",
                )

        for raw_module in baseline["external_import_modules"]:
            module = str(raw_module)
            repository_paths = tuple(
                candidate
                for candidate in (
                    self._modules.get(module),
                    *self._ambiguous_modules.get(module, ()),
                    self._untracked_modules.get(module),
                    *self._ambiguous_untracked_modules.get(module, ()),
                )
                if candidate
            )
            if repository_paths:
                return self._problem(
                    code="saved_external_module_association_changed",
                    entrypoint=normalized,
                    importer=normalized,
                    imported_module=module,
                    dependency_path=", ".join(repository_paths),
                    reason="saved external module now resolves to a repository source",
                )
        current_external_artifacts, artifact_error = self._external_artifacts(
            [str(module) for module in baseline["external_import_modules"]]
        )
        if current_external_artifacts is None:
            return self._problem(
                code="saved_external_module_artifact_unavailable",
                entrypoint=normalized,
                importer=normalized,
                reason=artifact_error,
            )
        if (
            external_module_artifacts_sha256(current_external_artifacts)
            != baseline["external_module_artifacts_sha256"]
        ):
            return self._problem(
                code="saved_external_module_artifact_changed",
                entrypoint=normalized,
                importer=normalized,
                reason="saved loaded external module artifact bytes changed",
            )
        self._watch_successful_identity(
            entrypoint=normalized,
            payload=baseline,
            external_artifacts=current_external_artifacts,
        )
        return lean_import_closure_payload_sha256(baseline), None

    def repository_source_bytes_for_closure(self, closure: object) -> dict[str, bytes]:
        """Transfer already authenticated source bytes without rereading files.

        A successful live or saved-closure identity has populated ``_sources``
        for exactly every repository source in its receipt. Downstream audit
        projections can adopt this snapshot, while ``finalization_problems``
        remains responsible for the fresh end-of-transaction recheck.
        """

        validated = validated_lean_import_closure_payload(closure)
        snapshot: dict[str, bytes] = {}
        for raw in validated["sources"]:
            assert isinstance(raw, dict)
            path = str(raw["path"])
            content = self._sources.get(path)
            if content is None:
                raise ValueError(
                    "Lean import-closure source was not authenticated by this provider: "
                    + path
                )
            if (
                len(content) != raw["byte_length"]
                or hashlib.sha256(content).hexdigest() != raw["sha256"]
            ):
                raise ValueError(
                    "provider source snapshot disagrees with Lean import closure: "
                    + path
                )
            snapshot[path] = content
        return snapshot

    def require_identity_for_entrypoint(self, entrypoint: str) -> str:
        """Return an identity or raise ``ImportClosureIdentityError``."""

        digest, problem = self.identity_for_entrypoint(entrypoint)
        if problem is not None:
            raise ImportClosureIdentityError(problem)
        assert digest is not None
        return digest


def dependency_closure_issues(
    repo: Path,
    *,
    candidate: str,
    treeish: str | None = None,
    entrypoints: Iterable[str] | None = None,
    extra_entrypoints: Iterable[str] | None = None,
) -> list[ImportClosureIssue]:
    """Validate repository-local imports in the index or current worktree.

    ``candidate='index'`` reads every traversed source from Git's index and
    rejects both untracked imported modules and unstaged changes to imported
    modules.  ``candidate='worktree'`` additionally starts from modified
    tracked Lean files and catches imports that exist only in untracked files.
    ``extra_entrypoints`` is unioned with the normal roots, which lets a release
    guard traverse every changed committed Lean file without dropping the
    package and PaperInterface roots.
    """

    if candidate not in {"index", "worktree", "tree"}:
        raise ValueError("candidate must be `index`, `worktree`, or `tree`")
    if candidate == "tree" and not treeish:
        raise ValueError("tree candidate requires a treeish")
    repo = repo.resolve()
    indexed = (
        tree_paths(repo, str(treeish)) if candidate == "tree" else index_paths(repo)
    )
    untracked = set() if candidate == "tree" else untracked_lean_paths(repo)
    unstaged = set() if candidate == "tree" else unstaged_paths(repo)
    changed = (
        set()
        if candidate == "tree"
        else staged_paths(repo)
        if candidate == "index"
        else unstaged
    )
    indexed_modules, indexed_ambiguous = module_map(indexed)
    untracked_modules, untracked_ambiguous = module_map(untracked)
    repository_prefixes = {
        module.split(".", 1)[0]
        for module in (
            *indexed_modules,
            *indexed_ambiguous,
            *untracked_modules,
            *untracked_ambiguous,
        )
    }
    roots = (
        set(entrypoints)
        if entrypoints is not None
        else default_entrypoints(indexed, changed)
    )
    roots.update(extra_entrypoints or ())

    def read_text(current_repo: Path, path: str) -> str:
        if candidate == "index":
            return _index_text(current_repo, path)
        if candidate == "worktree":
            return _worktree_text(current_repo, path)
        return _tree_text(current_repo, str(treeish), path)

    issues: list[ImportClosureIssue] = []
    seen_issue: set[tuple[str, str, str, str]] = set()
    candidate_blob_ids = _candidate_blob_ids(repo, candidate=candidate, treeish=treeish)
    blob_texts = _batch_blob_texts(repo, candidate_blob_ids.values())
    source_cache: dict[str, str] = {
        path: blob_texts[blob]
        for path, blob in candidate_blob_ids.items()
        if blob in blob_texts
    }
    import_cache: dict[str, list[str]] = {}

    def cached_source(path: str) -> str:
        if path not in source_cache:
            source_cache[path] = read_text(repo, path)
        return source_cache[path]

    def cached_imports(path: str, source: str) -> list[str]:
        if path not in import_cache:
            import_cache[path] = imported_modules(source)
        return import_cache[path]

    def add(issue: ImportClosureIssue) -> None:
        key = (
            issue.importer,
            issue.imported_module,
            issue.dependency_path,
            issue.reason,
        )
        if key not in seen_issue:
            seen_issue.add(key)
            issues.append(issue)

    for entrypoint in sorted(roots):
        if entrypoint not in indexed:
            add(
                ImportClosureIssue(
                    entrypoint,
                    entrypoint,
                    "",
                    entrypoint,
                    "entrypoint is not present in the Git index",
                )
            )
            continue
        pending = [entrypoint]
        visited: set[str] = set()
        while pending:
            importer = pending.pop()
            if importer in visited:
                continue
            visited.add(importer)
            try:
                source = cached_source(importer)
            except (OSError, RuntimeError) as exc:
                add(
                    ImportClosureIssue(
                        entrypoint,
                        importer,
                        "",
                        importer,
                        f"candidate source cannot be read: {exc}",
                    )
                )
                continue
            for module in cached_imports(importer, source):
                if module in indexed_ambiguous:
                    add(
                        ImportClosureIssue(
                            entrypoint,
                            importer,
                            module,
                            ", ".join(indexed_ambiguous[module]),
                            "module identity is ambiguous in the Git index",
                        )
                    )
                    continue
                dependency = indexed_modules.get(module)
                if dependency is None:
                    loose = untracked_modules.get(module)
                    loose_paths = untracked_ambiguous.get(module)
                    if loose is not None or loose_paths is not None:
                        paths = (loose,) if loose is not None else loose_paths or ()
                        add(
                            ImportClosureIssue(
                                entrypoint,
                                importer,
                                module,
                                ", ".join(paths),
                                "import resolves only to an untracked Lean module",
                            )
                        )
                        continue
                    prefix = module.split(".", 1)[0]
                    if prefix in repository_prefixes or prefix == "AppliedModelingLib":
                        add(
                            ImportClosureIssue(
                                entrypoint,
                                importer,
                                module,
                                "",
                                "repository-owned import has no module in the candidate tree",
                            )
                        )
                    elif prefix not in EXTERNAL_MODULE_PREFIXES:
                        add(
                            ImportClosureIssue(
                                entrypoint,
                                importer,
                                module,
                                "",
                                "import prefix is neither repository-owned nor in the explicit external-module registry",
                            )
                        )
                    continue
                if candidate == "index" and dependency in unstaged:
                    add(
                        ImportClosureIssue(
                            entrypoint,
                            importer,
                            module,
                            dependency,
                            "imported Lean module has unstaged changes",
                        )
                    )
                pending.append(dependency)
    return issues


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo", type=Path, default=ROOT, help="Git worktree to inspect"
    )
    parser.add_argument(
        "--candidate",
        choices=("index", "worktree", "both"),
        default="both",
        help="candidate surface to validate (default: both)",
    )
    args = parser.parse_args()

    modes = ("index", "worktree") if args.candidate == "both" else (args.candidate,)
    issues: list[ImportClosureIssue] = []
    try:
        for mode in modes:
            issues.extend(dependency_closure_issues(args.repo, candidate=mode))
    except RuntimeError as exc:
        parser.error(str(exc))
    for issue in issues:
        print("ERROR: " + issue.format(), file=sys.stderr)
    if issues:
        print(f"Lean import closure: {len(issues)} error(s)", file=sys.stderr)
        return 1
    print("Lean import closure: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
