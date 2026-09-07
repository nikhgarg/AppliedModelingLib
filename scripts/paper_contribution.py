#!/usr/bin/env python3
"""Create and validate an isolated AppliedModelingLib paper contribution.

This is the stable contributor-facing facade.  It deliberately keeps a
single-paper pull request independent from every unchanged paper.  The same
base/head classifier is used locally and in CI; anything outside the exact
paper-owned boundary escalates to a docs, aggregate-only, or repository
integration lane according to its actual scope.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
from contextlib import contextmanager
from dataclasses import asdict, dataclass
from pathlib import Path, PurePosixPath
from typing import Callable, Iterable, Iterator, Mapping, Sequence

try:
    from scripts.tomllib_compat import tomllib, tomllib_dependency_problem
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from tomllib_compat import tomllib, tomllib_dependency_problem

try:
    from scripts.check_formalization_engine_revision import (
        runtime_engine_registration_error,
    )
    from scripts.closeout_execution_state import (
        closeout_worker_state_path,
        read_execution_state,
    )
    from scripts.closeout_plan_receipt import load_validated_closeout_plan_receipt
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from check_formalization_engine_revision import runtime_engine_registration_error
    from closeout_execution_state import closeout_worker_state_path, read_execution_state
    from closeout_plan_receipt import load_validated_closeout_plan_receipt


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
PYTHON = sys.executable
PAPER_ID_RE = re.compile(r"^[A-Z][A-Za-z0-9]*\d{2}[A-Z][A-Za-z0-9]*$")
FULL_STATUSES = {"formalized", "formalized with caveat"}
PARTIAL_STATUSES = {"partially formalized", "not formalized"}
SCAFFOLD_STATUSES = {"paper draft", "scaffold", "not started"}
KNOWN_STATUSES = FULL_STATUSES | PARTIAL_STATUSES | SCAFFOLD_STATUSES
PROFILE_RANK = {"scaffold": 0, "partial": 1, "full": 2}
REPOSITORY_VISIBILITIES = {"public", "private_only"}
AGGREGATE_PATHS = {
    "docs/PAPER_STATUS.md",
    "papers/human_status.json",
    "papers/status.json",
    "site/index.html",
}
SITE_GENERATED_MARKERS = (
    (
        "<!-- BEGIN GENERATED LIBRARY COMPONENT ROWS -->",
        "<!-- END GENERATED LIBRARY COMPONENT ROWS -->",
    ),
    (
        "<!-- BEGIN GENERATED PROJECT STATS -->",
        "<!-- END GENERATED PROJECT STATS -->",
    ),
    (
        "<!-- BEGIN GENERATED PAPER STATUS ROWS -->",
        "<!-- END GENERATED PAPER STATUS ROWS -->",
    ),
)
SOURCE_TEXT_STEMS = {
    "extracted-text",
    "full-text",
    "fulltext",
    "manuscript",
    "paper",
    "paper-text",
    "source",
    "source-text",
    "source-transcript",
    "transcript",
}
ROOT_CONTRIBUTOR_DOCS = {"CONTRIBUTING.md", "README.md", "CITATION.cff"}


class ContributionError(RuntimeError):
    """A user-actionable contribution boundary failure."""


@contextmanager
def _scope_repository(root: Path | None) -> Iterator[None]:
    """Temporarily direct a trusted command at an external checkout.

    CI executes the orchestration code archived from the trusted base while
    classifying or validating the candidate checkout.  The candidate's
    committed helper scripts are still executed where they need repository-
    relative discovery, but repository identity is rechecked after every
    executable phase.
    """

    global ROOT, PAPERS
    if root is None:
        yield
        return

    candidate = root.expanduser().resolve()
    try:
        probe = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=candidate,
            text=True,
            capture_output=True,
            check=False,
        )
    except OSError as exc:
        raise ContributionError(f"could not inspect --repo {candidate}: {exc}") from exc
    if probe.returncode != 0:
        detail = (probe.stderr or probe.stdout).strip()
        raise ContributionError(f"--repo is not a Git repository: {detail}")
    discovered = Path(probe.stdout.strip()).resolve()
    if discovered != candidate:
        raise ContributionError(
            f"--repo must name the repository root ({discovered}, not {candidate})"
        )

    previous_root, previous_papers = ROOT, PAPERS
    ROOT, PAPERS = candidate, candidate / "papers"
    try:
        yield
    finally:
        ROOT, PAPERS = previous_root, previous_papers


@dataclass(frozen=True)
class ChangedPath:
    status: str
    path: str


@dataclass(frozen=True)
class CommittedInput:
    path: str
    mode: str
    object_id: str


@dataclass(frozen=True)
class CommittedInputSnapshot:
    commit: str
    object_format: str
    entries: tuple[CommittedInput, ...]


@dataclass(frozen=True)
class ContributionPlan:
    schema: int
    mode: str
    base: str
    head: str
    merge_base: str
    paper: str
    new_paper: bool
    profile: str
    blocked: bool
    changed_paths: tuple[ChangedPath, ...]
    reasons: tuple[str, ...]

    def to_json(self) -> str:
        return json.dumps(asdict(self), indent=2, sort_keys=True) + "\n"


def _run(
    argv: Sequence[str],
    *,
    capture_output: bool = False,
    check: bool = True,
) -> subprocess.CompletedProcess[str]:
    print("+ " + " ".join(shlex.quote(part) for part in argv), flush=True)
    return subprocess.run(
        list(argv),
        cwd=ROOT,
        text=True,
        capture_output=capture_output,
        check=check,
    )


def _git_text(*args: str) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip()
        raise ContributionError(f"git {' '.join(args)} failed: {detail}")
    return proc.stdout


def _commit(ref: str) -> str:
    value = _git_text("rev-parse", "--verify", f"{ref}^{{commit}}").strip()
    if not re.fullmatch(r"[0-9a-f]{40}", value):
        raise ContributionError(f"could not resolve commit {ref!r}")
    return value


def _git_blob(commit: str, path: str) -> bytes | None:
    proc = subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=ROOT,
        capture_output=True,
        check=False,
    )
    if proc.returncode == 0:
        return proc.stdout
    return None


def _changed_paths(merge_base: str, head: str) -> tuple[ChangedPath, ...]:
    proc = subprocess.run(
        [
            "git",
            "diff",
            "--name-status",
            "-z",
            "--no-renames",
            merge_base,
            head,
        ],
        cwd=ROOT,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        raise ContributionError(proc.stderr.decode("utf-8", errors="replace").strip())
    fields = proc.stdout.split(b"\0")
    if fields and fields[-1] == b"":
        fields.pop()
    if len(fields) % 2:
        raise ContributionError("git returned an invalid name-status stream")
    changes: list[ChangedPath] = []
    for index in range(0, len(fields), 2):
        status = fields[index].decode("ascii", errors="strict")
        path = fields[index + 1].decode("utf-8", errors="strict")
        normalized = PurePosixPath(path)
        if normalized.is_absolute() or ".." in normalized.parts:
            raise ContributionError(f"unsafe changed path from git: {path!r}")
        changes.append(ChangedPath(status=status, path=normalized.as_posix()))
    return tuple(changes)


def _commit_history_paths(
    merge_base: str, head: str, *, include_deletions: bool = True
) -> tuple[str, ...]:
    """Return every path mentioned by a non-merge candidate commit."""

    merge_commits = _git_text(
        "rev-list", "--min-parents=2", f"{merge_base}..{head}"
    ).splitlines()
    if merge_commits:
        raise ContributionError(
            "paper-scoped history must be rebased and contain no merge commits"
        )
    proc = subprocess.run(
        [
            "git",
            "log",
            "--format=",
            "--name-only",
            "-z",
            "--no-renames",
            *([] if include_deletions else ["--diff-filter=ACMRT"]),
            f"{merge_base}..{head}",
        ],
        cwd=ROOT,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        raise ContributionError(proc.stderr.decode("utf-8", errors="replace").strip())
    paths: set[str] = set()
    for raw in proc.stdout.split(b"\0"):
        if not raw:
            continue
        path = raw.decode("utf-8", errors="strict").lstrip("\n")
        normalized = PurePosixPath(path)
        if normalized.is_absolute() or ".." in normalized.parts:
            raise ContributionError(f"unsafe historical path from git: {path!r}")
        paths.add(normalized.as_posix())
    return tuple(sorted(paths))


def _unsafe_public_artifact(path: str) -> bool:
    parts = PurePosixPath(path).parts
    if not parts:
        return False
    if parts[0] == ".scratch":
        return True
    if len(parts) < 3 or parts[0] != "papers":
        return False
    relative = parts[2:]
    if not relative:
        return False
    name = relative[-1].lower()
    source_candidate = PurePosixPath(name)
    source_directory = re.sub(r"[-_.]", "", relative[0].lower())
    return bool(
        (len(relative) > 1 and source_directory.startswith("source"))
        or source_directory in {"auditsource", "papersource"}
        or name.startswith("source-audited")
        or name in {"source.pdf", "source.txt", "source.tex"}
        or (
            source_candidate.stem in SOURCE_TEXT_STEMS
            and source_candidate.suffix in {".md", ".txt", ".text", ".tex"}
        )
        or name.endswith((".doc", ".docx", ".rtf", ".epub"))
        or (
            name.endswith(".pdf")
            and tuple(relative) not in {
                ("docs", "DependencyDAG.pdf"),
                ("docs", "HUMAN_REVIEW_PACKET.pdf"),
            }
        )
        or name.endswith(
            (
                ".7z",
                ".bz2",
                ".gz",
                ".rar",
                ".tar",
                ".tar.bz2",
                ".tar.gz",
                ".tar.xz",
                ".tgz",
                ".txz",
                ".xz",
                ".zip",
            )
        )
    )


def _site_static_shell(blob: bytes) -> str:
    """Remove generated regions while preserving every static site byte."""

    try:
        text = blob.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ContributionError(f"site/index.html is not UTF-8: {exc}") from exc
    pieces: list[str] = []
    cursor = 0
    for begin, end in SITE_GENERATED_MARKERS:
        if text.count(begin) != 1 or text.count(end) != 1:
            raise ContributionError(
                "site/index.html must contain each generated marker exactly once"
            )
        start = text.find(begin, cursor)
        finish = text.find(end, start + len(begin))
        if start < cursor or finish < 0:
            raise ContributionError(
                "site/index.html generated markers are missing, reordered, or overlapping"
            )
        pieces.append(text[cursor : start + len(begin)])
        pieces.append("\n<generated-region>\n")
        cursor = finish
    pieces.append(text[cursor:])
    return "".join(pieces)


def _paper_for_path(path: str) -> str | None:
    parts = PurePosixPath(path).parts
    if not parts or parts[0] != "papers":
        return None
    if len(parts) >= 3 and PAPER_ID_RE.fullmatch(parts[1]):
        return parts[1]
    if len(parts) == 2 and parts[1].endswith(".lean"):
        candidate = parts[1][:-5]
        if PAPER_ID_RE.fullmatch(candidate):
            return candidate
    return None


def _tree_mode(commit: str, path: str) -> tuple[str, str] | None:
    output = _git_text("ls-tree", "-z", commit, "--", path)
    if not output:
        return None
    record = output.split("\0", 1)[0]
    metadata, _separator, recorded_path = record.partition("\t")
    mode, kind, _object = metadata.split(" ", 2)
    if recorded_path != path:
        return None
    return mode, kind


def _paper_library_names(lakefile_bytes: bytes) -> set[str]:
    try:
        payload = tomllib.loads(lakefile_bytes.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        raise ContributionError(f"lakefile.toml is invalid: {exc}") from exc
    libraries = payload.get("lean_lib", [])
    if not isinstance(libraries, list):
        raise ContributionError("lakefile.toml lean_lib entries are not a list")
    return {
        str(item.get("name"))
        for item in libraries
        if isinstance(item, Mapping) and item.get("srcDir") == "papers"
    }


def _exact_lake_registration(
    base_bytes: bytes,
    head_bytes: bytes,
    paper: str,
) -> tuple[bool, str]:
    try:
        from scripts.paper_target_registration import registration_is_exact_addition
    except ModuleNotFoundError:  # pragma: no cover - supports direct script execution.
        from paper_target_registration import registration_is_exact_addition

    try:
        exact = registration_is_exact_addition(
            base_bytes.decode("utf-8"),
            head_bytes.decode("utf-8"),
            paper,
        )
    except (UnicodeDecodeError, ValueError) as exc:
        return False, str(exc)
    if exact:
        return True, ""
    return False, "lakefile change is not exactly one additive paper lean_lib"


LeanModuleGraphLoader = Callable[
    [Path, str, int], tuple[tuple[str, ...] | None, str]
]


def _default_lean_module_graph_loader() -> LeanModuleGraphLoader:
    """Load the graph implementation before contributor Lean can execute."""

    # Prefer the package import used by the rest of the closeout stack.  Using
    # the script-directory import first can load a second module object when
    # this facade is imported as ``scripts.paper_contribution``; that splits
    # instrumentation and makes the graph-only path needlessly noncanonical.
    try:
        from scripts.lean_import_closure import lean_loaded_module_closure
    except ModuleNotFoundError:  # pragma: no cover - supports direct script execution.
        from lean_import_closure import lean_loaded_module_closure
    return lean_loaded_module_closure


def _graph_only_lean_module_graph_loader() -> LeanModuleGraphLoader:
    """Read an already-built Lean graph without mutating a closeout receipt.

    A full closeout has either scheduled the root build or validated an exact
    completed receipt. Its post-closeout contribution-isolation check therefore
    needs the authoritative graph, but must not compile again and change the
    compiled inputs that made the receipt current.
    """

    try:
        from scripts.lean_import_closure import lean_loaded_module_closure
    except ModuleNotFoundError:  # pragma: no cover - supports direct script execution.
        from lean_import_closure import lean_loaded_module_closure

    def load_graph(root: Path, entry_module: str, timeout_seconds: int) -> tuple[
        tuple[str, ...] | None, str
    ]:
        return lean_loaded_module_closure(
            root,
            entry_module,
            timeout_seconds,
            build_entry_module=False,
        )

    return load_graph


def _semantic_cross_paper_dependencies(
    paper: str,
    paper_libraries: set[str],
    *,
    root: Path | None = None,
    module_graph_loader: LeanModuleGraphLoader | None = None,
) -> tuple[str, ...]:
    """Return other paper modules in Lean's transitive root-module closure.

    Lean, rather than Python source spelling, owns reachability.  In
    particular, quoted module identifiers and dependencies reached through a
    paper-local bridge have the same normalized module identity here.
    """

    if module_graph_loader is None:
        try:
            from lean_import_closure import DEFAULT_LEAN_GRAPH_TIMEOUT_SECONDS
        except ModuleNotFoundError:  # pragma: no cover - supports module imports.
            from scripts.lean_import_closure import DEFAULT_LEAN_GRAPH_TIMEOUT_SECONDS

        module_graph_loader = _default_lean_module_graph_loader()
        timeout_seconds = DEFAULT_LEAN_GRAPH_TIMEOUT_SECONDS
    else:
        timeout_seconds = 600

    graph_root = ROOT if root is None else root
    modules, problem = module_graph_loader(graph_root, paper, timeout_seconds)
    if modules is None:
        raise ContributionError(
            f"could not verify the semantic Lean import closure for {paper}: "
            + (problem or "Lean returned no module graph")
        )
    if paper not in modules:
        raise ContributionError(
            f"semantic Lean import closure for {paper} omits its root module"
        )

    paper_root = graph_root / "papers"
    path_owned_papers = {
        path.name
        for path in paper_root.iterdir()
        if path.is_dir() and PAPER_ID_RE.fullmatch(path.name)
    }
    other_papers = (paper_libraries | path_owned_papers) - {paper}
    dependencies = {
        module
        for module in modules
        if any(module == owner or module.startswith(owner + ".") for owner in other_papers)
    }
    return tuple(sorted(dependencies))


@contextmanager
def _trusted_base_checkout(commit: str) -> Iterator[Path]:
    """Expose exact committed Lean inputs for a Lean-owned base graph query.

    The archive contains every committed Lean source plus Lake/toolchain
    controls, but omits audit evidence and source artifacts.  It has its own
    build directory and may share downloaded Lake packages, which are fixed by
    the unchanged manifest; candidate sources and build artifacts stay out.
    """

    commit = _commit(commit)
    temporary_parent = ROOT / ".lake"
    temporary_parent.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix="paper-contribution-base-",
        dir=temporary_parent,
    ) as temporary:
        checkout = Path(temporary) / "repository"
        checkout.mkdir()
        controls = [
            path
            for path in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")
            if _git_blob(commit, path) is not None
        ]
        archive_argv = [
            "git",
            "archive",
            "--format=tar",
            commit,
            "--",
            ":(glob)**/*.lean",
            *controls,
        ]
        with tempfile.TemporaryFile(dir=temporary) as archive_stream:
            proc = subprocess.run(
                archive_argv,
                cwd=ROOT,
                stdout=archive_stream,
                stderr=subprocess.PIPE,
                check=False,
            )
            if proc.returncode != 0:
                detail = proc.stderr.decode("utf-8", errors="replace").strip()
                raise ContributionError(
                    f"could not archive trusted-base Lean inputs: {detail}"
                )
            archive_stream.seek(0)
            with tarfile.open(fileobj=archive_stream, mode="r:") as archive:
                for member in archive:
                    relative = PurePosixPath(member.name)
                    if relative.is_absolute() or ".." in relative.parts:
                        raise ContributionError(
                            f"trusted-base archive contains unsafe path {member.name!r}"
                        )
                    destination = checkout.joinpath(*relative.parts)
                    if member.isdir():
                        destination.mkdir(parents=True, exist_ok=True)
                        continue
                    if not member.isfile():
                        raise ContributionError(
                            "trusted-base Lean archive contains a non-file entry: "
                            + member.name
                        )
                    source = archive.extractfile(member)
                    if source is None:
                        raise ContributionError(
                            f"could not read trusted-base archive member {member.name}"
                        )
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    with destination.open("wb") as output:
                        shutil.copyfileobj(source, output)

        candidate_packages = ROOT / ".lake" / "packages"
        if candidate_packages.is_dir():
            base_lake = checkout / ".lake"
            base_lake.mkdir(exist_ok=True)
            (base_lake / "packages").symlink_to(
                candidate_packages.resolve(), target_is_directory=True
            )
        yield checkout


def _render_cross_paper_dependencies(
    root: Path,
    dependencies: Iterable[str],
) -> str:
    rendered: list[str] = []
    for module in dependencies:
        relative = PurePosixPath("papers", *module.split(".")).with_suffix(".lean")
        if (root / relative).is_file():
            rendered.append(f"{module} ({relative.as_posix()})")
        else:
            rendered.append(module)
    return ", ".join(rendered)


def _assert_semantically_isolated_paper(
    paper: str,
    *,
    trusted_base: str | None = None,
    allow_existing_development_dependencies: bool = False,
    module_graph_loader: LeanModuleGraphLoader | None = None,
) -> None:
    """Reject cross-paper modules newly introduced by this contribution.

    A new paper, or a check without an explicit trusted base, must be wholly
    independent.  An existing-paper repair may retain modules already present
    in the exact trusted-base Lean closure; it may not widen that closure.
    """

    try:
        paper_libraries = _paper_library_names(
            (ROOT / "lakefile.toml").read_bytes()
        )
    except OSError as exc:
        raise ContributionError(f"could not read lakefile.toml: {exc}") from exc
    if paper not in paper_libraries:
        raise ContributionError(f"lakefile.toml does not register paper target {paper}")
    dependencies = _semantic_cross_paper_dependencies(
        paper,
        paper_libraries,
        module_graph_loader=module_graph_loader,
    )
    if not dependencies:
        return

    if allow_existing_development_dependencies:
        base_root = _git_blob("HEAD", f"papers/{paper}.lean")
        base_status = _git_blob("HEAD", f"papers/{paper}/status.json")
        if base_root is not None and base_status is not None:
            print(
                "development check observed cross-paper dependencies; exact "
                "trusted-base comparison is deferred to check --base/prepare-pr"
            )
            return

    if trusted_base is not None:
        base_lake = _git_blob(trusted_base, "lakefile.toml")
        if base_lake is None:
            raise ContributionError(
                "could not verify retained cross-paper dependencies: "
                "trusted base has no lakefile.toml"
            )
        base_libraries = _paper_library_names(base_lake)
        if paper not in base_libraries:
            raise ContributionError(
                f"new paper {paper} may not depend on another paper target"
            )
        with _trusted_base_checkout(trusted_base) as base_root:
            base_dependencies = _semantic_cross_paper_dependencies(
                paper,
                base_libraries,
                root=base_root,
                module_graph_loader=module_graph_loader,
            )
        introduced = tuple(sorted(set(dependencies) - set(base_dependencies)))
        if not introduced:
            return
        detail = _render_cross_paper_dependencies(ROOT, introduced)
        raise ContributionError(
            f"semantic Lean import closure for {paper} introduces new other-paper "
            f"module(s) relative to the trusted base: {detail}"
        )

    detail = _render_cross_paper_dependencies(ROOT, dependencies)
    raise ContributionError(
        f"semantic Lean import closure for {paper} reaches other paper target(s): "
        + detail
    )


def _status_metadata(head: str, paper: str) -> tuple[str, str, str]:
    raw = _git_blob(head, f"papers/{paper}/status.json")
    if raw is None:
        return "", "", "paper status.json is missing from the candidate tree"
    try:
        payload = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        return "", "", f"paper status.json is invalid: {exc}"
    if not isinstance(payload, dict):
        return "", "", "paper status.json must contain an object"
    if payload.get("id") != paper:
        return "", "", f"status.id must be {paper!r}"
    status = str(payload.get("status") or "").strip()
    if status not in KNOWN_STATUSES:
        return "", "", f"status.status has unsupported value {status!r}"
    visibility = str(payload.get("repository_visibility") or "").strip()
    if visibility not in REPOSITORY_VISIBILITIES:
        return (
            "",
            "",
            "status.repository_visibility must be `public` or `private_only`",
        )
    if status in FULL_STATUSES:
        return "full", visibility, ""
    if status in PARTIAL_STATUSES:
        return "partial", visibility, ""
    return "scaffold", visibility, ""


def _docs_only(changes: Iterable[ChangedPath]) -> bool:
    for change in changes:
        path = change.path
        if path in ROOT_CONTRIBUTOR_DOCS:
            continue
        if path.startswith("docs/"):
            continue
        if path.startswith(".github/ISSUE_TEMPLATE/"):
            continue
        if path == ".github/pull_request_template.md":
            continue
        return False
    return True


def contribution_plan(base_ref: str, head_ref: str = "HEAD") -> ContributionPlan:
    """Classify an exact committed contribution without reading paper semantics."""

    base = _commit(base_ref)
    head = _commit(head_ref)
    merge_base = _git_text("merge-base", base, head).strip()
    changes = _changed_paths(merge_base, head)
    reasons: list[str] = []
    blocked = False
    if merge_base != base:
        reasons.append(
            "narrowed contribution lanes require a branch rebased onto the exact base"
        )
    try:
        history_paths = _commit_history_paths(merge_base, head)
        introduced_paths = _commit_history_paths(merge_base, head, include_deletions=False)
    except ContributionError as exc:
        history_paths = ()
        introduced_paths = ()
        reasons.append(str(exc))
    # A deletion removes content already reachable from the public base. Added
    # and later deleted source bytes still occur in introduced_paths and block.
    for path in introduced_paths:
        if _unsafe_public_artifact(path):
            blocked = True
            reasons.append(
                f"public pull-request history contains a local/source artifact: {path}"
            )
    papers = sorted(
        {paper for change in changes if (paper := _paper_for_path(change.path))}
    )

    if not changes:
        if any(
            not _docs_only((ChangedPath(status="H", path=path),))
            for path in history_paths
        ):
            reasons.append("commit history contains reverted non-documentation paths")
        return ContributionPlan(
            schema=2,
            mode="integration" if reasons else "docs",
            base=base,
            head=head,
            merge_base=merge_base,
            paper="",
            new_paper=False,
            profile="none",
            blocked=blocked,
            changed_paths=changes,
            reasons=tuple(dict.fromkeys(reasons or ["no changed paths"])),
        )

    if all(change.path in AGGREGATE_PATHS for change in changes):
        aggregate_reasons = list(reasons)
        for path in history_paths:
            if path not in AGGREGATE_PATHS:
                aggregate_reasons.append(
                    f"aggregate-only history touched non-aggregate path: {path}"
                )
        for change in changes:
            if change.status != "M":
                aggregate_reasons.append(
                    f"aggregate projection {change.path} must be modified, not {change.status}"
                )
                continue
            for label, commit in (("base", merge_base), ("candidate", head)):
                mode = _tree_mode(commit, change.path)
                if mode != ("100644", "blob"):
                    aggregate_reasons.append(
                        f"aggregate projection {change.path} is not a regular file in {label}"
                    )
        site_path = "site/index.html"
        if any(change.path == site_path for change in changes):
            base_site = _git_blob(merge_base, site_path)
            head_site = _git_blob(head, site_path)
            if base_site is None or head_site is None:
                aggregate_reasons.append("site/index.html is missing from base or candidate")
            else:
                try:
                    static_unchanged = _site_static_shell(base_site) == _site_static_shell(
                        head_site
                    )
                except ContributionError as exc:
                    aggregate_reasons.append(str(exc))
                else:
                    if not static_unchanged:
                        aggregate_reasons.append(
                            "aggregate-only site edit changes bytes outside generated regions"
                        )
        if not aggregate_reasons:
            return ContributionPlan(
                schema=2,
                mode="aggregate",
                base=base,
                head=head,
                merge_base=merge_base,
                paper="",
                new_paper=False,
                profile="none",
                blocked=False,
                changed_paths=changes,
                reasons=(),
            )
        reasons = aggregate_reasons

    final_aggregate_paths = {
        change.path for change in changes if change.path in AGGREGATE_PATHS
    }
    historical_aggregate_paths = set(history_paths).intersection(AGGREGATE_PATHS)
    if final_aggregate_paths or historical_aggregate_paths:
        reasons.append(
            "aggregate projection paths may not be mixed into another narrowed lane"
        )

    if not papers:
        final_paths = {change.path for change in changes}
        for path in history_paths:
            if path in final_paths:
                continue
            if not _docs_only((ChangedPath(status="H", path=path),)):
                reasons.append(f"commit history touched non-documentation path: {path}")

    if len(papers) != 1:
        if len(papers) > 1:
            reasons.append("more than one paper is changed")
        elif not _docs_only(changes):
            reasons.append("the change is not owned by one paper")
    paper = papers[0] if len(papers) == 1 else ""
    new_paper = bool(
        paper
        and _git_blob(merge_base, f"papers/{paper}/status.json") is None
        and _git_blob(merge_base, f"papers/{paper}.lean") is None
    )
    if paper:
        for path in history_paths:
            if _unsafe_public_artifact(path):
                continue
            owner = _paper_for_path(path)
            if owner == paper:
                continue
            if path == "lakefile.toml" and new_paper:
                continue
            if path not in {change.path for change in changes}:
                reasons.append(f"commit history touched non-paper path: {path}")

        for change in changes:
            owner = _paper_for_path(change.path)
            if owner == paper:
                if change.status not in {"A", "M", "D"}:
                    reasons.append(
                        f"{change.path} has unsupported {change.status} change"
                    )
                continue
            if change.path == "lakefile.toml" and new_paper:
                continue
            if change.path in AGGREGATE_PATHS:
                reasons.append(
                    f"generated aggregate {change.path} belongs to the aggregate-only "
                    "follow-up, not the paper PR"
                )
            else:
                reasons.append(f"shared path changed: {change.path}")

        for change in changes:
            if change.status not in {"A", "M"}:
                continue
            mode = _tree_mode(head, change.path)
            if mode is not None and mode[0] in {"120000", "160000"}:
                reasons.append(f"symlink or submodule is not allowed: {change.path}")

        root_path = f"papers/{paper}.lean"
        status_path = f"papers/{paper}/status.json"
        interface_path = f"papers/{paper}/PaperInterface.lean"
        root_blob = _git_blob(head, root_path)
        if root_blob is None:
            reasons.append(f"missing paper root module {root_path}")
        else:
            expected_import = f"import {paper}.PaperInterface"
            root_lines = [line.strip() for line in root_blob.decode("utf-8").splitlines()]
            if new_paper and root_lines != [expected_import]:
                reasons.append(
                    f"{root_path} must contain exactly `{expected_import}`"
                )
            elif not new_paper and expected_import not in root_lines:
                reasons.append(f"{root_path} must import `{paper}.PaperInterface`")
        if _git_blob(head, status_path) is None:
            reasons.append(f"missing paper-owned status file {status_path}")
        if _git_blob(head, interface_path) is None:
            reasons.append(f"missing paper-facing interface {interface_path}")

        profile, visibility, profile_error = _status_metadata(head, paper)
        if profile_error:
            reasons.append(profile_error)
        elif visibility != "public":
            reasons.append(
                "paper-scoped public PR validation requires "
                "status.repository_visibility = `public`"
            )

        if not new_paper:
            base_profile, base_visibility, base_profile_error = _status_metadata(
                merge_base, paper
            )
            if base_profile_error:
                reasons.append(f"base paper status is invalid: {base_profile_error}")
            elif (
                not profile_error
                and PROFILE_RANK[profile] < PROFILE_RANK[base_profile]
            ):
                reasons.append(
                    f"paper status profile is downgraded from {base_profile} to {profile}"
                )
            if (
                not profile_error
                and base_visibility == "public"
                and visibility != "public"
            ):
                reasons.append("a public paper may not become private in the paper lane")

        base_lake = _git_blob(merge_base, "lakefile.toml")
        head_lake = _git_blob(head, "lakefile.toml")
        if base_lake is None or head_lake is None:
            reasons.append("lakefile.toml is missing from the base or candidate")
            paper_libraries: set[str] = set()
        else:
            paper_libraries = _paper_library_names(head_lake)
            if paper not in paper_libraries:
                reasons.append(f"lakefile.toml does not register paper target {paper}")
            lake_changed = any(change.path == "lakefile.toml" for change in changes)
            if new_paper and not lake_changed:
                reasons.append("new paper has no additive lakefile registration")
            elif new_paper and lake_changed:
                exact, error = _exact_lake_registration(base_lake, head_lake, paper)
                if not exact:
                    reasons.append(error)
            elif lake_changed:
                reasons.append("an existing-paper PR may not change lakefile.toml")

    else:
        profile = "none"

    if paper and not reasons:
        mode = "paper"
    elif not papers and _docs_only(changes) and not reasons:
        mode = "docs"
    else:
        mode = "integration"
    return ContributionPlan(
        schema=2,
        mode=mode,
        base=base,
        head=head,
        merge_base=merge_base,
        paper=paper,
        new_paper=new_paper,
        profile=profile,
        blocked=blocked,
        changed_paths=changes,
        reasons=tuple(dict.fromkeys(reasons)),
    )


def _write_github_output(path: Path, plan: ContributionPlan) -> None:
    values = {
        "mode": plan.mode,
        "paper": plan.paper,
        "new_paper": str(plan.new_paper).lower(),
        "profile": plan.profile,
        "blocked": str(plan.blocked).lower(),
    }
    with path.open("a", encoding="utf-8") as handle:
        for key, value in values.items():
            if "\n" in value or "\r" in value:
                raise ContributionError(f"invalid GitHub output value for {key}")
            handle.write(f"{key}={value}\n")


def _paper_status(paper: str) -> dict[str, object]:
    path = PAPERS / paper / "status.json"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ContributionError(f"could not read {path.relative_to(ROOT)}: {exc}") from exc
    if not isinstance(payload, dict) or payload.get("id") != paper:
        raise ContributionError(f"{path.relative_to(ROOT)} must identify {paper}")
    return payload


def _validation_commands(
    paper: str,
    *,
    fast: bool,
    allow_missing_source_bytes: bool,
) -> list[list[str]]:
    payload = _paper_status(paper)
    status = str(payload.get("status") or "").strip()
    if status not in KNOWN_STATUSES:
        raise ContributionError(f"unsupported paper status {status!r}")
    commands: list[list[str]] = [
        ["lake", "build", f"+{paper}.PaperInterface" if fast else f"+{paper}"]
    ]
    if fast:
        return commands
    if status in FULL_STATUSES:
        command = [
            PYTHON,
            "scripts/audit_repository.py",
            "--paper",
            paper,
            "--paper-closeout",
            "--include-active",
            "--info-limit",
            "0",
            "--no-closeout-state",
        ]
        if allow_missing_source_bytes:
            command.append("--allow-missing-source-bytes")
            # This public-checkout diagnostic cannot establish a source-grounded
            # closeout. Keep it from creating a legacy execution state that
            # would later obstruct the planner-owned strict transaction.
            command.append("--no-closeout-state")
        commands.append(command)
        return commands

    commands.append(
        [
            PYTHON,
            "scripts/sync_paper_status.py",
            "--paper",
            paper,
            "--check",
        ]
    )
    commands.append(
        [PYTHON, "scripts/audit_conclusion_provenance.py", "--paper", paper]
    )
    evidence = [PYTHON, "scripts/audit_evidence_integrity.py", "--paper", paper]
    if allow_missing_source_bytes:
        evidence.append("--allow-missing-source-bytes")
    commands.append(evidence)
    commands.append(
        [
            PYTHON,
            "scripts/review_dashboard.py",
            "--paper",
            paper,
            "--source-inventory-check",
        ]
    )
    if status in PARTIAL_STATUSES:
        for flag in (
            "--statement-check",
            "--source-to-lean-check",
            "--paper-coverage-check",
            "--assumption-check",
        ):
            commands.append(
                [PYTHON, "scripts/review_dashboard.py", "--paper", paper, flag]
            )
    return commands


def _run_json(argv: Sequence[str]) -> dict[str, object]:
    proc = _run(argv, capture_output=True, check=False)
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip()
        raise ContributionError(
            f"command failed with exit code {proc.returncode}: {detail}"
        )
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise ContributionError(
            f"command did not return one JSON object: {argv[0]}"
        ) from exc
    if not isinstance(payload, dict):
        raise ContributionError("command JSON result is not an object")
    return payload


def _current_completed_closeout(plan: Mapping[str, object]) -> bool:
    action = plan.get("next_action")
    if not isinstance(action, Mapping) or action.get("id") != "inspect_existing_closeout":
        return False
    execution = plan.get("last_closeout_execution")
    if not isinstance(execution, Mapping):
        return False
    result = execution.get("result")
    identity = str(plan.get("plan_identity_sha256") or "")
    return bool(
        identity
        and execution.get("state") == "complete"
        and execution.get("exit_code") == 0
        and isinstance(result, Mapping)
        and result.get("semantic_closeout_passed") is True
        and result.get("operational_plan_identity") == identity
    )


def _strict_closeout_completion_is_current(
    paper: str,
    *,
    plan_identity: str,
    deep_paper_prose: bool,
) -> bool:
    """Revalidate one terminal worker without rerunning advisory planning.

    A worker state alone is not enough because inputs may change after its
    final check.  Conversely, a fresh plan-receipt replay is sufficient here:
    it preserves the strict external-artifact/TOCTOU guarantee without
    repeating raw preflight, dashboard deserialization, or item reuse.
    """

    if runtime_engine_registration_error(ROOT):
        return False
    state, error = read_execution_state(closeout_worker_state_path(ROOT, paper))
    if error or not isinstance(state, Mapping) or state.get("state") != "complete":
        return False
    result = state.get("result")
    if (
        not isinstance(result, Mapping)
        or state.get("exit_code") != 0
        or result.get("semantic_closeout_passed") is not True
        or result.get("operational_plan_identity") != plan_identity
    ):
        return False
    _receipt, receipt_error = load_validated_closeout_plan_receipt(
        ROOT,
        paper=paper,
        deep_paper_prose=deep_paper_prose,
        expected_plan_identity=plan_identity,
    )
    return not receipt_error


def _validated_planner_command(
    paper: str,
    plan: Mapping[str, object],
    action: Mapping[str, object],
) -> list[str]:
    """Return a canonical command only for one exact known-safe action shape."""

    action_id = str(action.get("id") or "")
    raw_argv = action.get("argv")
    if not isinstance(raw_argv, list) or any(
        not isinstance(part, str) or not part for part in raw_argv
    ):
        raise ContributionError(f"planner returned invalid argv for {action_id}")
    argv = list(raw_argv)
    if action_id == "paper_build":
        expected = ["env", "LEAN_NUM_THREADS=1", "lake", "build", f"+{paper}"]
        if argv != expected:
            raise ContributionError("planner paper_build command is not canonical")
        return expected
    if action_id == "strict_closeout":
        identity = str(plan.get("plan_identity_sha256") or "")
        if not re.fullmatch(r"[0-9a-f]{64}", identity):
            raise ContributionError("strict closeout plan has no canonical identity")
        expected_tail = ["scripts/run_paper_closeout.py", "--paper", paper]
        if "--deep-paper-prose" in argv:
            expected_tail.append("--deep-paper-prose")
        expected_tail.extend(["--plan-identity", identity])
        if "--new-run" in argv:
            expected_tail.append("--new-run")
        if len(argv) != 1 + len(expected_tail) or argv[1:] != expected_tail:
            raise ContributionError("planner strict_closeout command is not canonical")
        if Path(argv[0]).name not in {"python", "python3", Path(PYTHON).name}:
            raise ContributionError("planner strict_closeout interpreter is not Python")
        return [PYTHON, *expected_tail]
    raise ContributionError(f"closeout action `{action_id}` is not machine-safe")


def _execute_planned_closeout(
    paper: str,
    *,
    after_phase: Callable[[], None] | None = None,
    ensure_semantic_isolation: Callable[[], None] | None = None,
) -> None:
    """Follow only machine-safe planner transitions until exact acceptance."""

    reassert = after_phase or (lambda: None)
    isolation_checked = False

    def ensure_isolation() -> None:
        """Run the PR-scope graph check only after planner eligibility."""

        nonlocal isolation_checked
        if ensure_semantic_isolation is None or isolation_checked:
            return
        ensure_semantic_isolation()
        reassert()
        isolation_checked = True

    planner = [PYTHON, "scripts/closeout_reuse_plan.py", "--paper", paper]
    retried_publication_races: set[tuple[str, str]] = set()
    for _step in range(12):
        plan = _run_json(planner)
        reassert()
        if _current_completed_closeout(plan):
            ensure_isolation()
            print("reused the current successful closeout execution")
            return
        action = plan.get("next_action")
        if not isinstance(action, Mapping):
            reasons = plan.get("invalidation_reasons")
            raise ContributionError(
                "closeout planner exposed no executable next action"
                + (f": {reasons}" if reasons else "")
            )
        action_id = str(action.get("id") or "")
        if action_id == "replan_current_inputs":
            retryable = action.get("retryable") is True
            disposition = str(action.get("publication_disposition") or "")
            input_identity = str(action.get("input_identity_sha256") or "")
            reason = str(
                action.get("reason")
                or plan.get("operational_plan_error")
                or "the exact operational input snapshot could not be frozen"
            )
            if not retryable:
                raise ContributionError(
                    "closeout planner could not publish an operational receipt "
                    f"({disposition or 'unclassified'}): {reason}"
                )
            if disposition not in {"source_race", "compiled_race"} or not re.fullmatch(
                r"[0-9a-f]{64}", input_identity
            ):
                raise ContributionError(
                    "closeout planner exposed an invalid retryable receipt-publication "
                    f"transition: {reason}"
                )
            retry_key = (disposition, input_identity)
            if retry_key in retried_publication_races:
                raise ContributionError(
                    "closeout planner repeated the same receipt-publication race "
                    f"without new inputs ({disposition} {input_identity}): {reason}"
                )
            retried_publication_races.add(retry_key)
            continue
        if action_id not in {"paper_build", "strict_closeout"}:
            reason = str(action.get("reason") or "manual inspection is required")
            raise ContributionError(
                f"closeout stopped at `{action_id}`: {reason}"
            )
        if action_id == "strict_closeout":
            ensure_isolation()
        _run(_validated_planner_command(paper, plan, action))
        reassert()
        if action_id == "strict_closeout":
            identity = str(plan.get("plan_identity_sha256") or "")
            raw_argv = action.get("argv")
            deep_paper_prose = isinstance(raw_argv, list) and (
                "--deep-paper-prose" in raw_argv
            )
            if _strict_closeout_completion_is_current(
                paper,
                plan_identity=identity,
                deep_paper_prose=deep_paper_prose,
            ):
                print("strict closeout completed with a current terminal receipt")
                return
        if action_id == "paper_build":
            # The graph query needs the paper target's fresh compiled surface.
            # Run it before the dependent manifest refresh, and never before a
            # planner preflight has ruled out a source/status stop.
            ensure_isolation()

    raise ContributionError("closeout planner did not reach a terminal result in 12 steps")


def check_paper(
    paper: str,
    *,
    base: str | None,
    fast: bool,
    allow_missing_source_bytes: bool,
) -> None:
    if not PAPER_ID_RE.fullmatch(paper):
        raise ContributionError(f"invalid paper id {paper!r}")
    module_graph_loader = _default_lean_module_graph_loader()
    plan: ContributionPlan | None = None

    def reassert() -> None:
        return None

    if base is not None:
        _require_clean_worktree()
        plan = contribution_plan(base)
        if plan.mode != "paper" or plan.paper != paper:
            detail = "; ".join(plan.reasons) or f"scope is {plan.mode}"
            raise ContributionError(
                f"candidate is not an isolated {paper} contribution: {detail}"
            )
        expected_head = plan.head
        committed_inputs = _committed_input_snapshot(expected_head, paper)
        trusted_script_root = Path(__file__).resolve().parent
        trusted_scripts = (
            trusted_script_root,
            _script_tree_digest(trusted_script_root),
        )

        def reassert() -> None:
            _require_committed_identity(
                expected_head,
                inputs=committed_inputs,
                trusted_scripts=trusted_scripts,
            )

        reassert()
    status = str(_paper_status(paper).get("status") or "").strip()
    if status in FULL_STATUSES and not fast and not allow_missing_source_bytes:
        _run(
            [
                PYTHON,
                "scripts/sync_paper_status.py",
                "--paper",
                paper,
                "--check",
            ]
        )
        reassert()

        graph_only_loader = _graph_only_lean_module_graph_loader()

        def closeout_isolation_graph_loader(
            root: Path, entry_module: str, timeout_seconds: int
        ) -> tuple[tuple[str, ...] | None, str]:
            # A trusted-base graph runs in an isolated checkout. It may build
            # there without mutating the candidate closeout's compiled inputs.
            if root.resolve() != ROOT.resolve():
                return module_graph_loader(root, entry_module, timeout_seconds)
            return graph_only_loader(root, entry_module, timeout_seconds)

        def ensure_semantic_isolation() -> None:
            _assert_semantically_isolated_paper(
                paper,
                trusted_base=(
                    plan.merge_base if plan is not None and not plan.new_paper else None
                ),
                allow_existing_development_dependencies=plan is None,
                module_graph_loader=closeout_isolation_graph_loader,
            )

        _execute_planned_closeout(
            paper,
            after_phase=reassert,
            ensure_semantic_isolation=ensure_semantic_isolation,
        )
    else:
        commands = _validation_commands(
            paper,
            fast=fast,
            allow_missing_source_bytes=allow_missing_source_bytes,
        )
        _run(commands[0])
        reassert()
        _assert_semantically_isolated_paper(
            paper,
            trusted_base=(
                plan.merge_base if plan is not None and not plan.new_paper else None
            ),
            allow_existing_development_dependencies=plan is None,
            module_graph_loader=module_graph_loader,
        )
        reassert()
        for command in commands[1:]:
            _run(command)
            reassert()
    diff_command = ["git", "diff", "--check"]
    if plan is not None:
        diff_command.extend([plan.merge_base, plan.head])
    diff_command.extend(
        [
            "--",
            f"papers/{paper}",
            f"papers/{paper}.lean",
            "lakefile.toml",
            # A byte-pinned canonical source artifact must be copied verbatim,
            # including the publisher's trailing whitespace.  It is an audit
            # input, not contributor-authored formatting, so diff --check
            # must not reject an otherwise valid paper release because of it.
            f":(exclude)papers/{paper}/source/",
        ]
    )
    _run(diff_command)
    reassert()


def _require_clean_worktree() -> None:
    output = _git_text("status", "--porcelain=v1", "--untracked-files=all")
    if output:
        raise ContributionError(
            "validation against a committed candidate requires a clean worktree "
            "so the checked files exactly match that candidate"
        )


def _protected_validation_input(path: str, paper: str) -> bool:
    if path in {
        ".gitmodules",
        "lake-manifest.json",
        "lakefile.toml",
        "lean-toolchain",
        "papers/audit_config.json",
        "papers/human_status.json",
        "papers/status.json",
        "pyproject.toml",
    }:
        return True
    if path.startswith(("config/", "scripts/", "skills/econcs-formalizer/")):
        return True
    if path.endswith(".lean"):
        return True
    paper_prefix = f"papers/{paper}/"
    return path.startswith(paper_prefix) and not _unsafe_public_artifact(path)


def _committed_input_snapshot(commit: str, paper: str) -> CommittedInputSnapshot:
    """Capture exact Git blobs used by a narrowed validation run."""

    commit = _commit(commit)
    object_format = _git_text("rev-parse", "--show-object-format").strip()
    if object_format not in hashlib.algorithms_available:
        raise ContributionError(
            f"unsupported Git object format for input verification: {object_format!r}"
        )
    proc = subprocess.run(
        ["git", "ls-tree", "-r", "-z", "--full-tree", commit],
        cwd=ROOT,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        detail = proc.stderr.decode("utf-8", errors="replace").strip()
        raise ContributionError(f"could not snapshot committed inputs: {detail}")
    entries: list[CommittedInput] = []
    for raw in proc.stdout.split(b"\0"):
        if not raw:
            continue
        metadata, separator, raw_path = raw.partition(b"\t")
        if not separator:
            raise ContributionError("git ls-tree returned an invalid input record")
        mode, kind, object_id = metadata.decode("ascii").split(" ", 2)
        path = raw_path.decode("utf-8", errors="strict")
        normalized = PurePosixPath(path)
        if normalized.is_absolute() or ".." in normalized.parts:
            raise ContributionError(f"unsafe committed input path: {path!r}")
        if not _protected_validation_input(path, paper):
            continue
        if kind != "blob" or mode not in {"100644", "100755", "120000"}:
            raise ContributionError(
                f"protected validation input has unsupported mode/type: {path}"
            )
        entries.append(CommittedInput(path, mode, object_id))
    return CommittedInputSnapshot(commit, object_format, tuple(entries))


def _git_object_id(data: bytes, algorithm: str) -> str:
    digest = hashlib.new(algorithm)
    digest.update(f"blob {len(data)}\0".encode("ascii"))
    digest.update(data)
    return digest.hexdigest()


def _assert_committed_inputs(snapshot: CommittedInputSnapshot) -> None:
    """Compare protected files with HEAD blobs without trusting Git's index."""

    expected_scripts: set[str] = set()
    for entry in snapshot.entries:
        path = ROOT.joinpath(*PurePosixPath(entry.path).parts)
        if entry.path.startswith("scripts/"):
            expected_scripts.add(entry.path)
        try:
            metadata = path.lstat()
        except FileNotFoundError as exc:
            raise ContributionError(
                f"validation removed committed input {entry.path}"
            ) from exc
        if entry.mode == "120000":
            if not stat.S_ISLNK(metadata.st_mode):
                raise ContributionError(
                    f"validation changed committed symlink input {entry.path}"
                )
            data = os.readlink(os.fsencode(path))
        else:
            if not stat.S_ISREG(metadata.st_mode):
                raise ContributionError(
                    f"validation changed committed file type {entry.path}"
                )
            executable = bool(metadata.st_mode & 0o111)
            if executable != (entry.mode == "100755"):
                raise ContributionError(
                    f"validation changed committed file mode {entry.path}"
                )
            data = path.read_bytes()
        if _git_object_id(data, snapshot.object_format) != entry.object_id:
            raise ContributionError(
                f"validation changed committed input bytes {entry.path}"
            )

    scripts_root = ROOT / "scripts"
    actual_scripts = {
        path.relative_to(ROOT).as_posix()
        for path in scripts_root.rglob("*")
        if (path.is_file() or path.is_symlink())
        and "__pycache__" not in path.parts
        and path.suffix not in {".pyc", ".pyo"}
    }
    unexpected = sorted(actual_scripts - expected_scripts)
    if unexpected:
        raise ContributionError(
            "validation introduced an uncommitted executable/helper input: "
            + ", ".join(unexpected[:5])
        )


def _script_tree_digest(root: Path) -> str:
    """Digest trusted helper bytes while ignoring interpreter bytecode."""

    digest = hashlib.sha256()
    for path in sorted(root.rglob("*")):
        if "__pycache__" in path.parts or path.suffix in {".pyc", ".pyo"}:
            continue
        if path.is_dir() and not path.is_symlink():
            continue
        relative = path.relative_to(root).as_posix().encode("utf-8")
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        if path.is_symlink():
            marker = b"L"
            payload = os.readlink(os.fsencode(path))
        elif path.is_file():
            marker = b"F"
            payload = path.read_bytes()
        else:
            raise ContributionError(
                f"trusted script tree contains unsupported entry {path}"
            )
        digest.update(marker)
        digest.update(len(payload).to_bytes(8, "big"))
        digest.update(payload)
    return digest.hexdigest()


def _require_committed_identity(
    expected_head: str,
    *,
    inputs: CommittedInputSnapshot | None = None,
    trusted_scripts: tuple[Path, str] | None = None,
) -> None:
    """Fail if an executed validation phase changed the candidate checkout."""

    actual_head = _commit("HEAD")
    if actual_head != expected_head:
        raise ContributionError(
            "validation changed the candidate commit identity "
            f"({expected_head} -> {actual_head})"
        )
    if inputs is not None:
        _assert_committed_inputs(inputs)
    if trusted_scripts is not None:
        script_root, expected_digest = trusted_scripts
        if _script_tree_digest(script_root) != expected_digest:
            raise ContributionError(
                "validation modified the trusted CI helper implementation"
            )
    try:
        _require_clean_worktree()
    except ContributionError as exc:
        raise ContributionError(
            "validation modified tracked or untracked repository inputs; "
            "the candidate no longer matches the committed tree"
        ) from exc


def _agent_source_audit_template(paper: str) -> str:
    return f"""# Agent Source Audit: {paper}

## Overall status: NEEDS AGENT REVIEW

Complete this after the statement map and `PaperInterface.lean` are stable,
but do not complete it during intake or the first repair-oriented adversarial
source-to-interface pass. First finish semantic judgments and compiled Lean
evidence, then run the closeout planner. Replace the status above with `PASS`
only when the planner schedules the final adversarial audit and that review is
complete.

- Reviewed final holistic audit surface identity: `<replace with planner-issued sha256>`

This must be an independent source-first review: it must not merely summarize
existing sidecars. Construct the source inventory from the source itself before
using Lean declarations as navigation, then compare the interface for
omissions, hidden strengthening/weakening, and semantic mismatches. Reread the
complete source rather than treating the frozen intake inventory as proof of
its own completeness. This final adversarial pass is separate from the earlier
source-only intake review, the first adversarial repair pass, and the item-level
machine gates. It must bind the exact source-and-Lean semantic surface reviewed.

## Source Inventory

- Source version and digest:
- Named definitions and theoretical results reviewed:
- Explicitly excluded computational or narrative material:

## Lean Interface Comparison

- Missing paper-facing statements:
- Hidden or additional Lean assumptions:
- Weakened or strengthened conclusions:
- Source proof repairs or additional regularity conditions:

## Machine Audit Results

- Focused Lean build:
- Statement, coverage, assumption, and provenance checks:
- Consolidated paper closeout:

## Findings

- Audit result:
- Remaining proof or review obligations:
"""


def _extend_scaffold_source_ignores(paper_dir: Path) -> None:
    """Keep common local source caches out of a contributor-owned branch."""

    ignore = paper_dir / ".gitignore"
    existing = ignore.read_text(encoding="utf-8") if ignore.is_file() else ""
    additions = (
        "# Local paper sources are audit inputs, not contribution outputs.\n"
        "source/\n"
        "sources/\n"
        "source_tex/\n"
        ".audit_source/\n"
        "*.7z\n"
        "*.bz2\n"
        "*.gz\n"
        "*.rar\n"
        "*.tar\n"
        "*.tar.*\n"
        "*.tgz\n"
        "*.txz\n"
        "*.xz\n"
        "*.zip\n"
    )
    if additions not in existing:
        separator = "" if not existing or existing.endswith("\n") else "\n"
        ignore.write_text(existing + separator + additions, encoding="utf-8")


def _new_paper(args: argparse.Namespace) -> None:
    paper = args.folder
    if not PAPER_ID_RE.fullmatch(paper):
        raise ContributionError(f"invalid paper id {paper!r}")
    paper_dir = PAPERS / paper
    root_module = PAPERS / f"{paper}.lean"
    if paper_dir.exists() or root_module.exists():
        raise ContributionError(
            "contributor scaffolding requires a new destination; it never merges "
            "or overwrites an existing paper"
        )

    try:
        from scripts.paper_target_registration import (
            PaperTargetRegistrationError,
            plan_paper_target_registration,
            register_paper_target,
            restore_paper_target_registration,
        )
    except ModuleNotFoundError:  # pragma: no cover - supports direct script execution.
        from paper_target_registration import (
            PaperTargetRegistrationError,
            plan_paper_target_registration,
            register_paper_target,
            restore_paper_target_registration,
        )

    try:
        registration_plan = plan_paper_target_registration(
            ROOT / "lakefile.toml", paper
        )
    except PaperTargetRegistrationError as exc:
        raise ContributionError(f"could not register paper target: {exc}") from exc
    command = [
        PYTHON,
        "scripts/new_paper.py",
        args.url,
        "--folder",
        paper,
        "--title",
        args.title,
        "--authors",
        args.authors,
        "--version",
        args.version,
    ]
    for option, value in (
        ("--official-url", args.official_url),
        ("--pdf-url", args.pdf_url),
        ("--namespace", args.namespace),
        ("--statement-spec", args.statement_spec),
    ):
        if value is not None:
            command.extend([option, str(value)])
    if args.no_download:
        command.append("--no-download")
    if args.with_notes:
        command.append("--with-notes")

    try:
        _run(command)
        _extend_scaffold_source_ignores(paper_dir)
        _run(
            [
                PYTHON,
                "scripts/sync_paper_status.py",
                "--paper",
                paper,
            ]
        )
        audit_doc = paper_dir / "docs" / "AGENT_SOURCE_AUDIT.md"
        audit_doc.write_text(_agent_source_audit_template(paper), encoding="utf-8")
        register_paper_target(ROOT / "lakefile.toml", paper)
    except BaseException as exc:
        if paper_dir.exists():
            shutil.rmtree(paper_dir)
        if root_module.exists():
            root_module.unlink()
        try:
            restore_paper_target_registration(registration_plan)
        except PaperTargetRegistrationError as rollback_exc:
            raise ContributionError(
                "paper scaffolding failed and the additive Lake registration "
                f"could not be rolled back safely: {rollback_exc}"
            ) from exc
        if isinstance(exc, PaperTargetRegistrationError):
            raise ContributionError(f"could not register paper target: {exc}") from exc
        raise
    print(f"paper contribution scaffold ready: papers/{paper}")
    print(f"next: {PYTHON} scripts/paper_contribution.py check {paper} --fast")


def _init_spec(args: argparse.Namespace) -> None:
    source = args.source.expanduser().resolve()
    if not source.is_file():
        raise ContributionError(f"source artifact does not exist: {source}")
    output = args.output.expanduser().resolve()
    if output.exists():
        raise ContributionError(f"refusing to overwrite existing file: {output}")
    try:
        relative_source = os.path.relpath(source, output.parent)
    except ValueError:
        relative_source = str(source)
    payload = {
        "schema": 1,
        "source_artifact_path": relative_source,
        "source_artifact_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "source_version": args.version,
        "targets": [
            {
                "source_item": "REPLACE WITH THEOREM LABEL",
                "source_kind": "theorem",
                "source_location": "REPLACE WITH EXACT PAGE/SECTION LOCATOR",
                "source_statement": "REPLACE WITH THE COMPLETE SOURCE STATEMENT",
                "lean_name": "replace_with_lean_name",
                "lean_type": "REPLACE WITH THE EXACT LEAN PROPOSITION",
                "kind": "theorem",
            }
        ],
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"wrote statement-spec template: {output}")
    print("replace every REPLACE field before passing it to `new --statement-spec`")


def _doctor() -> None:
    missing: list[str] = []
    print(f"required: python: {sys.version.split()[0]}")
    if sys.version_info < (3, 10):
        missing.append("Python >= 3.10")
    if problem := tomllib_dependency_problem():
        missing.append(problem)
    for command in ("git", "lake"):
        path = shutil.which(command)
        if path:
            proc = subprocess.run(
                [command, "--version"],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            if proc.returncode == 0:
                version = (proc.stdout or proc.stderr).strip().splitlines()[0]
                print(f"required: {command}: {path} ({version})")
            else:
                print(f"required command failed: {command}")
                missing.append(command)
        else:
            print(f"missing required command: {command}")
            missing.append(command)
    for command, purpose in (
        ("pdftotext", "source PDF text extraction"),
        ("latexmk", "dependency-DAG PDF rendering"),
    ):
        path = shutil.which(command)
        state = path or f"not installed (optional; used for {purpose})"
        print(f"optional: {command}: {state}")
    toolchain = ROOT / "lean-toolchain"
    if not toolchain.is_file():
        missing.append("lean-toolchain")
        print("missing required repository file: lean-toolchain")
    else:
        print(f"toolchain: {toolchain.read_text(encoding='utf-8').strip()}")
    if "lake" not in missing:
        lean = subprocess.run(
            ["lake", "env", "lean", "--version"],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        if lean.returncode == 0:
            print(f"required: lean: {lean.stdout.strip().splitlines()[0]}")
        else:
            print("required Lean environment failed to start")
            missing.append("lake env lean")
    if missing:
        raise ContributionError("missing required prerequisites: " + ", ".join(missing))


def _add_common_check_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("paper", help="citation-style paper folder id")
    parser.add_argument(
        "--base",
        help="base branch/ref; when supplied, require an exact isolated paper diff",
    )
    parser.add_argument(
        "--fast",
        action="store_true",
        help="run only the focused interface build and semantic import check",
    )
    parser.add_argument(
        "--allow-missing-source-bytes",
        action="store_true",
        help=argparse.SUPPRESS,
    )
    parser.add_argument("--repo", type=Path, help=argparse.SUPPRESS)


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    subparsers.add_parser("doctor", help="check required and optional local tools")

    spec = subparsers.add_parser(
        "init-spec", help="create a SHA-256-pinned statement-spec template"
    )
    spec.add_argument("source", type=Path, help="local source PDF/text/TeX artifact")
    spec.add_argument("--version", required=True, help="exact source version")
    spec.add_argument("--output", type=Path, required=True, help="new JSON path")

    new = subparsers.add_parser("new", help="create a contributor-safe paper scaffold")
    new.add_argument("url", help="paper URL")
    new.add_argument("--folder", required=True, help="citation-style paper id")
    new.add_argument("--title", required=True)
    new.add_argument("--authors", required=True)
    new.add_argument("--version", required=True)
    new.add_argument("--official-url")
    new.add_argument("--pdf-url")
    new.add_argument("--namespace")
    new.add_argument("--statement-spec", type=Path)
    new.add_argument("--no-download", action="store_true")
    new.add_argument("--with-notes", action="store_true")

    scope = subparsers.add_parser(
        "scope", help="classify an exact base/head contribution for CI or review"
    )
    scope.add_argument("--base", required=True)
    scope.add_argument("--head", default="HEAD")
    scope.add_argument("--github-output", type=Path)
    scope.add_argument(
        "--repo",
        type=Path,
        help=argparse.SUPPRESS,
    )

    check = subparsers.add_parser("check", help="run paper-owned validation")
    _add_common_check_arguments(check)

    prepare = subparsers.add_parser(
        "prepare-pr", help="require a clean isolated branch and run its final checks"
    )
    prepare.add_argument("paper", help="citation-style paper folder id")
    prepare.add_argument(
        "--base",
        required=True,
        help="public base branch/ref used to derive the committed PR scope",
    )
    prepare.set_defaults(fast=False, allow_missing_source_bytes=False)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        if args.command == "doctor":
            _doctor()
        elif args.command == "init-spec":
            _init_spec(args)
        elif args.command == "new":
            _new_paper(args)
        elif args.command == "scope":
            with _scope_repository(args.repo):
                plan = contribution_plan(args.base, args.head)
            print(plan.to_json(), end="")
            if args.github_output is not None:
                _write_github_output(args.github_output, plan)
            if plan.blocked:
                raise ContributionError(
                    "unsafe public contribution history: " + "; ".join(plan.reasons)
                )
        elif args.command == "check":
            with _scope_repository(args.repo):
                check_paper(
                    args.paper,
                    base=args.base,
                    fast=args.fast,
                    allow_missing_source_bytes=args.allow_missing_source_bytes,
                )
        elif args.command == "prepare-pr":
            if not args.base:
                raise ContributionError("prepare-pr requires --base <upstream/main>")
            _require_clean_worktree()
            plan = contribution_plan(args.base)
            if plan.mode != "paper" or plan.paper != args.paper:
                detail = "; ".join(plan.reasons) or f"scope is {plan.mode}"
                raise ContributionError(detail)
            payload = _paper_status(args.paper)
            if payload.get("repository_visibility") != "public":
                raise ContributionError(
                    "prepare-pr requires status.repository_visibility = `public`; "
                    "make that promotion only when the paper is approved for publication"
                )
            check_paper(
                args.paper,
                base=args.base,
                fast=False,
                allow_missing_source_bytes=False,
            )
            print("\nPull request candidate is isolated and paper checks passed.")
            print(f"Paper: {args.paper}")
            print(f"Base: {plan.merge_base}")
            print("Aggregate status/docs/site updates are deferred to a cheap follow-up.")
        else:  # pragma: no cover - argparse prevents this branch.
            raise ContributionError(f"unsupported command {args.command}")
    except ContributionError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    except subprocess.CalledProcessError as exc:
        return exc.returncode or 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
