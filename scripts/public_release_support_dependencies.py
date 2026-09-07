#!/usr/bin/env python3
"""Select status-less Lean namespaces needed by accepted public papers.

This module does not grant paper acceptance or public-release approval.  It
recognizes a narrow transport role for Lean files whose exact paths and bytes
already occur in a normal public paper's receipt-authenticated import closure.
The release guard remains responsible for ordinary public-paper status gates,
candidate-history allowlisting, private-source provenance, and final approval.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import tempfile
from typing import Iterable, Mapping

try:
    from final_closure_receipt import load_final_closure_receipt
    from obligation_closure_credential import (
        recorded_accepted_graph_lean_import_closure_sha256,
    )
    from obligation_evidence_store import load_lean_import_closure_preimage
except ModuleNotFoundError:  # pragma: no cover - module-style import.
    from scripts.final_closure_receipt import load_final_closure_receipt
    from scripts.obligation_closure_credential import (
        recorded_accepted_graph_lean_import_closure_sha256,
    )
    from scripts.obligation_evidence_store import load_lean_import_closure_preimage


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
PAPER_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]*$")
PAPERS_NON_NAMESPACE_PATHS = frozenset(
    {
        "papers/audit_config.json",
        "papers/catalog.json",
        "papers/human_status.json",
        "papers/status.json",
    }
)


@dataclass(frozen=True)
class SupportDependencySelection:
    """Exact dependency-only namespaces and paths accepted by this selector."""

    eligible_namespaces: frozenset[str]
    eligible_paths: frozenset[str]
    issues: tuple[str, ...]


@dataclass(frozen=True)
class _TreeEntry:
    mode: str
    object_type: str


@dataclass(frozen=True)
class _EntryFields:
    path: str
    kind: str
    provenance: str
    public_safety_reviewed: bool | None


def _git_bytes(repo: Path, args: list[str]) -> bytes:
    completed = subprocess.run(
        ["git", *args],
        cwd=repo,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(detail or "git command failed")
    return completed.stdout


def _candidate_tree_paths(repo: Path, candidate_ref: str) -> frozenset[str]:
    raw = _git_bytes(repo, ["ls-tree", "-r", "--name-only", "-z", candidate_ref])
    values = raw.split(b"\0")
    if values and values[-1] == b"":
        values.pop()
    return frozenset(
        value.decode("utf-8", errors="surrogateescape") for value in values
    )


def _tree_entry(repo: Path, candidate_ref: str, path: str) -> _TreeEntry | None:
    raw = _git_bytes(
        repo,
        ["ls-tree", "-z", candidate_ref, "--", f":(literal){path}"],
    )
    records = [record for record in raw.split(b"\0") if record]
    if not records:
        return None
    if len(records) != 1 or b"\t" not in records[0]:
        raise RuntimeError(f"cannot resolve one exact tree entry for {candidate_ref}:{path}")
    metadata, raw_path = records[0].split(b"\t", 1)
    if raw_path.decode("utf-8", errors="surrogateescape") != path:
        raise RuntimeError(f"Git returned an unexpected tree path for {candidate_ref}:{path}")
    fields = metadata.split()
    if len(fields) != 3:
        raise RuntimeError(f"Git returned malformed tree metadata for {candidate_ref}:{path}")
    return _TreeEntry(
        mode=fields[0].decode("ascii"),
        object_type=fields[1].decode("ascii"),
    )


def _entry_value(entry: object, field: str) -> object:
    if isinstance(entry, Mapping):
        return entry.get(field)
    return getattr(entry, field, None)


def _entry_index(entries: Iterable[object]) -> tuple[dict[str, _EntryFields], list[str]]:
    index: dict[str, _EntryFields] = {}
    issues: list[str] = []
    for entry in entries:
        raw_path = _entry_value(entry, "path")
        if not isinstance(raw_path, str) or not raw_path:
            issues.append("support dependency allowlist entry has no exact path")
            continue
        path = str(PurePosixPath(raw_path))
        if PurePosixPath(raw_path).is_absolute() or ".." in PurePosixPath(raw_path).parts:
            issues.append(f"support dependency allowlist entry has unsafe path: {raw_path!r}")
            continue
        if path in index:
            issues.append(f"support dependency allowlist path is duplicated: {path}")
            continue
        reviewed = _entry_value(entry, "public_safety_reviewed")
        index[path] = _EntryFields(
            path=path,
            kind=str(_entry_value(entry, "kind") or ""),
            provenance=str(_entry_value(entry, "provenance") or ""),
            public_safety_reviewed=(reviewed if isinstance(reviewed, bool) else None),
        )
    return index, issues


def _paper_namespace(path: str) -> str | None:
    if path in PAPERS_NON_NAMESPACE_PATHS or not path.startswith("papers/"):
        return None
    pure = PurePosixPath(path)
    if len(pure.parts) >= 3:
        paper = pure.parts[1]
    elif len(pure.parts) == 2 and pure.suffix == ".lean":
        paper = pure.stem
    else:
        return None
    if paper == "TEMPLATE" or not PAPER_RE.fullmatch(paper):
        return None
    return paper


def _candidate_json(repo: Path, candidate_ref: str, path: str) -> object:
    raw = _git_bytes(repo, ["show", f"{candidate_ref}:{path}"])
    try:
        return json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read JSON from {path}: {exc}") from exc


def _listed_paper_namespaces(
    repo: Path, candidate_ref: str, paths: frozenset[str]
) -> set[str]:
    """Keep dependency-only code out of the public paper catalog and rows."""

    listed: set[str] = set()
    for path in ("papers/status.json", "papers/human_status.json"):
        if path not in paths:
            continue
        payload = _candidate_json(repo, candidate_ref, path)
        rows = payload.get("papers", []) if isinstance(payload, Mapping) else []
        for row in rows:
            if isinstance(row, Mapping) and isinstance(row.get("id"), str):
                listed.add(row["id"])
    if "papers/catalog.json" in paths:
        catalog = _candidate_json(repo, candidate_ref, "papers/catalog.json")
        if isinstance(catalog, Mapping):
            for key in (
                "publication_overrides", "source_url_overrides", "readme_title_overrides",
                "public_summary_overrides", "preserve_partial_status",
            ):
                values = catalog.get(key, {})
                if isinstance(values, Mapping):
                    listed.update(str(name) for name in values)
                elif isinstance(values, list):
                    listed.update(value for value in values if isinstance(value, str))
    return listed


def _authenticated_public_parent_sources(
    repo: Path,
    candidate_ref: str,
    candidate_paths: frozenset[str],
) -> tuple[dict[str, set[tuple[str, str]]], list[str]]:
    """Return closure source path/SHA pairs indexed by authenticated parent."""

    public_parents: list[str] = []
    issues: list[str] = []
    for status_path in sorted(
        path
        for path in candidate_paths
        if len(PurePosixPath(path).parts) == 3
        and PurePosixPath(path).parts[0] == "papers"
        and PurePosixPath(path).parts[2] == "status.json"
    ):
        paper = PurePosixPath(status_path).parts[1]
        try:
            status = _candidate_json(repo, candidate_ref, status_path)
        except (RuntimeError, ValueError) as exc:
            issues.append(f"{status_path}: cannot inspect support parent visibility: {exc}")
            continue
        if isinstance(status, Mapping) and status.get("repository_visibility") == "public":
            public_parents.append(paper)

    sources_by_parent: dict[str, set[tuple[str, str]]] = {}
    with tempfile.TemporaryDirectory(prefix="public-support-dependencies-") as temporary:
        snapshot = Path(temporary)

        def copy_exact(path: str) -> bytes:
            if path not in candidate_paths:
                raise ValueError(
                    "authenticated support parent artifact is absent from the exact "
                    f"candidate tree: {path}"
                )
            raw = _git_bytes(repo, ["show", f"{candidate_ref}:{path}"])
            target = snapshot / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
            return raw

        for paper in sorted(public_parents):
            base = f"papers/{paper}/audit/obligation_evidence"
            pointer = f"{base}/current_accepted_graph.json"
            try:
                selection = json.loads(copy_exact(pointer))
                if not isinstance(selection, Mapping) or selection.get("schema") != 2:
                    raise ValueError("selected public graph must use the packed schema-2 pointer")
                graph_digest = selection.get("graph_sha256")
                if not isinstance(graph_digest, str) or not SHA256_RE.fullmatch(graph_digest):
                    raise ValueError("selected graph digest is malformed")
                graph_path = (
                    f"{base}/accepted_graphs/sha256/{graph_digest[:2]}/"
                    f"{graph_digest}.json"
                )
                copy_exact(graph_path)
                copy_exact(f"papers/{paper}/FINAL_CLOSURE_RECEIPT.md")
                receipt = load_final_closure_receipt(snapshot, paper)
                closure_digest = recorded_accepted_graph_lean_import_closure_sha256(
                    snapshot, paper, receipt.payload
                )
                closure_path = (
                    f"{base}/lean_import_closures/sha256/{closure_digest[:2]}/"
                    f"{closure_digest}.json"
                )
                copy_exact(closure_path)
                closure = load_lean_import_closure_preimage(
                    snapshot, paper, closure_digest
                )
                raw_sources = closure.get("sources")
                if not isinstance(raw_sources, list):
                    raise ValueError("selected Lean import closure has no source list")
                parent_sources: set[tuple[str, str]] = set()
                for source in raw_sources:
                    if not isinstance(source, Mapping):
                        raise ValueError("selected Lean import closure has a malformed source")
                    path = source.get("path")
                    digest = source.get("sha256")
                    if not isinstance(path, str) or not isinstance(digest, str):
                        raise ValueError("selected Lean import closure source identity is malformed")
                    parent_sources.add((path, digest))
            except (ValueError, RuntimeError, OSError) as exc:
                issues.append(
                    f"papers/{paper}: cannot authenticate support dependency closure: {exc}"
                )
                continue
            sources_by_parent[paper] = parent_sources
    return sources_by_parent, issues


def select_public_support_dependencies(
    candidate_repo: Path,
    candidate_ref: str,
    candidate_paths: Iterable[str],
    entries: Iterable[object],
) -> SupportDependencySelection:
    """Select exact status-less Lean dependencies of accepted public parents.

    ``candidate_paths`` must be the complete recursive path inventory for
    ``candidate_ref``.  ``entries`` may contain guard allowlist dataclasses or
    mappings with ``path``, ``kind``, and ``provenance`` fields.  A matching
    release entry for a dependency-only Lean file must use ``private_blob``;
    unchanged paths may have no release entry.  The outer guard must still
    enforce that every candidate-history change has an allowlist entry.
    """

    repo = candidate_repo.resolve()
    supplied_paths = frozenset(str(path) for path in candidate_paths)
    issues: list[str] = []
    try:
        tree_paths = _candidate_tree_paths(repo, candidate_ref)
    except RuntimeError as exc:
        return SupportDependencySelection(
            frozenset(), frozenset(), (f"cannot read exact candidate tree: {exc}",)
        )
    if supplied_paths != tree_paths:
        missing = sorted(tree_paths - supplied_paths)
        extra = sorted(supplied_paths - tree_paths)
        detail: list[str] = []
        if missing:
            detail.append("missing " + ", ".join(missing[:5]))
        if extra:
            detail.append("extra " + ", ".join(extra[:5]))
        return SupportDependencySelection(
            frozenset(),
            frozenset(),
            ("support dependency candidate path inventory is not exact: " + "; ".join(detail),),
        )

    entry_by_path, entry_issues = _entry_index(entries)
    issues.extend(entry_issues)

    namespaces: dict[str, set[str]] = {}
    root_entrypoints: set[str] = set()
    status_namespaces: set[str] = set()
    for path in sorted(tree_paths):
        namespace = _paper_namespace(path)
        if namespace is None:
            continue
        pure = PurePosixPath(path)
        if len(pure.parts) == 2 and pure.suffix == ".lean":
            root_entrypoints.add(namespace)
        elif len(pure.parts) >= 3:
            namespaces.setdefault(namespace, set()).add(path)
            if pure.parts[2:] == ("status.json",):
                status_namespaces.add(namespace)

    support_candidates = sorted(set(namespaces) - status_namespaces)
    try:
        listed_namespaces = _listed_paper_namespaces(repo, candidate_ref, tree_paths)
    except (RuntimeError, ValueError) as exc:
        return SupportDependencySelection(
            frozenset(), frozenset(), (f"cannot inspect public paper listing: {exc}",)
        )
    sources_by_parent, parent_issues = _authenticated_public_parent_sources(
        repo, candidate_ref, tree_paths
    )
    issues.extend(parent_issues)
    authenticated_sources: dict[tuple[str, str], set[str]] = {}
    for parent, sources in sources_by_parent.items():
        for identity in sources:
            authenticated_sources.setdefault(identity, set()).add(parent)

    eligible_namespaces: set[str] = set()
    eligible_paths: set[str] = set()
    for namespace in support_candidates:
        namespace_paths = namespaces[namespace]
        namespace_issues: list[str] = []
        if namespace in listed_namespaces:
            namespace_issues.append(
                f"papers/{namespace}: dependency-only namespace must not have a public paper listing"
            )
        if namespace in root_entrypoints:
            namespace_issues.append(
                f"papers/{namespace}: dependency-only namespace must not expose "
                f"papers/{namespace}.lean"
            )
        non_lean = sorted(
            path for path in namespace_paths if PurePosixPath(path).suffix != ".lean"
        )
        for path in non_lean:
            namespace_issues.append(
                f"papers/{namespace}: dependency-only namespace contains non-Lean file: {path}"
            )

        lean_paths = sorted(namespace_paths - set(non_lean))
        for path in lean_paths:
            allowlist_entry = entry_by_path.get(path)
            if allowlist_entry is not None and (
                allowlist_entry.kind != "file"
                or allowlist_entry.provenance != "private_blob"
                or allowlist_entry.public_safety_reviewed is False
            ):
                namespace_issues.append(
                    f"{path}: new dependency-only export requires a reviewed exact-file "
                    "private_blob allowlist entry"
                )
                continue
            try:
                tree_entry = _tree_entry(repo, candidate_ref, path)
                blob = _git_bytes(repo, ["show", f"{candidate_ref}:{path}"])
            except RuntimeError as exc:
                namespace_issues.append(f"{path}: cannot inspect candidate Lean file: {exc}")
                continue
            if tree_entry is None or tree_entry.object_type != "blob" or tree_entry.mode not in {
                "100644",
                "100755",
            }:
                mode = None if tree_entry is None else tree_entry.mode
                object_type = None if tree_entry is None else tree_entry.object_type
                namespace_issues.append(
                    f"{path}: dependency-only path must be a regular file blob, got "
                    f"{mode}/{object_type}"
                )
                continue
            digest = hashlib.sha256(blob).hexdigest()
            parents = authenticated_sources.get((path, digest), set())
            if not parents:
                path_only = any(
                    source_path == path
                    for source_path, _source_digest in authenticated_sources
                )
                if path_only:
                    namespace_issues.append(
                        f"{path}: candidate bytes do not match any authenticated public-parent "
                        "Lean closure source"
                    )
                else:
                    namespace_issues.append(
                        f"{path}: file is not referenced by any authenticated public-parent "
                        "Lean closure"
                    )

        if namespace_issues:
            issues.extend(namespace_issues)
            continue
        if not lean_paths:
            issues.append(f"papers/{namespace}: dependency-only namespace has no Lean files")
            continue
        eligible_namespaces.add(namespace)
        eligible_paths.update(lean_paths)

    return SupportDependencySelection(
        eligible_namespaces=frozenset(eligible_namespaces),
        eligible_paths=frozenset(eligible_paths),
        issues=tuple(issues),
    )


__all__ = ["SupportDependencySelection", "select_public_support_dependencies"]
