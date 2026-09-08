#!/usr/bin/env python3
"""Validate a clean, allowlisted public release candidate without publishing it."""

from __future__ import annotations

import argparse
from html import unescape as html_unescape
import hashlib
import json
import os
import pwd
import re
import shutil
import stat
import subprocess
import sys
import tempfile
from urllib.parse import unquote
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
try:
    from lean_import_closure import ImportClosureIssue, dependency_closure_issues
except ModuleNotFoundError:  # pragma: no cover - module-style import.
    from scripts.lean_import_closure import ImportClosureIssue, dependency_closure_issues
try:
    from tomllib_compat import tomllib
except ModuleNotFoundError:  # pragma: no cover - module-style import.
    from scripts.tomllib_compat import tomllib
try:
    from check_formalization_engine_revision import (
        EngineRevisionError,
        validate_revision_ledger,
    )
except ModuleNotFoundError:  # pragma: no cover - module-style import.
    from scripts.check_formalization_engine_revision import (
        EngineRevisionError,
        validate_revision_ledger,
    )
try:
    from strict_closeout_authority import (
        StrictCloseoutAuthorityError,
        recorded_strict_closeout_authority,
    )
except ModuleNotFoundError:  # pragma: no cover - module-style import.
    from scripts.strict_closeout_authority import (
        StrictCloseoutAuthorityError,
        recorded_strict_closeout_authority,
    )
try:
    from corrected_target_identity import (
        CORRECTED_TARGET_RECORD_SHA256_FIELD,
        CORRECTED_TARGET_REVIEW_SHA256_FIELD,
        corrected_target_review_digest,
        source_requires_approved_corrected_target,
    )
except ModuleNotFoundError:  # pragma: no cover - module-style import.
    from scripts.corrected_target_identity import (
        CORRECTED_TARGET_RECORD_SHA256_FIELD,
        CORRECTED_TARGET_REVIEW_SHA256_FIELD,
        corrected_target_review_digest,
        source_requires_approved_corrected_target,
    )
try:
    from public_release_artifact_policy import public_release_artifact_issues
except ModuleNotFoundError:  # pragma: no cover - module-style import.
    from scripts.public_release_artifact_policy import public_release_artifact_issues
try:
    from public_source_role_projection import (
        PUBLIC_SOURCE_ROLE_PROJECTION_FILE,
        PublicSourceRoleProjectionError,
        accepted_source_role_sha256s_by_source_item,
        validate_public_source_role_projection_envelope,
        validate_runtime_public_source_role_projection,
    )
except ModuleNotFoundError:  # pragma: no cover - module-style import.
    from scripts.public_source_role_projection import (
        PUBLIC_SOURCE_ROLE_PROJECTION_FILE,
        PublicSourceRoleProjectionError,
        accepted_source_role_sha256s_by_source_item,
        validate_public_source_role_projection_envelope,
        validate_runtime_public_source_role_projection,
    )
try:
    from public_release_projection import (
        PUBLIC_CONTRIBUTOR_WORKFLOW_PATHS,
        PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD,
        PUBLIC_CORRECTED_TARGET_PROJECTION_SCHEMA,
        PUBLIC_WITHHELD_APPROVAL_REFERENCE,
        PUBLIC_README_PRIVATE_WORKFLOW_GUIDANCE,
        PUBLIC_PROJECTION_GENERATOR,
        PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD,
        PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST,
        PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA,
        ProjectionError,
        project_bytes,
        public_source_excerpt_route_is_permitted,
        source_excerpt_field_is_bound,
        source_excerpt_safety_issue,
    )
except ModuleNotFoundError:  # pragma: no cover - module-style import.
    from scripts.public_release_projection import (
        PUBLIC_CONTRIBUTOR_WORKFLOW_PATHS,
        PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD,
        PUBLIC_CORRECTED_TARGET_PROJECTION_SCHEMA,
        PUBLIC_WITHHELD_APPROVAL_REFERENCE,
        PUBLIC_README_PRIVATE_WORKFLOW_GUIDANCE,
        PUBLIC_PROJECTION_GENERATOR,
        PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD,
        PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST,
        PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA,
        ProjectionError,
        project_bytes,
        public_source_excerpt_route_is_permitted,
        source_excerpt_field_is_bound,
        source_excerpt_safety_issue,
    )


ROOT = Path(__file__).resolve().parents[1]
SHA1_RE = re.compile(r"^[0-9a-f]{40}$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
PUBLIC_REMOTE = "origin"
PUBLIC_BASE_REF = "origin/main"
PUBLIC_BRANCH_PREFIX = "release/"
PRIVATE_REMOTE = "origin"
PRIVATE_BASE_REF = "origin/main"
REVIEWER_APPROVAL_PATH = (
    Path(pwd.getpwuid(os.getuid()).pw_dir)
    / ".config"
    / "econcslib"
    / "public-release-approval.json"
)
PUBLIC_REMOTE_RE = re.compile(
    r"^(?:https://github\.com/|ssh://git@github\.com/|git@github\.com:)"
    r"nikhgarg/(?:AppliedModelingLib|EconCSLib)(?:\.git)?$",
    re.IGNORECASE,
)
PRIVATE_REMOTE_RE = re.compile(
    r"^(?:https://github\.com/|ssh://git@github\.com/|git@github\.com:)"
    r"nikhgarg/EconCSLib-private(?:\.git)?$",
    re.IGNORECASE,
)
FORBIDDEN_PUBLIC_PATH_RE = re.compile(
    r"(?:^|/)(?:\.review_traces|\.audit_source|source|sources|source_tex)(?:/|$)|"
    r"(?:^|/)(?:source(?:[._-][^/]*)?\.(?:txt|pdf|tex|tar|tgz|zip|gz)|"
    r"arxiv_source\.(?:tar|tgz|zip|gz))$|"
    r"\.(?:zip|tar|tgz|gz|bz2|xz|7z|rar)$|"
    r"(?:^|/)(?:PRIVATE_[^/]*|[^/]*_HANDOFF_[^/]*)$",
    re.IGNORECASE,
)
# These exact public workflow tools contain ``private`` in their established
# filenames.  They remain subject to ordinary byte provenance and content
# checks; this exception applies only to the filename-level artifact filter.
PUBLIC_PRIVATE_NAMED_WORKFLOW_PATHS = frozenset(
    {
        "docs/PRIVATE_DEVELOPMENT_WORKFLOW.md",
        "scripts/private_paper_checkpoint.py",
        "site/private_preview_server.py",
    }
)
GENERATED_PUBLIC_STATUS_PATHS = frozenset(
    {
        "papers/status.json",
        "papers/human_status.json",
        "docs/PAPER_STATUS.md",
        "site/index.html",
    }
)
PUBLIC_STATUS_GENERATOR = "python3 scripts/sync_paper_status.py"
PUBLIC_SOURCE_DISPLAY_PROJECTION_GENERATOR = (
    "python3 scripts/public_source_display_projection.py"
)
PUBLIC_SOURCE_DISPLAY_PROJECTION_MATERIAL = (
    "selected_byte_pinned_source_anchor_quotes"
)
SESSION_INSIGHTS_PREFIX = "skills/econcs-session-insights/"
# The public entrypoint explains the general maintenance workflow. Concrete
# wiki evidence and feedback ledgers remain private, including inherited files.
PUBLIC_SESSION_INSIGHTS_PATHS = frozenset(
    {
        "skills/econcs-session-insights/SKILL.md",
    }
)
# The projector owns the exact reviewed contributor-document set. Sharing it
# prevents a new public stage guide from being preserved by projection but
# rejected by the candidate check under an older duplicate list.
# The landing page may give this one concrete, contributor-facing recommendation
# without exposing a private checkout, source cache, or session archive.  This
# is deliberately an exact path-and-text exception, not a site-wide exemption.
PUBLIC_SITE_PRIVATE_WORKFLOW_GUIDANCE = (
    "New paper formalizations should start in a private workflow and be\n"
    "            proposed to enter the library through a pull request when ready."
)
PUBLIC_SITE_PRIVATE_WORKFLOW_SENTINEL = "__APPROVED_PUBLIC_WORKFLOW_GUIDANCE__"
# The rendered overview is the PDF form of the explicitly approved contributor
# workflow guide.  It may use the same private-draft terminology as its TeX
# source, but still undergoes every source-artifact, local-path, and URL check.
PUBLIC_CONTRIBUTOR_WORKFLOW_PDF_PATHS = frozenset(
    {"docs/FORMALIZATION_AUDIT_PROCEDURE_OVERVIEW.pdf"}
)
PUBLICATION_LOCATOR = "cited publication"
TRUSTED_STATUS_SYNC = Path(__file__).resolve().with_name("sync_paper_status.py")
SOURCE_TEXT_COMPANION_PATH_FIELDS = frozenset(
    {
        "canonical_text",
        "visual_primary_scan",
        "transcript_input_scan",
        "semantic_review_transcription",
    }
)
PAPERS_NON_NAMESPACE_PATHS = frozenset(
    {
        "papers/audit_config.json",
        "papers/catalog.json",
        "papers/human_status.json",
        "papers/status.json",
    }
)


@dataclass(frozen=True)
class AllowlistEntry:
    path: str
    kind: str
    provenance: str
    source_commit: str | None
    reason: str
    generator: str | None
    public_base_blob_sha256: str | None = None
    candidate_blob_sha256: str | None = None
    private_source_blob_sha256: str | None = None


@dataclass(frozen=True)
class CandidateChange:
    status: str
    path: str


@dataclass(frozen=True)
class CandidateCommit:
    commit: str
    parent: str
    changes: tuple[CandidateChange, ...]


@dataclass(frozen=True)
class GitTreeEntry:
    mode: str
    object_type: str
    object_id: str


@dataclass(frozen=True)
class ReleaseApproval:
    candidate_commit: str
    public_base_commit: str
    allowlist_sha256: str
    guard_sha256: str
    trusted_tooling_sha256: str
    private_source_commits: tuple[str, ...]


def _git_environment() -> dict[str, str]:
    environment = os.environ.copy()
    for key in list(environment):
        if key.startswith("GIT_CONFIG_") or key in {
            "GIT_ALTERNATE_OBJECT_DIRECTORIES",
            "GIT_COMMON_DIR",
            "GIT_DIR",
            "GIT_INDEX_FILE",
            "GIT_NAMESPACE",
            "GIT_OBJECT_DIRECTORY",
            "GIT_WORK_TREE",
        }:
            environment.pop(key, None)
    environment["GIT_NO_REPLACE_OBJECTS"] = "1"
    return environment


def _git(repo: Path, args: list[str], *, check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=repo,
        env=_git_environment(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if check and result.returncode != 0:
        raise RuntimeError(
            f"git {' '.join(args)} failed: {result.stderr.strip() or result.stdout.strip()}"
        )
    return result.stdout


def _git_bytes(repo: Path, args: list[str]) -> bytes:
    result = subprocess.run(
        ["git", *args],
        cwd=repo,
        env=_git_environment(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"git {' '.join(args)} failed: "
            + result.stderr.decode("utf-8", errors="replace").strip()
        )
    return result.stdout


def is_git_repository(path: Path) -> bool:
    """Return whether ``path`` names a usable Git repository/worktree."""

    if not path.is_dir():
        return False
    result = subprocess.run(
        ["git", "rev-parse", "--git-dir"],
        cwd=path,
        env=_git_environment(),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return result.returncode == 0


def resolved_commit(repo: Path, ref: str) -> str:
    return _git(repo, ["rev-parse", "--verify", f"{ref}^{{commit}}"]).strip()


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _guard_sha256() -> str:
    return _sha256_bytes(Path(__file__).resolve().read_bytes())


def _trusted_tooling_sha256(scripts_dir: Path | None = None) -> str:
    """Digest every private production helper that release validation may load.

    The release guard imports and executes helpers from its sibling ``scripts``
    directory.  Pinning only this file would leave those transitive authorities
    mutable after review.  Hash the complete production-tooling directory,
    excluding tests and interpreter caches, so newly introduced local helpers
    are covered without maintaining a fragile hand-written import list.
    """

    scripts_dir = (
        Path(__file__).resolve().parent
        if scripts_dir is None
        else scripts_dir.resolve()
    )
    root = scripts_dir.parent
    records: list[dict[str, object]] = []
    for path in sorted(scripts_dir.rglob("*"), key=lambda item: item.as_posix()):
        relative_to_scripts = path.relative_to(scripts_dir)
        if any(part in {"__pycache__", "tests"} for part in relative_to_scripts.parts):
            continue
        try:
            metadata = path.lstat()
        except OSError as exc:
            raise RuntimeError(f"cannot inspect trusted tooling path {path}: {exc}") from exc
        if stat.S_ISDIR(metadata.st_mode):
            continue
        if not stat.S_ISREG(metadata.st_mode) or path.is_symlink():
            raise RuntimeError(
                f"trusted tooling contains a non-regular path: {path.relative_to(root)}"
            )
        if path.suffix in {".pyc", ".pyo"}:
            continue
        try:
            payload = path.read_bytes()
        except OSError as exc:
            raise RuntimeError(f"cannot read trusted tooling path {path}: {exc}") from exc
        records.append(
            {
                "path": path.relative_to(root).as_posix(),
                "executable": bool(metadata.st_mode & 0o111),
                "byte_length": len(payload),
                "sha256": _sha256_bytes(payload),
            }
        )
    if not records:
        raise RuntimeError("trusted release-tooling bundle is empty")
    encoded = json.dumps(
        {
            "schema": "econcslib.public-release-trusted-tooling/v1",
            "files": records,
        },
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("utf-8")
    return _sha256_bytes(encoded)


def _path_is_within(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
    except ValueError:
        return False
    return True


def load_release_approval(path: Path) -> ReleaseApproval:
    """Load one fixed-path, reviewer-owned approval without following symlinks."""

    try:
        parent_metadata = path.parent.lstat()
    except OSError as exc:
        raise ValueError(f"cannot inspect reviewer approval directory {path.parent}: {exc}") from exc
    if (
        path.parent.is_symlink()
        or not stat.S_ISDIR(parent_metadata.st_mode)
        or parent_metadata.st_uid != os.getuid()
        or parent_metadata.st_mode & (stat.S_IWGRP | stat.S_IWOTH)
    ):
        raise ValueError(
            "reviewer approval directory must be reviewer-owned, non-symlink, and "
            f"not group/world writable: {path.parent}"
        )
    try:
        descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    except OSError as exc:
        raise ValueError(f"cannot read reviewer approval {path}: {exc}") from exc
    try:
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_uid != os.getuid()
            or metadata.st_mode & (stat.S_IWGRP | stat.S_IWOTH)
        ):
            raise ValueError(
                "reviewer approval must be one reviewer-owned regular file that is "
                f"not group/world writable: {path}"
            )
        with os.fdopen(descriptor, "r", encoding="utf-8") as handle:
            descriptor = -1
            payload = json.load(handle)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read reviewer approval {path}: {exc}") from exc
    finally:
        if descriptor >= 0:
            os.close(descriptor)
    required_fields = {
        "schema",
        "candidate_commit",
        "public_base_commit",
        "allowlist_sha256",
        "guard_sha256",
        "trusted_tooling_sha256",
        "private_source_commits",
    }
    if not isinstance(payload, dict) or set(payload) != required_fields:
        raise ValueError(
            "reviewer approval must be a schema-2 object with exactly: "
            + ", ".join(sorted(required_fields))
        )
    if payload.get("schema") != 2:
        raise ValueError("reviewer approval must use schema 2")
    candidate_commit = str(payload.get("candidate_commit") or "").strip().lower()
    public_base_commit = str(payload.get("public_base_commit") or "").strip().lower()
    allowlist_sha256 = str(payload.get("allowlist_sha256") or "").strip().lower()
    guard_sha256 = str(payload.get("guard_sha256") or "").strip().lower()
    trusted_tooling_sha256 = (
        str(payload.get("trusted_tooling_sha256") or "").strip().lower()
    )
    raw_source_commits = payload.get("private_source_commits")
    if not SHA1_RE.fullmatch(candidate_commit):
        raise ValueError("reviewer approval candidate_commit must be 40 lowercase hex")
    if not SHA1_RE.fullmatch(public_base_commit):
        raise ValueError("reviewer approval public_base_commit must be 40 lowercase hex")
    if not SHA256_RE.fullmatch(allowlist_sha256):
        raise ValueError("reviewer approval allowlist_sha256 must be 64 lowercase hex")
    if not SHA256_RE.fullmatch(guard_sha256):
        raise ValueError("reviewer approval guard_sha256 must be 64 lowercase hex")
    if not SHA256_RE.fullmatch(trusted_tooling_sha256):
        raise ValueError(
            "reviewer approval trusted_tooling_sha256 must be 64 lowercase hex"
        )
    if not isinstance(raw_source_commits, list):
        raise ValueError("reviewer approval private_source_commits must be a list")
    source_commits = tuple(
        str(commit).strip().lower() for commit in raw_source_commits
    )
    if any(not SHA1_RE.fullmatch(commit) for commit in source_commits):
        raise ValueError(
            "reviewer approval private_source_commits entries must be 40 lowercase hex"
        )
    if tuple(sorted(set(source_commits))) != source_commits:
        raise ValueError(
            "reviewer approval private_source_commits must be sorted and duplicate-free"
        )
    return ReleaseApproval(
        candidate_commit=candidate_commit,
        public_base_commit=public_base_commit,
        allowlist_sha256=allowlist_sha256,
        guard_sha256=guard_sha256,
        trusted_tooling_sha256=trusted_tooling_sha256,
        private_source_commits=source_commits,
    )


def canonical_remote_issues(
    repo: Path,
    *,
    remote: str,
    expected: re.Pattern[str],
    label: str,
) -> list[str]:
    """Require one canonical URL for both fetch and every push operation."""

    issues: list[str] = []
    fetch_urls = [
        value.strip()
        for value in _git(
            repo, ["remote", "get-url", "--all", remote], check=False
        ).splitlines()
        if value.strip()
    ]
    push_urls = [
        value.strip()
        for value in _git(
            repo, ["remote", "get-url", "--push", "--all", remote], check=False
        ).splitlines()
        if value.strip()
    ]
    for direction, urls in (("fetch", fetch_urls), ("push", push_urls)):
        if len(urls) != 1 or expected.fullmatch(urls[0]) is None:
            issues.append(
                f"{label} remote {remote!r} must have exactly one canonical {direction} "
                f"URL; got {urls!r}"
            )
    return issues


def _git_storage_path(repo: Path, arguments: list[str]) -> Path:
    return Path(
        _git(
            repo,
            ["rev-parse", "--path-format=absolute", *arguments],
        ).strip()
    ).resolve()


def shared_git_storage_issues(candidate_repo: Path, private_repo: Path) -> list[str]:
    """Reject worktrees or repositories that expose the same Git object store."""

    issues: list[str] = []
    for arguments, label in (
        (["--git-common-dir"], "Git common directory"),
        (["--git-path", "objects"], "Git object directory"),
    ):
        candidate_path = _git_storage_path(candidate_repo, arguments)
        private_path = _git_storage_path(private_repo, arguments)
        if candidate_path == private_path:
            issues.append(
                f"public candidate and private repository share the same {label}: "
                f"{candidate_path}"
            )
    candidate_objects = _git_storage_path(
        candidate_repo, ["--git-path", "objects"]
    )
    alternates = candidate_objects / "info" / "alternates"
    if alternates.exists():
        try:
            configured = [
                line.strip()
                for line in alternates.read_text(encoding="utf-8").splitlines()
                if line.strip()
            ]
        except (OSError, UnicodeDecodeError) as exc:
            issues.append(f"cannot inspect public candidate object alternates: {exc}")
        else:
            if configured:
                issues.append(
                    "public candidate must use a standalone Git object database; "
                    f"found alternates in {alternates}"
                )
    return issues


def _tree_entry(repo: Path, ref: str, path: str) -> GitTreeEntry | None:
    """Read one exact tree entry without treating ``path`` as a pathspec."""

    raw = _git_bytes(repo, ["ls-tree", "-z", ref, "--", f":(literal){path}"])
    records = [record for record in raw.split(b"\0") if record]
    if not records:
        return None
    if len(records) != 1 or b"\t" not in records[0]:
        raise RuntimeError(f"cannot resolve one exact tree entry for {ref}:{path}")
    metadata, raw_path = records[0].split(b"\t", 1)
    if raw_path.decode("utf-8", errors="surrogateescape") != path:
        raise RuntimeError(f"Git returned an unexpected tree path for {ref}:{path}")
    fields = metadata.split()
    if len(fields) != 3:
        raise RuntimeError(f"Git returned malformed tree metadata for {ref}:{path}")
    return GitTreeEntry(
        mode=fields[0].decode("ascii"),
        object_type=fields[1].decode("ascii"),
        object_id=fields[2].decode("ascii"),
    )


def _safe_relative_path(value: object) -> str | None:
    if not isinstance(value, str) or not value.strip():
        return None
    path = PurePosixPath(value.strip())
    if path.is_absolute() or ".." in path.parts or str(path) in {"", "."}:
        return None
    return str(path)


def load_allowlist(path: Path) -> list[AllowlistEntry]:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise ValueError(f"cannot read public export allowlist {path}: {exc}") from exc
    return parse_allowlist(raw, source=str(path))


def parse_allowlist(raw: bytes, *, source: str) -> list[AllowlistEntry]:
    try:
        payload = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read public export allowlist {source}: {exc}") from exc
    if not isinstance(payload, dict) or payload.get("schema") != 1:
        raise ValueError("public export allowlist must be a schema-1 object")
    raw_entries = payload.get("entries")
    if not isinstance(raw_entries, list) or not raw_entries:
        raise ValueError("public export allowlist entries must be a nonempty list")
    entries: list[AllowlistEntry] = []
    seen: set[str] = set()
    for index, raw in enumerate(raw_entries):
        if not isinstance(raw, dict):
            raise ValueError(f"allowlist entry {index} must be an object")
        candidate = _safe_relative_path(raw.get("path"))
        kind = raw.get("kind")
        provenance = str(raw.get("provenance") or "").strip()
        raw_source_commit = raw.get("source_commit")
        source_commit = (
            str(raw_source_commit).strip().lower()
            if raw_source_commit is not None
            else None
        )
        reason = str(raw.get("reason") or "").strip()
        raw_generator = raw.get("generator")
        generator = str(raw_generator).strip() if raw_generator is not None else None
        raw_public_base_blob_sha256 = raw.get("public_base_blob_sha256")
        public_base_blob_sha256 = (
            str(raw_public_base_blob_sha256).strip().lower()
            if raw_public_base_blob_sha256 is not None
            else None
        )
        raw_private_source_blob_sha256 = raw.get("private_source_blob_sha256")
        private_source_blob_sha256 = (
            str(raw_private_source_blob_sha256).strip().lower()
            if raw_private_source_blob_sha256 is not None
            else None
        )
        raw_candidate_blob_sha256 = raw.get("candidate_blob_sha256")
        candidate_blob_sha256 = (
            str(raw_candidate_blob_sha256).strip().lower()
            if raw_candidate_blob_sha256 is not None
            else None
        )
        if candidate is None:
            raise ValueError(f"allowlist entry {index} has an unsafe path")
        if candidate in seen:
            raise ValueError(f"allowlist path is duplicated: {candidate}")
        if kind != "file":
            raise ValueError(
                f"allowlist entry {candidate} kind must be file; directory entries "
                "cannot authorize an unreviewed descendant"
            )
        if provenance not in {
            "private_blob",
            "private_projection",
            "public_generated",
            "public_base_deletion",
            "public_base_edit",
            "public_base_addition",
        }:
            raise ValueError(
                f"allowlist entry {candidate} provenance must be private_blob, "
                "private_projection, public_generated, public_base_deletion, public_base_edit, or "
                "public_base_addition"
            )
        if provenance == "private_blob":
            if source_commit is None or not SHA1_RE.fullmatch(source_commit):
                raise ValueError(
                    f"allowlist entry {candidate} needs a 40-hex source_commit"
                )
            if generator is not None:
                raise ValueError(
                    f"private_blob allowlist entry {candidate} cannot declare a generator"
                )
            if (
                public_base_blob_sha256 is not None
                or private_source_blob_sha256 is not None
                or candidate_blob_sha256 is not None
            ):
                raise ValueError(
                    f"private_blob allowlist entry {candidate} cannot declare "
                    "public-base edit digests"
                )
        elif provenance == "private_projection":
            if source_commit is None or not SHA1_RE.fullmatch(source_commit):
                raise ValueError(
                    f"private_projection entry {candidate} needs a 40-hex source_commit"
                )
            if generator != PUBLIC_PROJECTION_GENERATOR:
                raise ValueError(
                    f"private_projection entry {candidate} must declare generator "
                    f"{PUBLIC_PROJECTION_GENERATOR!r}"
                )
            if public_base_blob_sha256 is not None:
                raise ValueError(
                    f"private_projection entry {candidate} cannot declare a "
                    "public_base_blob_sha256"
                )
            if not SHA256_RE.fullmatch(private_source_blob_sha256 or ""):
                raise ValueError(
                    f"private_projection entry {candidate} needs a 64-hex "
                    "private_source_blob_sha256"
                )
            if not SHA256_RE.fullmatch(candidate_blob_sha256 or ""):
                raise ValueError(
                    f"private_projection entry {candidate} needs a 64-hex "
                    "candidate_blob_sha256"
                )
            if private_source_blob_sha256 == candidate_blob_sha256:
                raise ValueError(
                    f"private_projection entry {candidate} must pin distinct private "
                    "source and candidate blob digests"
                )
        elif provenance == "public_generated":
            if kind != "file" or candidate not in GENERATED_PUBLIC_STATUS_PATHS:
                raise ValueError(
                    f"public_generated entry {candidate} must be one exact generated status path"
                )
            if source_commit is not None:
                raise ValueError(
                    f"public_generated entry {candidate} must not claim a source_commit"
                )
            if generator != PUBLIC_STATUS_GENERATOR:
                raise ValueError(
                    f"public_generated entry {candidate} must declare generator "
                    f"{PUBLIC_STATUS_GENERATOR!r}"
                )
            if (
                public_base_blob_sha256 is not None
                or private_source_blob_sha256 is not None
                or candidate_blob_sha256 is not None
            ):
                raise ValueError(
                    f"public_generated entry {candidate} cannot declare "
                    "public-base edit digests"
                )
        elif provenance == "public_base_deletion":
            if (
                source_commit is not None
                or generator is not None
                or private_source_blob_sha256 is not None
            ):
                raise ValueError(
                    f"public_base_deletion entry {candidate} cannot declare source_commit or generator"
                )
            if (
                public_base_blob_sha256 is not None
                or private_source_blob_sha256 is not None
                or candidate_blob_sha256 is not None
            ):
                raise ValueError(
                    f"public_base_deletion entry {candidate} cannot declare "
                    "public-base edit digests"
                )
        elif provenance == "public_base_edit":
            if (
                source_commit is not None
                or generator is not None
                or private_source_blob_sha256 is not None
            ):
                raise ValueError(
                    f"public_base_edit entry {candidate} cannot declare source_commit or generator"
                )
            if not SHA256_RE.fullmatch(public_base_blob_sha256 or ""):
                raise ValueError(
                    f"public_base_edit entry {candidate} needs a 64-hex "
                    "public_base_blob_sha256"
                )
            if not SHA256_RE.fullmatch(candidate_blob_sha256 or ""):
                raise ValueError(
                    f"public_base_edit entry {candidate} needs a 64-hex "
                    "candidate_blob_sha256"
                )
            if public_base_blob_sha256 == candidate_blob_sha256:
                raise ValueError(
                    f"public_base_edit entry {candidate} must pin distinct base and "
                    "candidate blob digests"
                )
        else:
            if (
                source_commit is not None
                or generator is not None
                or private_source_blob_sha256 is not None
            ):
                raise ValueError(
                    f"public_base_addition entry {candidate} cannot declare "
                    "source_commit or generator"
                )
            if public_base_blob_sha256 is not None:
                raise ValueError(
                    f"public_base_addition entry {candidate} cannot declare a "
                    "public_base_blob_sha256"
                )
            if not SHA256_RE.fullmatch(candidate_blob_sha256 or ""):
                raise ValueError(
                    f"public_base_addition entry {candidate} needs a 64-hex "
                    "candidate_blob_sha256"
                )
        if not reason:
            raise ValueError(f"allowlist entry {candidate} needs a review reason")
        if raw.get("public_safety_reviewed") is not True:
            raise ValueError(
                f"allowlist entry {candidate} must set public_safety_reviewed=true"
            )
        seen.add(candidate)
        entries.append(
            AllowlistEntry(
                candidate,
                str(kind),
                provenance,
                source_commit,
                reason,
                generator,
                public_base_blob_sha256,
                candidate_blob_sha256,
                private_source_blob_sha256,
            )
        )
    return entries


def path_is_allowlisted(path: str, entries: list[AllowlistEntry]) -> bool:
    return matching_allowlist_entry(path, entries) is not None


def matching_allowlist_entry(
    path: str, entries: list[AllowlistEntry]
) -> AllowlistEntry | None:
    return next((entry for entry in entries if path == entry.path), None)


def unused_allowlist_issues(
    entries: list[AllowlistEntry], used_entries: set[AllowlistEntry]
) -> list[str]:
    return [
        f"allowlist entry is unused by candidate history: {entry.path}"
        for entry in entries
        if entry not in used_entries
    ]


def status_visibility_issues(
    repo: Path,
    candidate_ref: str = "HEAD",
    *,
    entries: list[AllowlistEntry] | None = None,
) -> list[str]:
    """Require public visibility and terminal artifacts for each paper namespace.

    Credential contents are checked by the existing accepted-graph transport
    validator. This presence check prevents an absent pointer from skipping
    that validation, including for a disclosed partial formalization.
    """

    paths = set(_git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines())
    paper_names: set[str] = set()
    status_paths: dict[str, str] = {}
    for path in paths:
        if path in PAPERS_NON_NAMESPACE_PATHS or not path.startswith("papers/"):
            continue
        pure = PurePosixPath(path)
        if len(pure.parts) >= 3:
            paper_name = pure.parts[1]
        elif len(pure.parts) == 2 and pure.suffix == ".lean":
            paper_name = pure.stem
        else:
            continue
        if paper_name == "TEMPLATE":
            continue
        paper_names.add(paper_name)
        expected_status = f"papers/{paper_name}/status.json"
        if path == expected_status:
            status_paths[paper_name] = path

    issues: list[str] = []
    support_namespaces: frozenset[str] = frozenset()
    if entries is not None and paper_names - set(status_paths):
        try:
            from public_release_support_dependencies import select_public_support_dependencies
        except ModuleNotFoundError:  # Module-style import.
            from scripts.public_release_support_dependencies import select_public_support_dependencies
        support = select_public_support_dependencies(repo, candidate_ref, paths, entries)
        issues.extend(support.issues)
        support_namespaces = support.eligible_namespaces
    for paper_name in sorted(paper_names):
        if paper_name in support_namespaces:
            continue
        path = status_paths.get(paper_name)
        if path is None:
            issues.append(
                f"papers/{paper_name}: public candidate paper namespace requires "
                f"papers/{paper_name}/status.json with repository_visibility=`public`"
            )
            continue
        try:
            payload = json.loads(_git(repo, ["show", f"{candidate_ref}:{path}"]))
        except (RuntimeError, json.JSONDecodeError) as exc:
            issues.append(f"{path}: cannot read candidate status: {exc}")
            continue
        visibility = payload.get("repository_visibility") if isinstance(payload, dict) else None
        if visibility != "public":
            issues.append(
                f"{path}: public candidate requires repository_visibility=`public`, "
                f"got {visibility!r}"
            )
            continue
        for artifact in (
            "audit/obligation_evidence/current_accepted_graph.json",
            "FINAL_CLOSURE_RECEIPT.md",
        ):
            expected = f"papers/{paper_name}/{artifact}"
            if expected not in paths:
                issues.append(
                    f"papers/{paper_name}: public paper is missing terminal "
                    f"credential artifact `{expected}`"
                )
    return issues


def changed_formalized_packet_issues(
    repo: Path,
    candidate_ref: str,
    *,
    public_base_ref: str,
) -> list[str]:
    """Require a durable review packet for each newly released final paper.

    This applies when a public completed paper is added or its status record is
    changed in the candidate.  It deliberately does not retroactively reject
    older public papers while their packets are being migrated.  The packet is
    a reviewer aid (not a human-signoff substitute), but its committed PDF and
    TeX ensure a public release exposes the same source/Lean review surface as
    the local dashboard.
    """

    changed = set(
        _git(repo, ["diff", "--name-only", public_base_ref, candidate_ref]).splitlines()
    )
    candidate_paths = set(
        _git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
    )
    issues: list[str] = []
    for status_path in sorted(
        path
        for path in changed
        if re.fullmatch(r"papers/[^/]+/status\.json", path)
    ):
        # A reviewed candidate may delete a paper that existed on the public
        # base. Deletion authorization is checked by the ordinary exact-path
        # allowlist and namespace gates; there is no candidate status or packet
        # to validate after the deletion.
        if status_path not in candidate_paths:
            continue
        try:
            payload = json.loads(_git(repo, ["show", f"{candidate_ref}:{status_path}"]))
        except (RuntimeError, json.JSONDecodeError) as exc:
            issues.append(f"{status_path}: cannot read candidate status: {exc}")
            continue
        if not isinstance(payload, dict):
            issues.append(f"{status_path}: candidate status must be a JSON object")
            continue
        if payload.get("repository_visibility") != "public" or str(
            payload.get("status") or ""
        ).strip().lower() not in {"formalized", "formalized with caveat"}:
            continue
        paper = PurePosixPath(status_path).parts[1]
        pdf_path = f"papers/{paper}/docs/HUMAN_REVIEW_PACKET.pdf"
        tex_path = f"papers/{paper}/docs/HUMAN_REVIEW_PACKET.tex"
        readme_path = f"papers/{paper}/README.md"
        artifacts = payload.get("artifacts")
        if not isinstance(artifacts, dict):
            issues.append(f"{status_path}: public finalized paper needs an artifacts object with human review packet paths")
            continue
        if artifacts.get("human_review_packet_pdf") != pdf_path:
            issues.append(f"{status_path}: artifacts.human_review_packet_pdf must be `{pdf_path}`")
        if artifacts.get("human_review_packet_tex") != tex_path:
            issues.append(f"{status_path}: artifacts.human_review_packet_tex must be `{tex_path}`")
        for path in (pdf_path, tex_path):
            if path not in candidate_paths:
                issues.append(f"{status_path}: public finalized paper is missing `{path}`")
        if readme_path not in candidate_paths:
            issues.append(f"{status_path}: public finalized paper is missing `{readme_path}`")
            continue
        try:
            readme = _git(repo, ["show", f"{candidate_ref}:{readme_path}"])
        except RuntimeError as exc:
            issues.append(f"{readme_path}: cannot read candidate README: {exc}")
            continue
        expected_link = "Human review packet: [HUMAN_REVIEW_PACKET.pdf](docs/HUMAN_REVIEW_PACKET.pdf)"
        if expected_link not in readme:
            issues.append(f"{readme_path}: public finalized paper must link its human review packet")
    return issues


def _paper_local_candidate_path(
    *, paper_dir: PurePosixPath, raw_path: object
) -> str | None:
    """Resolve the source-map path convention without touching the worktree."""

    if not isinstance(raw_path, str) or not raw_path.strip():
        return None
    raw = raw_path.strip()
    candidate = PurePosixPath(raw)
    if candidate.is_absolute() or ".." in candidate.parts:
        return None
    resolved = candidate if candidate.parts[:1] == ("papers",) else paper_dir / candidate
    try:
        resolved.relative_to(paper_dir)
    except ValueError:
        return None
    return str(resolved)


def _artifact_present(candidate_paths: set[str], artifact_path: str) -> bool:
    prefix = artifact_path.rstrip("/") + "/"
    return artifact_path in candidate_paths or any(
        path.startswith(prefix) for path in candidate_paths
    )


def public_arxiv_tex_artifact_paths(
    repo: Path, candidate_ref: str = "HEAD"
) -> tuple[set[str], list[str]]:
    """Return candidate TeX files eligible for the official-arXiv exception.

    Only a canonical source-map artifact is eligible, and only when the exact
    candidate blob equals its recorded SHA-256.  Source archives, PDFs, OCR
    text, companion scans, and arbitrary item-level paths remain private.
    """

    candidate_paths = set(
        _git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
    )
    map_paths = sorted(
        path
        for path in candidate_paths
        if path.startswith("papers/")
        and path.endswith("/audit/paper_statement_map.json")
    )
    approved: set[str] = set()
    issues: list[str] = []
    for map_path in map_paths:
        paper_dir = PurePosixPath(map_path).parents[1]
        try:
            payload = json.loads(_git(repo, ["show", f"{candidate_ref}:{map_path}"]))
        except (RuntimeError, json.JSONDecodeError) as exc:
            issues.append(f"{map_path}: cannot inspect official arXiv source exception: {exc}")
            continue
        if not isinstance(payload, dict):
            continue
        source_url = str(payload.get("source_url") or "").strip().lower()
        raw_path = payload.get("source_artifact_path")
        expected_sha256 = str(payload.get("source_artifact_sha256") or "").strip().lower()
        artifact = _paper_local_candidate_path(paper_dir=paper_dir, raw_path=raw_path)
        # A release-projected map intentionally omits the private source-file
        # path. A single checked-in ``source/*.tex`` file remains eligible as
        # official arXiv source when its bytes match the retained map digest.
        # A directory or an ambiguous collection never inherits this exception.
        if artifact is None:
            candidates = sorted(
                path
                for path in candidate_paths
                if PurePosixPath(path).parent == paper_dir / "source"
                and PurePosixPath(path).suffix.lower() == ".tex"
            )
            if len(candidates) == 1:
                artifact = candidates[0]
        if artifact not in candidate_paths:
            continue
        if not re.match(r"https?://(?:export\.)?arxiv\.org/(?:abs|e-print)/", source_url):
            continue
        if artifact is None or PurePosixPath(artifact).suffix.lower() != ".tex":
            continue
        if not SHA256_RE.fullmatch(expected_sha256):
            issues.append(
                f"{map_path}: public official-arXiv TeX artifact has no valid source-artifact SHA-256"
            )
            continue
        actual_sha256 = hashlib.sha256(
            _git_bytes(repo, ["show", f"{candidate_ref}:{artifact}"])
        ).hexdigest()
        if actual_sha256 != expected_sha256:
            issues.append(
                f"{map_path}: public official-arXiv TeX artifact does not match its source-map SHA-256"
            )
            continue
        approved.add(artifact)
    return approved, issues


def source_artifact_leakage_issues(
    repo: Path, candidate_ref: str = "HEAD"
) -> list[str]:
    """Reject source bytes declared by candidate source maps and companions."""

    candidate_paths = set(
        _git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
    )
    map_paths = sorted(
        path
        for path in candidate_paths
        if path.startswith("papers/")
        and path.endswith("/audit/paper_statement_map.json")
    )
    approved_arxiv_tex, approved_issues = public_arxiv_tex_artifact_paths(
        repo, candidate_ref
    )
    issues: list[str] = list(approved_issues)
    for map_path in map_paths:
        paper_dir = PurePosixPath(map_path).parents[1]
        try:
            payload = json.loads(_git(repo, ["show", f"{candidate_ref}:{map_path}"]))
        except (RuntimeError, json.JSONDecodeError) as exc:
            issues.append(f"{map_path}: cannot inspect declared source artifacts: {exc}")
            continue
        if not isinstance(payload, dict):
            issues.append(f"{map_path}: source map must be a JSON object")
            continue
        descriptors: list[tuple[str, object]] = []

        def collect_item_source_paths(value: object, location: str = "$") -> None:
            """Collect schema-declared source-byte paths without guessing by filename."""

            if isinstance(value, dict):
                for field in ("source_artifact_path", "source_text_file"):
                    if field in value:
                        descriptors.append((f"{location}.{field}", value.get(field)))
                anchors = value.get("source_anchor_evidence")
                if isinstance(anchors, list):
                    for index, anchor in enumerate(anchors):
                        if isinstance(anchor, dict) and "path" in anchor:
                            descriptors.append(
                                (
                                    f"{location}.source_anchor_evidence[{index}].path",
                                    anchor.get("path"),
                                )
                            )
                for field, child in value.items():
                    if field == "source_anchor_evidence":
                        continue
                    collect_item_source_paths(child, f"{location}.{field}")
            elif isinstance(value, list):
                for index, child in enumerate(value):
                    collect_item_source_paths(child, f"{location}[{index}]")

        collect_item_source_paths(payload)
        companion = payload.get("source_text_companion")
        if isinstance(companion, dict):
            for field in sorted(SOURCE_TEXT_COMPANION_PATH_FIELDS):
                descriptor = companion.get(field)
                raw_path = descriptor.get("path") if isinstance(descriptor, dict) else None
                descriptors.append((f"source_text_companion.{field}.path", raw_path))
        archive_surface = payload.get("source_archive_surface")
        if isinstance(archive_surface, dict):
            archive = archive_surface.get("archive")
            raw_path = archive.get("path") if isinstance(archive, dict) else None
            descriptors.append(("source_archive_surface.archive.path", raw_path))
        reported_artifacts: set[str] = set()
        for field, raw_path in descriptors:
            artifact = _paper_local_candidate_path(
                paper_dir=paper_dir, raw_path=raw_path
            )
            if artifact is None:
                if isinstance(raw_path, str) and raw_path.strip():
                    issues.append(
                        f"{map_path}: declared private source artifact path is unsafe "
                        f"or leaves its paper directory ({field} -> {raw_path.strip()})"
                    )
                continue
            if artifact in approved_arxiv_tex:
                continue
            if artifact not in reported_artifacts and _artifact_present(
                candidate_paths, artifact
            ):
                reported_artifacts.add(artifact)
                issues.append(
                    f"{map_path}: declared private source artifact is present in the "
                    f"public candidate ({field} -> {artifact})"
                )
    return issues


def _candidate_json_object(
    repo: Path,
    candidate_ref: str,
    path: str,
    *,
    label: str,
) -> tuple[dict[str, object] | None, bytes | None, list[str]]:
    """Read one candidate JSON object without falling back to its worktree.

    Public display projections are bound to the committed candidate tree.  In
    particular, this helper never opens a local source artifact or substitutes
    current private bytes for the candidate's displayed excerpts.
    """

    try:
        raw = _git_bytes(repo, ["show", f"{candidate_ref}:{path}"])
    except RuntimeError as exc:
        return None, None, [f"{label}: cannot read candidate JSON: {exc}"]
    try:
        payload = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        return None, raw, [f"{label}: candidate JSON is invalid: {exc}"]
    if not isinstance(payload, dict):
        return None, raw, [f"{label}: candidate JSON must be an object"]
    return payload, raw, []


def _valid_sha256(value: object) -> str | None:
    """Return one canonical SHA-256 string, or ``None`` for an invalid value."""

    if not isinstance(value, str):
        return None
    normalized = value.strip().lower()
    return normalized if SHA256_RE.fullmatch(normalized) else None


def _valid_display_anchor_errors(
    public_anchor: object,
    manifest_anchor: object,
    *,
    label: str,
) -> list[str]:
    """Compare one public-map anchor to its display-manifest anchor.

    The candidate map is already the public projection, so a ``path`` field is
    itself an error.  We nevertheless remove it for the exact-content
    comparison in order to describe the intended correspondence precisely and
    to produce a useful diagnostic for an accidentally unprojected map.
    """

    errors: list[str] = []
    if not isinstance(public_anchor, dict):
        return [f"{label}: projected-map anchor is not an object"]
    if not isinstance(manifest_anchor, dict):
        return [f"{label}: display-manifest anchor is not an object"]
    if "path" in public_anchor:
        errors.append(f"{label}: projected-map anchor retains a source path")
    if "path" in manifest_anchor:
        errors.append(f"{label}: display-manifest anchor retains a source path")
    public_without_path = {
        key: value for key, value in public_anchor.items() if key != "path"
    }
    if public_without_path != manifest_anchor:
        errors.append(
            f"{label}: display-manifest anchor does not exactly match the projected map"
        )
    for surface, anchor in (
        ("projected-map", public_without_path),
        ("display-manifest", manifest_anchor),
    ):
        if anchor.get("publication_locator") != PUBLICATION_LOCATOR:
            errors.append(f"{label}: {surface} anchor lacks publication_locator `cited publication`")
        line_start = anchor.get("line_start")
        line_end = anchor.get("line_end")
        if (
            not isinstance(line_start, int)
            or isinstance(line_start, bool)
            or line_start < 1
        ):
            errors.append(f"{label}: {surface} anchor has an invalid line_start")
        if (
            not isinstance(line_end, int)
            or isinstance(line_end, bool)
            or not isinstance(line_start, int)
            or isinstance(line_start, bool)
            or line_end < line_start
        ):
            errors.append(f"{label}: {surface} anchor has an invalid line_end")
        quote = anchor.get("quoted_text")
        quote_sha256 = _valid_sha256(anchor.get("quoted_text_sha256"))
        if not isinstance(quote, str) or not quote:
            errors.append(f"{label}: {surface} anchor has no quoted_text")
        elif quote_sha256 is None:
            errors.append(f"{label}: {surface} anchor has an invalid quoted_text_sha256")
        elif _sha256_bytes(quote.encode("utf-8")) != quote_sha256:
            errors.append(f"{label}: {surface} anchor quoted_text_sha256 does not match quoted_text")
    return errors


def _display_anchor_bundle_issues(
    public_anchors: object,
    manifest_anchors: object,
    *,
    label: str,
) -> list[str]:
    if not isinstance(public_anchors, list):
        return [f"{label}: projected-map source_anchor_evidence is not a list"]
    if not isinstance(manifest_anchors, list):
        return [f"{label}: display-manifest source_anchors is not a list"]
    errors: list[str] = []
    if not public_anchors:
        errors.append(f"{label}: projected-map source_anchor_evidence is empty")
    if not manifest_anchors:
        errors.append(f"{label}: display-manifest source_anchors is empty")
    if len(public_anchors) != len(manifest_anchors):
        errors.append(f"{label}: display-manifest source anchor count does not match the projected map")
    for index, public_anchor in enumerate(public_anchors):
        if index >= len(manifest_anchors):
            break
        errors.extend(
            _valid_display_anchor_errors(
                public_anchor,
                manifest_anchors[index],
                label=f"{label} source anchor {index}",
            )
        )
    return errors


def _display_selected_item_issues(
    public_item: object,
    manifest_item: object,
    *,
    item_id: str,
) -> list[str]:
    """Validate the displayed direct and contextual anchors for one source item."""

    label = f"selected source item `{item_id}`"
    if not isinstance(public_item, dict):
        return [f"{label}: absent from the projected source map"]
    if not isinstance(manifest_item, dict):
        return [f"{label}: absent from the display manifest"]
    errors: list[str] = []
    public_kind = public_item.get("source_kind")
    manifest_kind = manifest_item.get("source_kind")
    if not isinstance(public_kind, str) or not public_kind.strip():
        errors.append(f"{label}: projected-map source_kind is not a nonempty string")
    if public_kind != manifest_kind:
        errors.append(f"{label}: display-manifest source_kind does not match the projected map")
    errors.extend(
        _display_anchor_bundle_issues(
            public_item.get("source_anchor_evidence"),
            manifest_item.get("source_anchors"),
            label=label,
        )
    )

    public_context = public_item.get("semantic_context_requirements", [])
    manifest_context = manifest_item.get("semantic_context", [])
    if not isinstance(public_context, list):
        errors.append(f"{label}: projected-map semantic_context_requirements is not a list")
        return errors
    if not isinstance(manifest_context, list):
        errors.append(f"{label}: display-manifest semantic_context is not a list")
        return errors
    if len(public_context) != len(manifest_context):
        errors.append(f"{label}: display-manifest semantic context count does not match the projected map")
    for index, context in enumerate(public_context):
        if index >= len(manifest_context):
            break
        context_label = f"{label} semantic context {index}"
        manifest_record = manifest_context[index]
        if not isinstance(context, dict):
            errors.append(f"{context_label}: projected-map record is not an object")
            continue
        if not isinstance(manifest_record, dict):
            errors.append(f"{context_label}: display-manifest record is not an object")
            continue
        if context.get("semantic_role") != manifest_record.get("semantic_role"):
            errors.append(f"{context_label}: semantic_role does not match the projected map")
        errors.extend(
            _display_anchor_bundle_issues(
                context.get("source_anchor_evidence"),
                manifest_record.get("source_anchors"),
                label=context_label,
            )
        )
    return errors


def _private_source_map_binding_issues(
    *,
    manifest_private_sha256: str,
    map_path: str,
    entries: list[AllowlistEntry],
    private_repo: Path | None,
) -> list[str]:
    """Bind a displayed private-map digest when this release exports that map.

    A previously released, unchanged map has already been checked in its own
    candidate.  For a map changed in this candidate, the allowlist's exact
    private provenance is the authoritative binding.  This does not read a
    source artifact or characterize the public excerpt as a fresh byte audit.
    """

    entry = matching_allowlist_entry(map_path, entries)
    if entry is None or entry.source_commit is None:
        return []
    if entry.provenance == "private_projection":
        if entry.private_source_blob_sha256 != manifest_private_sha256:
            return [
                f"{map_path}: display manifest private_source_map_sha256 does not match "
                "the allowlisted private source-map blob"
            ]
        return []
    if entry.provenance != "private_blob" or private_repo is None:
        return []
    try:
        private_blob = _git_bytes(
            private_repo, ["show", f"{entry.source_commit}:{map_path}"]
        )
    except RuntimeError as exc:
        return [
            f"{map_path}: cannot bind display manifest private_source_map_sha256 "
            f"to allowlisted private map: {exc}"
        ]
    if _sha256_bytes(private_blob) != manifest_private_sha256:
        return [
            f"{map_path}: display manifest private_source_map_sha256 does not match "
            "the allowlisted private source map"
        ]
    return []


def public_source_display_projection_issues(
    candidate_repo: Path,
    candidate_ref: str,
    entries: list[AllowlistEntry],
    *,
    private_repo: Path | None = None,
) -> list[str]:
    """Validate candidate-only review displays without reopening private sources.

    A map with the public display marker must carry a matching, committed
    display manifest.  The manifest is only a safe presentation binding: it
    proves that the candidate's selected excerpts, hashes, and coverage mode
    agree with the projected map.  It deliberately does *not* make the public
    candidate a replacement for the private byte-pinned source audit.
    """

    candidate_paths = set(
        _git(candidate_repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
    )
    map_paths = sorted(
        path
        for path in candidate_paths
        if path.startswith("papers/")
        and path.endswith("/audit/paper_statement_map.json")
    )
    issues: list[str] = []
    for map_path in map_paths:
        map_payload, map_bytes, map_errors = _candidate_json_object(
            candidate_repo,
            candidate_ref,
            map_path,
            label=map_path,
        )
        issues.extend(map_errors)
        if map_payload is None or map_bytes is None:
            continue
        marker = map_payload.get(PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD)
        paper_dir = PurePosixPath(map_path).parents[1]
        expected_manifest = str(paper_dir / PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST)
        if marker is None:
            if expected_manifest in candidate_paths:
                issues.append(
                    f"{map_path}: saved public display manifest requires the exact "
                    "display-projection marker"
                )
            continue
        if not isinstance(marker, dict):
            issues.append(f"{map_path}: public display-projection marker must be an object")
            continue
        if marker.get("schema") != PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA:
            issues.append(f"{map_path}: public display-projection marker has the wrong schema")
        if marker.get("manifest") != PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST:
            issues.append(f"{map_path}: public display-projection marker has the wrong manifest path")
        if marker.get("raw_source_bytes_included") is not False:
            issues.append(f"{map_path}: public display-projection marker must declare raw_source_bytes_included=false")
        if expected_manifest not in candidate_paths:
            issues.append(f"{map_path}: marked public map is missing `{expected_manifest}`")
            continue
        manifest_payload, _manifest_bytes, manifest_errors = _candidate_json_object(
            candidate_repo,
            candidate_ref,
            expected_manifest,
            label=expected_manifest,
        )
        issues.extend(manifest_errors)
        if manifest_payload is None:
            continue

        if manifest_payload.get("schema") != PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA:
            issues.append(f"{expected_manifest}: display manifest has the wrong schema")
        if manifest_payload.get("generator") != PUBLIC_SOURCE_DISPLAY_PROJECTION_GENERATOR:
            issues.append(f"{expected_manifest}: display manifest has an unexpected generator")
        if manifest_payload.get("paper_id") != paper_dir.name:
            issues.append(f"{expected_manifest}: display manifest paper_id does not match its paper directory")
        if manifest_payload.get("public_manifest_path") != expected_manifest:
            issues.append(f"{expected_manifest}: display manifest public_manifest_path does not match its candidate path")
        if manifest_payload.get("raw_source_artifact_included") is not False:
            issues.append(f"{expected_manifest}: display manifest must declare raw_source_artifact_included=false")
        if manifest_payload.get("raw_source_display_material") != PUBLIC_SOURCE_DISPLAY_PROJECTION_MATERIAL:
            issues.append(f"{expected_manifest}: display manifest has unexpected source display material")

        expected_public_map_sha256 = _sha256_bytes(map_bytes)
        actual_public_map_sha256 = _valid_sha256(
            manifest_payload.get("public_source_map_sha256")
        )
        if actual_public_map_sha256 is None:
            issues.append(f"{expected_manifest}: display manifest has no valid public_source_map_sha256")
        elif actual_public_map_sha256 != expected_public_map_sha256:
            issues.append(f"{expected_manifest}: display manifest public_source_map_sha256 does not match the candidate projected map")

        private_source_map_sha256 = manifest_payload.get("private_source_map_sha256")
        if private_source_map_sha256 is not None:
            normalized_private_map_sha256 = _valid_sha256(private_source_map_sha256)
            if normalized_private_map_sha256 is None:
                issues.append(f"{expected_manifest}: display manifest has an invalid private_source_map_sha256")
            else:
                issues.extend(
                    _private_source_map_binding_issues(
                        manifest_private_sha256=normalized_private_map_sha256,
                        map_path=map_path,
                        entries=entries,
                        private_repo=private_repo,
                    )
                )

        public_artifact_sha256 = _valid_sha256(map_payload.get("source_artifact_sha256"))
        manifest_artifact_sha256 = _valid_sha256(
            manifest_payload.get("source_artifact_sha256")
        )
        if public_artifact_sha256 is None:
            issues.append(f"{map_path}: projected source map has no valid source_artifact_sha256")
        if manifest_artifact_sha256 is None:
            issues.append(f"{expected_manifest}: display manifest has no valid source_artifact_sha256")
        elif manifest_artifact_sha256 != public_artifact_sha256:
            issues.append(f"{expected_manifest}: display manifest source_artifact_sha256 does not match the projected source map")
        public_coverage_mode = map_payload.get("source_coverage_mode")
        manifest_coverage_mode = manifest_payload.get("source_coverage_mode")
        if not isinstance(public_coverage_mode, str) or not public_coverage_mode.strip():
            issues.append(f"{map_path}: projected source map has no valid source_coverage_mode")
        if manifest_coverage_mode != public_coverage_mode:
            issues.append(f"{expected_manifest}: display manifest source_coverage_mode does not match the projected source map")

        selected_ids = manifest_payload.get("selected_source_item_ids")
        selected_items = manifest_payload.get("selected_source_items")
        if not isinstance(selected_ids, list) or any(
            not isinstance(item_id, str) or not item_id for item_id in selected_ids
        ):
            issues.append(f"{expected_manifest}: selected_source_item_ids must be a list of nonempty strings")
            continue
        if selected_ids != sorted(set(selected_ids)):
            issues.append(f"{expected_manifest}: selected_source_item_ids must be sorted and unique")
        if not isinstance(selected_items, dict):
            issues.append(f"{expected_manifest}: selected_source_items must be an object")
            continue
        if set(selected_items) != set(selected_ids):
            issues.append(f"{expected_manifest}: selected_source_items keys do not match selected_source_item_ids")
            continue
        public_items = map_payload.get("items")
        if not isinstance(public_items, dict):
            issues.append(f"{map_path}: projected source map items must be an object")
            continue
        for item_id in selected_ids:
            issues.extend(
                _display_selected_item_issues(
                    public_items.get(item_id),
                    selected_items.get(item_id),
                    item_id=item_id,
                )
            )
    return sorted(set(issues))


def forbidden_candidate_path_issues(
    repo: Path, candidate_ref: str = "HEAD"
) -> list[str]:
    approved_source_tex, _ = approved_public_source_tex_paths(repo, candidate_ref)
    return [
        f"forbidden private/source artifact path in public candidate: {path}"
        for path in sorted(
            _git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
        )
        if FORBIDDEN_PUBLIC_PATH_RE.search(path)
        and path not in approved_source_tex
        and path not in PUBLIC_PRIVATE_NAMED_WORKFLOW_PATHS
    ]


def session_insights_path_issues(
    repo: Path, candidate_ref: str = "HEAD"
) -> list[str]:
    """Reject private wiki evidence and session-derived maintenance records.

    This is intentionally a path allowlist rather than a content heuristic:
    a new trace export can be benign-looking while still disclosing a user's
    private session history. Only the self-contained general skill entrypoint
    is public; the check covers the whole tree, not just newly added files.
    """

    paths = _git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
    return [
        "unapproved session-insights artifact in public candidate: " + path
        for path in sorted(paths)
        if path.startswith("wiki/")
        or (
            path.startswith(SESSION_INSIGHTS_PREFIX)
            and path not in PUBLIC_SESSION_INSIGHTS_PATHS
        )
    ]


PUBLIC_ARTIFACT_CONTENT_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "local filesystem path",
        re.compile(
            r"(?<![A-Za-z0-9_.-])/(?:tmp|home)(?=$|/)(?:/[^\s,;:()\[\]{}]+)*"
        ),
    ),
    (
        "private audit-source path",
        re.compile(r"(?<![A-Za-z0-9_.-])(?:[A-Za-z0-9_.-]+/)*\.audit_source(?:/[^\s,;:()\[\]{}]+)*"),
    ),
    (
        "private TeX audit-source path",
        re.compile(r"(?<![A-Za-z0-9_.-])\.?audit\\_source\b", re.IGNORECASE),
    ),
    (
        "non-public source transcript locator",
        re.compile(
            r"(?<![A-Za-z0-9_.-])(?:"
            r"(?:[A-Za-z0-9_.-]+/)*(?:sources?|source_tex|audit)/"
            r"[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*\.(?:txt|tex|pdf|html|tar(?:\.gz)?)"
            r"|source(?:[_-][A-Za-z0-9_.-]+)\.(?:txt|tex|pdf|html|tar(?:\.gz)?)"
            r"|source\.txt"
            r")(?![A-Za-z0-9_-])",
            re.IGNORECASE,
        ),
    ),
    (
        "non-public source artifact locator",
        re.compile(
            r"(?<![A-Za-z0-9_.-])(?:"
            r"(?:[A-Za-z0-9_.-]+/)*"
            r"|\.scratch/\$PAPER/)"
            r"source\.(?:pdf|tar(?:\.gz)?)(?![A-Za-z0-9_-])",
            re.IGNORECASE,
        ),
    ),
    (
        "private source-extraction wording",
        re.compile(r"\bprivate\s+(?:text|source)(?:[-\s]+)?extraction\b", re.IGNORECASE),
    ),
    ("remediation-handoff wording", re.compile(r"\bremediation\s+handoff\b", re.IGNORECASE)),
    (
        "unresolved-handoff wording",
        re.compile(r"\bunresolved\s+mathematical\s+handoff\b", re.IGNORECASE),
    ),
    (
        "agent remediation workflow wording",
        re.compile(r"\bcodex\b[^\n]{0,160}?\bremediation\b", re.IGNORECASE),
    ),
    ("local PDF-cache wording", re.compile(r"\blocal\s+PDF\s+cache\b", re.IGNORECASE)),
    ("local source-cache wording", re.compile(r"\bsource\s+cache\b", re.IGNORECASE)),
    ("private PAPER_NOTES reference", re.compile(r"\bPAPER_NOTES\.md\b", re.IGNORECASE)),
    (
        "private repository identity",
        re.compile(r"\bEconCSLib-private(?:-archive-[0-9]+)?\b", re.IGNORECASE),
    ),
    (
        "private artifact route",
        re.compile(r"(?:data-private-local-href|/private-artifacts(?:/|$))", re.IGNORECASE),
    ),
    (
        "private workflow reference",
        re.compile(
            r"\b(?:trusted\s+)?private\s+(?:origin(?:/main)?|source(?:\s+(?:review|commit|artifact|text))?|"
            r"checkout|workspace|workflow|repository(?:\s+context)?|collaboration\s+space|"
            r"(?:proof\s+body|intake|closeout|handoff)|Git\s+objects|by-default|by\s+sorry|"
            r"paper(?:\s+(?:folder|thread|development))?|"
            r"(?:plans?|approvals?|planning|history|incubator|target-setting\s+phase))\b",
            re.IGNORECASE,
        ),
    ),
    (
        "local review-trace path",
        re.compile(r"(?:^|[\s`])\.review_traces(?:/[^\s`]+)?", re.IGNORECASE),
    ),
    (
        "local scratch-workflow path",
        re.compile(r"(?:^|[\s`])\.scratch(?:/[^\s`]+)?", re.IGNORECASE),
    ),
    (
        "external reviewer-approval filesystem path",
        re.compile(r"~/.config/econcslib(?:/|$)", re.IGNORECASE),
    ),
)
_PUBLIC_HTTP_URL_RE = re.compile(r"https?://[^\s<>()\[\]{}]+", re.IGNORECASE)
_PRIVATE_PUBLIC_URL_RE = re.compile(
    r"(?:econcslib-private|private-artifacts|\.audit_source|\.review_traces)",
    re.IGNORECASE,
)
_GENERIC_SOURCE_TRANSCRIPT_LOCATOR_RE = re.compile(
    r"(?<![A-Za-z0-9_.-])(?:[A-Za-z0-9_.-]+/)*"
    r"[A-Za-z0-9_.-]+\.(?:txt|tex|pdf|html|tar(?:\.gz)?)(?::\d+(?:-\d+)?)?"
    r"(?![A-Za-z0-9_-])",
    re.IGNORECASE,
)
_SOURCE_LOCATOR_ROUTE_KEYS = frozenset(
    {
        "affected_source_locators",
        "archival_source_locator",
        "artifact_path",
        "companion_html_path",
        "extracted_tex_path",
        "non_target_source_inventory",
        "printed_source_locations",
        "semantic_basis",
        "semantic_match",
        "source_evidence",
        "source_expression",
        "source_anchor",
        "source_anchor_evidence",
        "source_anchors",
        "source_location",
        "source_locator",
        "source_pdf",
        "source_restatement_evidence",
        "source_stage",
        "source_support_scope",
        "source_term_use_anchor",
        "source_text",
        "statement",
    }
)


def _decoded_url_for_policy(url: str) -> str:
    """Decode bounded URL escapes before checking an internal route."""

    decoded = url
    for _ in range(3):
        next_decoded = html_unescape(unquote(decoded))
        if next_decoded == decoded:
            break
        decoded = next_decoded
    return decoded


def _decoded_text_for_policy(value: str) -> str:
    """Decode inert HTML/URL encodings before boundary-pattern checks."""

    decoded = value
    for _ in range(3):
        next_decoded = html_unescape(unquote(decoded))
        if next_decoded == decoded:
            break
        decoded = next_decoded
    return decoded


def _source_locator_route_has_local_transcript(
    value: str, route: tuple[str, ...]
) -> bool:
    """Whether a source-locator field still names an unavailable transcript."""

    return (
        any(component in _SOURCE_LOCATOR_ROUTE_KEYS for component in route)
        and _GENERIC_SOURCE_TRANSCRIPT_LOCATOR_RE.search(value) is not None
    )


def _is_audit_sidecar_path(relative_path: str) -> bool:
    """Whether a JSON artifact is an audit sidecar rather than a review map.

    Audit sidecars may name the internal transcript that supported a review.
    The filename carries provenance, not source bytes. Dashboard-facing maps,
    statuses, packets, and prose remain citation-centered.
    """

    path = PurePosixPath(relative_path)
    return (
        len(path.parts) == 4
        and path.parts[0] == "papers"
        and path.parts[2] == "audit"
        and path.suffix.lower() == ".json"
        and path.name
        not in {"paper_statement_map.json", "public_source_display_projection.json"}
    )


PUBLIC_SOURCE_EXCERPT_FIELDS = frozenset(
    {"quoted_text", "source_excerpt", "source_quote"}
)


def _private_public_url_issue(value: str) -> str | None:
    """Return a boundary error for a URL that names a non-public surface."""

    for match in _PUBLIC_HTTP_URL_RE.finditer(value):
        if _PRIVATE_PUBLIC_URL_RE.search(_decoded_url_for_policy(match.group(0))):
            return "private repository or artifact URL"
    return None


def _mask_approved_source_tex_references(value: str, approved_paths: set[str]) -> str:
    """Hide only known official-source paths during local-path hygiene scans.

    A checked-in arXiv TeX artifact is user-approved evidence.  Its exact
    repository path can therefore appear in public documentation without being
    mistaken for a private transcript locator.  The generic placeholder used
    in the release checklist is likewise documentation, not an actual source
    path.  No other ``source/`` path receives this exception.
    """

    result = value.replace("papers/<Paper>/source/<file>.tex", "APPROVED_SOURCE_TEX")
    for path in approved_paths:
        result = result.replace(path, "APPROVED_SOURCE_TEX")
    return result


def _mask_json_source_tex_references(
    value: object, approved_paths: set[str]
) -> object:
    """Return a scan-only JSON copy with approved TeX paths neutralized."""

    if isinstance(value, dict):
        return {
            key: _mask_json_source_tex_references(child, approved_paths)
            for key, child in value.items()
        }
    if isinstance(value, list):
        return [
            _mask_json_source_tex_references(child, approved_paths) for child in value
        ]
    if isinstance(value, str):
        return _mask_approved_source_tex_references(value, approved_paths)
    return value


def _public_artifact_string_issues(
    value: object,
    *,
    relative_path: str,
    route: tuple[str, ...] = (),
    source_excerpt: bool = False,
) -> list[tuple[str, str]]:
    """Find release-private wording while respecting approved source excerpts."""

    issues: list[tuple[str, str]] = []
    if isinstance(value, dict):
        bound_excerpt_fields = {
            key
            for key in PUBLIC_SOURCE_EXCERPT_FIELDS
            if source_excerpt_field_is_bound(value, key)
            and public_source_excerpt_route_is_permitted(
                relative_path, (*route, key)
            )
        }
        for key, child in value.items():
            if not isinstance(key, str):
                continue
            issues.extend(
                _public_artifact_string_issues(
                    child,
                    relative_path=relative_path,
                    route=(*route, key),
                    source_excerpt=(
                        source_excerpt
                        or (key in bound_excerpt_fields and isinstance(child, str))
                    ),
                )
            )
        return issues
    if isinstance(value, list):
        for index, child in enumerate(value):
            issues.extend(
                _public_artifact_string_issues(
                    child,
                    relative_path=relative_path,
                    route=(*route, str(index)),
                    source_excerpt=source_excerpt,
                )
            )
        return issues
    if not isinstance(value, str):
        return issues
    if route and route[-1] == "approval_reference" and value != PUBLIC_WITHHELD_APPROVAL_REFERENCE:
        issues.append((".".join(route), "private scope approval reference must be withheld"))
    if "deep_support_repair" in route and "approval" in route:
        if route[-1] not in {"publication_record", "private_record_sha256"}:
            issues.append((".".join(route), "private repair approval material must be withheld"))
    if source_excerpt:
        issue = source_excerpt_safety_issue(value)
        if issue is not None:
            issues.append((".".join(route) or "$", issue))
        return issues
    policy_value = _decoded_text_for_policy(value)
    permits_internal_transcript_filename = _is_audit_sidecar_path(relative_path)
    if (
        not permits_internal_transcript_filename
        and _source_locator_route_has_local_transcript(policy_value, route)
    ):
        issues.append((".".join(route) or "$", "non-public source transcript locator"))
    url_issue = _private_public_url_issue(policy_value)
    if url_issue is not None:
        issues.append((".".join(route) or "$", url_issue))
    scan_value = _PUBLIC_HTTP_URL_RE.sub("PUBLIC_HTTP_URL", policy_value)
    for label, pattern in PUBLIC_ARTIFACT_CONTENT_PATTERNS:
        if label == "non-public source transcript locator" and permits_internal_transcript_filename:
            continue
        if pattern.search(scan_value):
            issues.append((".".join(route) or "$", label))
    return issues


def _accepted_source_role_material(
    repo: Path,
    candidate_ref: str,
    paper: str,
) -> tuple[str, dict[str, str], bytes, bytes, str]:
    """Load exact selected graph bytes and their validated source-role index."""

    try:
        from scripts.obligation_evidence_graph import build_obligation_graph
        from scripts.obligation_evidence_store import (
            load_recorded_current_accepted_obligation_graph,
        )
        from scripts.obligation_paper_index import validate_paper_obligation_index
    except ModuleNotFoundError:  # pragma: no cover - direct-script support.
        from obligation_evidence_graph import build_obligation_graph
        from obligation_evidence_store import (
            load_recorded_current_accepted_obligation_graph,
        )
        from obligation_paper_index import validate_paper_obligation_index

    base = f"papers/{paper}/audit/obligation_evidence"
    pointer_path = f"{base}/current_accepted_graph.json"
    pointer_bytes = _git_bytes(repo, ["show", f"{candidate_ref}:{pointer_path}"])
    try:
        pointer = json.loads(pointer_bytes)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError("selected accepted-graph pointer is not valid JSON") from exc
    graph_sha256 = pointer.get("graph_sha256") if isinstance(pointer, dict) else None
    if (
        not isinstance(pointer, dict)
        or set(pointer) != {"schema", "graph_sha256"}
        or pointer.get("schema") != 2
        or not isinstance(graph_sha256, str)
        or not SHA256_RE.fullmatch(graph_sha256)
    ):
        raise ValueError("selected accepted-graph pointer is malformed")
    pack_path = (
        f"{base}/accepted_graphs/sha256/{graph_sha256[:2]}/{graph_sha256}.json"
    )
    pack_bytes = _git_bytes(repo, ["show", f"{candidate_ref}:{pack_path}"])
    try:
        packed = json.loads(pack_bytes)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError("selected packed accepted graph is not valid JSON") from exc
    if not isinstance(packed, dict):
        raise ValueError("selected packed accepted graph is malformed")

    # Reuse the store owner for canonical pointer, graph, leaf, and pack
    # validation. The temporary tree contains only the exact candidate blobs.
    with tempfile.TemporaryDirectory(prefix="public-role-accepted-graph-") as temporary:
        snapshot = Path(temporary)
        for path, raw in ((pointer_path, pointer_bytes), (pack_path, pack_bytes)):
            destination = snapshot / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(raw)
        accepted = load_recorded_current_accepted_obligation_graph(
            snapshot, paper, graph_sha256
        )

    if accepted.graph_sha256 != graph_sha256 or len(accepted.root_leaf_sha256s) != 1:
        raise ValueError("selected accepted graph identity or root is malformed")
    closure = accepted.leaves[accepted.root_leaf_sha256s[0]]
    semantic = build_obligation_graph(
        (
            leaf
            for digest, leaf in accepted.leaves.items()
            if digest != closure.leaf_sha256
        ),
        root_leaf_sha256s=closure.depends_on,
    )
    if closure.semantic_payload.get("semantic_graph_sha256") != semantic.graph_sha256:
        raise ValueError("selected closure binds a different semantic graph")
    paper_index = validate_paper_obligation_index(
        packed.get("paper_index"),
        graph=semantic,
        require_complete=True,
        preflight=None,
        require_current_aggregate_identity=False,
    )
    if closure.semantic_payload.get("paper_index_sha256") != paper_index.index_sha256:
        raise ValueError("selected closure binds a different paper index")
    roles = accepted_source_role_sha256s_by_source_item(accepted, paper_index)
    return graph_sha256, roles, pointer_bytes, pack_bytes, pack_path


def public_source_role_projection_issues(
    candidate_repo: Path,
    candidate_ref: str,
    entries: list[AllowlistEntry],
    *,
    private_repo: Path,
    public_base_ref: str | None = PUBLIC_BASE_REF,
) -> list[str]:
    """Validate guard-issued role bridges or exact trusted-base carryforward."""

    candidate_paths = set(
        _git(candidate_repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
    )
    manifest_paths = sorted(
        path
        for path in candidate_paths
        if len(PurePosixPath(path).parts) == 4
        and PurePosixPath(path).parts[0] == "papers"
        and PurePosixPath(path).parts[2:] == (
            "audit",
            "public_source_display_projection.json",
        )
    )
    issues: list[str] = []
    for manifest_path in manifest_paths:
        paper = PurePosixPath(manifest_path).parts[1]
        prefix = f"papers/{paper}/audit"
        map_path = f"{prefix}/paper_statement_map.json"
        envelope_path = f"{prefix}/{PurePosixPath(PUBLIC_SOURCE_ROLE_PROJECTION_FILE).name}"
        missing = [
            path for path in (map_path, envelope_path) if path not in candidate_paths
        ]
        if missing:
            issues.append(
                f"{manifest_path}: public source-role projection is incomplete; missing "
                + ", ".join(missing)
            )
            continue
        try:
            map_bytes = _git_bytes(
                candidate_repo, ["show", f"{candidate_ref}:{map_path}"]
            )
            manifest_bytes = _git_bytes(
                candidate_repo, ["show", f"{candidate_ref}:{manifest_path}"]
            )
            envelope_bytes = _git_bytes(
                candidate_repo, ["show", f"{candidate_ref}:{envelope_path}"]
            )
            (
                graph_sha256,
                accepted_roles,
                pointer_bytes,
                pack_bytes,
                pack_path,
            ) = _accepted_source_role_material(candidate_repo, candidate_ref, paper)
        except (RuntimeError, ValueError, PublicSourceRoleProjectionError) as exc:
            issues.append(
                f"{envelope_path}: cannot load accepted public source-role inputs: {exc}"
            )
            continue

        unchanged_from_base = False
        if public_base_ref is not None:
            try:
                unchanged_from_base = all(
                    _git_bytes(candidate_repo, ["show", f"{public_base_ref}:{path}"])
                    == raw
                    for path, raw in (
                        (map_path, map_bytes),
                        (manifest_path, manifest_bytes),
                        (envelope_path, envelope_bytes),
                    )
                )
            except RuntimeError:
                unchanged_from_base = False

        try:
            if unchanged_from_base:
                validate_runtime_public_source_role_projection(
                    trusted_envelope_bytes=envelope_bytes,
                    paper=paper,
                    public_source_map_bytes=map_bytes,
                    public_display_manifest_bytes=manifest_bytes,
                    accepted_graph_sha256=graph_sha256,
                    accepted_role_sha256s_by_source_item=accepted_roles,
                )
                continue

            entry = matching_allowlist_entry(map_path, entries)
            if (
                entry is None
                or entry.provenance != "private_projection"
                or entry.source_commit is None
            ):
                raise PublicSourceRoleProjectionError(
                    "new or changed role projection requires the source map's exact "
                    "private_projection allowlist provenance"
                )
            private_map_bytes = _git_bytes(
                private_repo, ["show", f"{entry.source_commit}:{map_path}"]
            )
            if (
                _sha256_bytes(private_map_bytes) != entry.private_source_blob_sha256
                or _sha256_bytes(map_bytes) != entry.candidate_blob_sha256
            ):
                raise PublicSourceRoleProjectionError(
                    "source map bytes do not match private_projection allowlist digests"
                )
            private_pointer_bytes = _git_bytes(
                private_repo,
                [
                    "show",
                    f"{entry.source_commit}:papers/{paper}/audit/obligation_evidence/"
                    "current_accepted_graph.json",
                ],
            )
            private_pack_bytes = _git_bytes(
                private_repo, ["show", f"{entry.source_commit}:{pack_path}"]
            )
            if (
                private_pointer_bytes != pointer_bytes
                or private_pack_bytes != pack_bytes
            ):
                raise PublicSourceRoleProjectionError(
                    "selected accepted graph differs from the pinned private source commit"
                )
            validate_public_source_role_projection_envelope(
                envelope_bytes,
                paper=paper,
                private_source_map_bytes=private_map_bytes,
                public_source_map_bytes=map_bytes,
                public_display_manifest_bytes=manifest_bytes,
                accepted_graph_sha256=graph_sha256,
                accepted_role_sha256s_by_source_item=accepted_roles,
            )
        except (RuntimeError, ValueError, PublicSourceRoleProjectionError) as exc:
            issues.append(f"{envelope_path}: {exc}")
    return issues


def approved_public_source_tex_paths(
    repo: Path, candidate_ref: str
) -> tuple[set[str], list[str]]:
    """Return exact official-arXiv TeX excerpts permitted in a public tree.

    Source TeX is user-approved evidence only when it is actually the
    byte-pinned source surface of that paper.  The check deliberately rejects
    an arbitrary ``papers/*/source/*.tex`` file: it must have an arXiv source
    URL and hash-match the paper map's declared source artifact.
    """

    paths = sorted(
        path
        for path in _git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
        if re.fullmatch(r"papers/[^/]+/source/[^/]+\.tex", path)
    )
    approved: set[str] = set()
    issues: list[str] = []
    for path in paths:
        paper = PurePosixPath(path).parts[1]
        map_path = f"papers/{paper}/audit/paper_statement_map.json"
        try:
            payload = json.loads(_git_bytes(repo, ["show", f"{candidate_ref}:{map_path}"]))
        except (RuntimeError, json.JSONDecodeError) as exc:
            issues.append(
                f"{path}: public source TeX lacks a readable paper statement map ({exc})"
            )
            continue
        if not isinstance(payload, dict):
            issues.append(f"{path}: public source TeX paper statement map must be an object")
            continue
        source_url = str(payload.get("source_url") or "").strip()
        if not re.match(
            r"https?://(?:export\.)?arxiv\.org/(?:abs|e-print|pdf)/",
            source_url,
            flags=re.IGNORECASE,
        ):
            issues.append(
                f"{path}: public source TeX requires an official arXiv source_url"
            )
            continue
        expected_sha = _valid_sha256(payload.get("source_artifact_sha256"))
        if expected_sha is None:
            issues.append(
                f"{path}: public source TeX paper statement map has no valid source_artifact_sha256"
            )
            continue
        actual_sha = _sha256_bytes(_git_bytes(repo, ["show", f"{candidate_ref}:{path}"]))
        if actual_sha != expected_sha:
            issues.append(
                f"{path}: public source TeX hash does not match the paper statement map"
            )
            continue
        approved.add(path)
    return approved, issues


def public_artifact_content_issues(
    repo: Path,
    candidate_ref: str,
    _changes: list[CandidateChange] | None = None,
) -> list[str]:
    """Reject private audit mechanics in every public-facing text artifact.

    The policy intentionally permits user-approved source excerpts and official
    arXiv TeX.  It scans the complete release-relevant ``papers/``, ``docs/``,
    ``site/``, and human-facing skill-documentation tree rather than only a
    candidate diff: an inherited public blob with a local audit path must not
    become invisible merely because it was not touched by the last release
    commit.  It additionally covers root contributor documentation and release
    configuration, while deliberately excluding implementation code: a public
    reviewer tool may legitimately operate on a local checkout.  The one
    explicitly approved session-feedback ledger is excluded by exact path, not
    by a broad skill-directory exception.  The optional third argument is
    retained for callers of the earlier helper signature and intentionally has
    no bearing on the complete-tree check.
    """

    approved_source_tex, source_tex_issues = approved_public_source_tex_paths(
        repo, candidate_ref
    )
    issues: list[str] = list(source_tex_issues)
    for path in sorted(
        _git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
    ):
        pure = PurePosixPath(path)
        if path in PUBLIC_CONTRIBUTOR_WORKFLOW_PATHS:
            continue
        is_human_skill_document = (
            path.startswith("skills/") and pure.suffix in {".md", ".txt", ".tex", ".json"}
        )
        is_root_reader_document = (
            len(pure.parts) == 1
            and pure.suffix.lower() in {".md", ".txt", ".tex", ".html", ".json"}
        )
        is_release_configuration = (
            path.startswith("config/")
            and pure.suffix.lower() in {".json", ".md", ".txt", ".toml"}
        )
        if not (
            path.startswith("papers/")
            or path.startswith("docs/")
            or path.startswith("site/")
            or is_human_skill_document
            or is_root_reader_document
            or is_release_configuration
        ):
            continue
        if path in approved_source_tex:
            continue
        try:
            raw = _git_bytes(repo, ["show", f"{candidate_ref}:{path}"])
            text = raw.decode("utf-8")
        except (RuntimeError, UnicodeDecodeError):
            continue
        if path.endswith(".json"):
            try:
                payload = json.loads(text)
            except json.JSONDecodeError:
                issues.append(f"{path}: public JSON artifact is not valid JSON")
                continue
            for route, label in _public_artifact_string_issues(
                _mask_json_source_tex_references(payload, approved_source_tex),
                relative_path=path,
            ):
                issues.append(f"{path}: {label} at {route}")
            continue
        if pure.name == ".gitignore":
            # Ignore patterns may intentionally name local source/cache
            # directories so they cannot be committed.  They are not public
            # provenance or reader-facing content; actual artifacts remain
            # forbidden by the independent path policy above.
            continue
        scan_text = _decoded_text_for_policy(
            _mask_approved_source_tex_references(text, approved_source_tex)
        )
        if path == "site/index.html":
            scan_text = scan_text.replace(
                PUBLIC_SITE_PRIVATE_WORKFLOW_GUIDANCE,
                PUBLIC_SITE_PRIVATE_WORKFLOW_SENTINEL,
            )
        if path == "README.md":
            scan_text = scan_text.replace(
                PUBLIC_README_PRIVATE_WORKFLOW_GUIDANCE,
                PUBLIC_SITE_PRIVATE_WORKFLOW_SENTINEL,
            )
        url_issue = _private_public_url_issue(scan_text)
        if url_issue is not None:
            issues.append(f"{path}: {url_issue}")
        scan_text = _PUBLIC_HTTP_URL_RE.sub("PUBLIC_HTTP_URL", scan_text)
        for label, pattern in PUBLIC_ARTIFACT_CONTENT_PATTERNS:
            if pure.suffix == ".lean" and label in {
                "non-public source transcript locator",
                "non-public source artifact locator",
            }:
                # Source filenames in checked Lean code are technical citation
                # locators, not redistributed source bytes or session history.
                # Preserve exact audited Lean blobs; actual source artifacts,
                # absolute local paths and private workflow prose still fail
                # their independent checks.
                continue
            if pattern.search(scan_text):
                issues.append(f"{path}: {label}")
    return issues


def human_review_packet_pdf_content_issues(
    repo: Path, candidate_ref: str = "HEAD"
) -> list[str]:
    """Scan every committed public PDF for the same private-workflow leaks.

    Rendered reports and dependency DAGs are independently downloadable from
    the public repository, so scanning only their TeX source is insufficient.
    The temporary files hold candidate Git blobs solely long enough for
    ``pdftotext`` to inspect them; no private source artifact is opened or
    regenerated here.
    """

    pdf_paths = sorted(
        path
        for path in _git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
        if path.lower().endswith(".pdf")
        and (
            path.startswith("papers/")
            or path.startswith("docs/")
            or path.startswith("site/")
            or "/" not in path
        )
    )
    if not pdf_paths:
        return []
    if shutil.which("pdftotext") is None:
        return [
            "cannot inspect committed public PDF text: pdftotext is unavailable"
        ]
    issues: list[str] = []
    for pdf_path in pdf_paths:
        try:
            pdf_bytes = _git_bytes(repo, ["show", f"{candidate_ref}:{pdf_path}"])
        except RuntimeError as exc:
            issues.append(f"{pdf_path}: cannot read committed public PDF: {exc}")
            continue
        with tempfile.TemporaryDirectory(prefix="econcslib-public-pdf-") as directory:
            temporary_directory = Path(directory)
            input_path = temporary_directory / "public.pdf"
            output_path = temporary_directory / "public.txt"
            input_path.write_bytes(pdf_bytes)
            try:
                result = subprocess.run(
                    ["pdftotext", "-enc", "UTF-8", str(input_path), str(output_path)],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    check=False,
                )
            except OSError as exc:
                issues.append(
                    f"{pdf_path}: cannot inspect committed public PDF with pdftotext: {exc}"
                )
                continue
            if result.returncode != 0:
                detail = result.stderr.strip() or result.stdout.strip() or "unknown failure"
                issues.append(
                    f"{pdf_path}: pdftotext failed while scanning committed public PDF: {detail}"
                )
                continue
            try:
                text = output_path.read_text(encoding="utf-8", errors="replace")
            except OSError as exc:
                issues.append(
                    f"{pdf_path}: pdftotext produced no readable text output: {exc}"
                )
                continue
        policy_text = _decoded_text_for_policy(text)
        url_issue = _private_public_url_issue(policy_text)
        if url_issue is not None:
            issues.append(f"{pdf_path}: {url_issue} in committed public PDF text")
        scan_text = _PUBLIC_HTTP_URL_RE.sub("PUBLIC_HTTP_URL", policy_text)
        for label, pattern in PUBLIC_ARTIFACT_CONTENT_PATTERNS:
            if (
                pdf_path in PUBLIC_CONTRIBUTOR_WORKFLOW_PDF_PATHS
                and label == "private workflow reference"
            ):
                continue
            if pattern.search(scan_text):
                issues.append(f"{pdf_path}: {label} in committed public PDF text")
    return sorted(set(issues))


def _status_string_leaves(
    value: object,
    route: tuple[str, ...] = (),
) -> list[tuple[tuple[str, ...], str]]:
    leaves: list[tuple[tuple[str, ...], str]] = []
    if isinstance(value, dict):
        for key, child in value.items():
            leaves.extend(_status_string_leaves(child, (*route, str(key))))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            leaves.extend(_status_string_leaves(child, (*route, str(index))))
    elif isinstance(value, str):
        leaves.append((route, value))
    return leaves


def _candidate_current_audit_artifacts(
    repo: Path,
    candidate_ref: str,
    candidate_paths: set[str],
) -> tuple[set[str], list[str]]:
    """Read present supplemental current-audit paths from candidate status fields.

    ``review_surface`` file fields are configured destinations.  Some lanes are
    conditional (for example, defect-support evidence is needed only when a
    quarantined defect is used as support), so a safe paper-local destination
    may legitimately be absent.  ``artifacts`` entries instead declare current
    outputs and remain required to exist.  In both sections, validate the path
    before testing presence so an absent unsafe or cross-paper route cannot be
    used to weaken the public artifact policy.
    """

    current: set[str] = set()
    issues: list[str] = []
    status_paths = sorted(
        path
        for path in candidate_paths
        if len(PurePosixPath(path).parts) == 3
        and PurePosixPath(path).parts[0] == "papers"
        and PurePosixPath(path).parts[2] == "status.json"
    )
    for status_path in status_paths:
        paper = PurePosixPath(status_path).parts[1]
        try:
            payload = json.loads(_git(repo, ["show", f"{candidate_ref}:{status_path}"]))
        except (RuntimeError, json.JSONDecodeError) as exc:
            issues.append(
                f"{status_path}: cannot derive current public audit artifacts: {exc}"
            )
            continue
        if not isinstance(payload, dict):
            issues.append(
                f"{status_path}: cannot derive current public audit artifacts from "
                "a non-object status"
            )
            continue
        expected_prefix = f"papers/{paper}/audit/"
        for section_name in ("artifacts", "review_surface"):
            section = payload.get(section_name)
            if section is None:
                continue
            if not isinstance(section, dict):
                issues.append(
                    f"{status_path}: {section_name} must be an object before it can "
                    "authorize current public audit artifacts"
                )
                continue
            for route, raw_path in _status_string_leaves(section):
                if "/audit/" not in raw_path or any(
                    character.isspace() for character in raw_path
                ):
                    continue
                normalized = _safe_relative_path(raw_path)
                route_text = ".".join((section_name, *route))
                if normalized is None or normalized != raw_path:
                    issues.append(
                        f"{status_path}: {route_text} has an unsafe or noncanonical "
                        f"current audit artifact path: {raw_path!r}"
                    )
                    continue
                if not normalized.startswith(expected_prefix):
                    issues.append(
                        f"{status_path}: {route_text} current audit artifact must stay "
                        f"beneath {expected_prefix}: {normalized}"
                    )
                    continue
                if normalized not in candidate_paths:
                    if section_name == "artifacts":
                        issues.append(
                            f"{status_path}: {route_text} declared current audit "
                            "artifact is absent from the exact candidate tree: "
                            f"{normalized}"
                        )
                    continue
                current.add(normalized)
    return current, issues


def _candidate_corrected_target_artifacts(
    repo: Path,
    candidate_ref: str,
    candidate_paths: set[str],
) -> tuple[set[str], list[str]]:
    """Validate public corrected targets while withholding approval records."""

    current: set[str] = set()
    issues: list[str] = []
    map_paths = sorted(
        path
        for path in candidate_paths
        if len(PurePosixPath(path).parts) == 4
        and PurePosixPath(path).parts[0] == "papers"
        and PurePosixPath(path).parts[2:] == ("audit", "paper_statement_map.json")
    )
    for map_path in map_paths:
        try:
            payload = json.loads(_git(repo, ["show", f"{candidate_ref}:{map_path}"]))
        except (RuntimeError, json.JSONDecodeError) as exc:
            issues.append(f"{map_path}: cannot read corrected-target artifacts: {exc}")
            continue
        items = payload.get("items", {}) if isinstance(payload, dict) else None
        if not isinstance(items, dict):
            issues.append(f"{map_path}: source-map items must be an object")
            continue
        corrected_targets: list[tuple[str, dict[str, object]]] = []
        for item_id, item in items.items():
            if not isinstance(item, dict):
                continue
            target = item.get("corrected_target")
            if target is None:
                if source_requires_approved_corrected_target(item):
                    issues.append(
                        f"{map_path}: {item_id} corrected_source_statement has no "
                        "corrected_target"
                    )
                continue
            if not isinstance(target, dict):
                issues.append(f"{map_path}: {item_id} corrected_target is malformed")
                continue
            corrected_targets.append((str(item_id), target))

        marker = payload.get(PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD)
        if not corrected_targets:
            if marker is not None:
                issues.append(
                    f"{map_path}: corrected-target projection marker has no corrected targets"
                )
            continue
        expected_marker = {
            "schema": PUBLIC_CORRECTED_TARGET_PROJECTION_SCHEMA,
            "approval_material_included": False,
        }
        if marker != expected_marker:
            issues.append(
                f"{map_path}: corrected targets require the exact public projection marker"
            )

        for item_id, target in corrected_targets:
            label = f"{map_path}: {item_id} corrected_target"
            if "approval" in target:
                issues.append(f"{label} exposes private approval material")
                continue
            if target.get("schema") != 1:
                issues.append(f"{label} must use schema 1")
                continue
            if target.get("archival_equivalence_claimed") is not False:
                issues.append(f"{label} must declare archival_equivalence_claimed=false")
                continue
            statement = target.get("statement")
            if not isinstance(statement, str) or not statement.strip():
                issues.append(f"{label} has no mathematical statement")
                continue
            record_digest = target.get(CORRECTED_TARGET_RECORD_SHA256_FIELD)
            if not isinstance(record_digest, str) or not SHA256_RE.fullmatch(record_digest):
                issues.append(
                    f"{label} has no valid retained {CORRECTED_TARGET_RECORD_SHA256_FIELD}"
                )
            review_digest = target.get(CORRECTED_TARGET_REVIEW_SHA256_FIELD)
            if (
                not isinstance(review_digest, str)
                or not SHA256_RE.fullmatch(review_digest)
                or review_digest != corrected_target_review_digest(target)
            ):
                issues.append(
                    f"{label} has a stale or malformed retained "
                    f"{CORRECTED_TARGET_REVIEW_SHA256_FIELD}"
                )
    return current, issues


def _candidate_accepted_graph_artifacts(
    repo: Path,
    candidate_ref: str,
    candidate_paths: set[str],
) -> tuple[set[str], list[str]]:
    """Retain only the selected graph and its authenticated build-input preimage.

    The store owner validates canonical graph/leaf identities from exact candidate
    blobs. This selects transport artifacts; it does not grant paper acceptance.
    """

    try:
        from scripts.final_closure_receipt import load_final_closure_receipt
        from scripts.obligation_closure_credential import (
            recorded_accepted_graph_lean_import_closure_sha256,
        )
        from scripts.obligation_evidence_store import load_lean_import_closure_preimage
    except ModuleNotFoundError:  # Direct script execution.
        from final_closure_receipt import load_final_closure_receipt
        from obligation_closure_credential import recorded_accepted_graph_lean_import_closure_sha256
        from obligation_evidence_store import load_lean_import_closure_preimage

    selected: set[str] = set()
    issues: list[str] = []
    pointers = sorted(
        path for path in candidate_paths
        if len(PurePosixPath(path).parts) == 5
        and PurePosixPath(path).parts[0] == "papers"
        and PurePosixPath(path).parts[2:] == (
            "audit", "obligation_evidence", "current_accepted_graph.json"
        )
    )
    with tempfile.TemporaryDirectory(prefix="selected-graph-artifacts-") as temporary:
        snapshot = Path(temporary)

        def copy_exact(path: str) -> bytes:
            if path not in candidate_paths:
                raise ValueError("selected artifact is absent from the exact candidate tree: " + path)
            raw = _git_bytes(repo, ["show", f"{candidate_ref}:{path}"])
            target = snapshot / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
            return raw

        for pointer in pointers:
            paper = PurePosixPath(pointer).parts[1]
            try:
                selection = json.loads(copy_exact(pointer))
                if not isinstance(selection, dict) or selection.get("schema") != 2:
                    raise ValueError("selected public graph must use the packed schema-2 pointer")
                digest = selection.get("graph_sha256")
                if not isinstance(digest, str) or not SHA256_RE.fullmatch(digest):
                    raise ValueError("selected graph digest is malformed")
                base = f"papers/{paper}/audit/obligation_evidence"
                pack = f"{base}/accepted_graphs/sha256/{digest[:2]}/{digest}.json"
                copy_exact(pack)
                copy_exact(f"papers/{paper}/FINAL_CLOSURE_RECEIPT.md")
                receipt = load_final_closure_receipt(snapshot, paper)
                closure_digest = recorded_accepted_graph_lean_import_closure_sha256(
                    snapshot, paper, receipt.payload
                )
                preimage = (
                    f"{base}/lean_import_closures/sha256/"
                    f"{closure_digest[:2]}/{closure_digest}.json"
                )
                copy_exact(preimage)
                load_lean_import_closure_preimage(snapshot, paper, closure_digest)
            except (ValueError, RuntimeError, OSError) as exc:
                issues.append(f"{pointer}: cannot select current graph artifacts: {exc}")
                continue
            selected.update((pointer, pack, preimage))
    return selected, issues


def _candidate_registered_engine_protocols(
    repo: Path,
    candidate_ref: str,
) -> dict[str, frozenset[str]]:
    """Return the validated public engine-to-protocol registration relation."""

    try:
        payload = json.loads(
            _git(
                repo,
                [
                    "show",
                    f"{candidate_ref}:config/formalization_engine_revisions.json",
                ],
            )
        )
    except (RuntimeError, json.JSONDecodeError) as exc:
        raise EngineRevisionError(
            f"public engine registration ledger is unreadable: {exc}"
        ) from exc
    revisions = payload.get("revisions") if isinstance(payload, dict) else None
    tip = revisions[-1] if isinstance(revisions, list) and revisions else None
    if not isinstance(tip, dict):
        raise EngineRevisionError(
            "public engine registration ledger has no recorded issuer"
        )
    validated = validate_revision_ledger(
        payload,
        current_engine_sha256=str(tip.get("engine_tree_sha256") or ""),
        current_protocol_sha256=str(
            tip.get("formalization_review_protocol_sha256") or ""
        ),
    )
    relation: dict[str, set[str]] = {}
    for revision in validated["revisions"]:
        relation.setdefault(revision["engine_tree_sha256"], set()).add(
            revision["formalization_review_protocol_sha256"]
        )
    return {
        engine: frozenset(protocols)
        for engine, protocols in relation.items()
    }


def selected_graph_authority_registration_issues(
    repo: Path,
    candidate_ref: str,
) -> list[str]:
    """Require every selected strict engine to have one public protocol row."""

    candidate_paths = {
        path
        for path in _git(
            repo,
            ["ls-tree", "-r", "--name-only", "-z", candidate_ref],
        ).split("\0")
        if path
    }
    pointers = sorted(
        path
        for path in candidate_paths
        if len(PurePosixPath(path).parts) == 5
        and PurePosixPath(path).parts[0] == "papers"
        and PurePosixPath(path).parts[2:] == (
            "audit", "obligation_evidence", "current_accepted_graph.json"
        )
    )
    if not pointers:
        return []
    try:
        registrations = _candidate_registered_engine_protocols(
            repo, candidate_ref
        )
    except EngineRevisionError as exc:
        return [
            "selected graph authority registrations cannot be validated: "
            + str(exc)
        ]
    issues: list[str] = []
    for pointer_path in pointers:
        paper = PurePosixPath(pointer_path).parts[1]
        try:
            pointer = json.loads(
                _git(repo, ["show", f"{candidate_ref}:{pointer_path}"])
            )
            if not isinstance(pointer, dict):
                raise ValueError("selected graph pointer is malformed")
            graph_sha256 = pointer.get("graph_sha256")
            if (
                pointer.get("schema") != 2
                or not isinstance(graph_sha256, str)
                or not SHA256_RE.fullmatch(graph_sha256)
            ):
                raise ValueError("selected graph pointer is malformed")
            base = f"papers/{paper}/audit/obligation_evidence"
            pack_path = (
                f"{base}/accepted_graphs/sha256/{graph_sha256[:2]}/"
                f"{graph_sha256}.json"
            )
            pack = json.loads(
                _git(repo, ["show", f"{candidate_ref}:{pack_path}"])
            )
            leaves = pack.get("leaves") if isinstance(pack, dict) else None
            closures = [
                leaf
                for leaf in (leaves.values() if isinstance(leaves, dict) else [])
                if isinstance(leaf, dict) and leaf.get("kind") == "paper_closure"
            ]
            if len(closures) != 1:
                raise ValueError(
                    "selected graph has no unique paper-closure strict authority"
                )
            closure_payload = closures[0].get("semantic_payload")
            authority = recorded_strict_closeout_authority(
                closure_payload.get("strict_closeout_authority")
                if isinstance(closure_payload, dict)
                else None
            )
            if authority.paper != paper:
                raise ValueError(
                    "selected graph strict authority belongs to another paper"
                )
        except (
            RuntimeError,
            json.JSONDecodeError,
            ValueError,
            StrictCloseoutAuthorityError,
        ) as exc:
            issues.append(
                f"{pointer_path}: cannot validate selected strict authority: {exc}"
            )
            continue
        protocols = registrations.get(authority.engine_tree_sha256, frozenset())
        if not protocols:
            issues.append(
                f"{pointer_path}: selected strict authority engine "
                f"{authority.engine_tree_sha256} has no public engine/protocol "
                "registration"
            )
        elif len(protocols) != 1:
            issues.append(
                f"{pointer_path}: selected strict authority engine "
                f"{authority.engine_tree_sha256} has ambiguous public protocol "
                "registrations"
            )
    return issues


def _candidate_receipt_review_ledgers(
    repo: Path,
    candidate_ref: str,
    candidate_paths: set[str],
) -> tuple[set[str], list[str]]:
    """Read receipt-bound current audit ledgers from the exact candidate tree.

    A direct source-row review is an accepted closeout lane.  Its compact JSON
    ledger is canonical when, and only when, the paper's final closure receipt
    binds that exact paper-local audit path.  Do not require a duplicate status
    field merely to make the public artifact policy recognize this evidence.
    """

    current: set[str] = set()
    issues: list[str] = []
    receipt_paths = sorted(
        path
        for path in candidate_paths
        if len(PurePosixPath(path).parts) == 3
        and PurePosixPath(path).parts[0] == "papers"
        and PurePosixPath(path).parts[2] == "FINAL_CLOSURE_RECEIPT.md"
    )
    for receipt_path in receipt_paths:
        paper = PurePosixPath(receipt_path).parts[1]
        try:
            text = _git(repo, ["show", f"{candidate_ref}:{receipt_path}"])
        except RuntimeError as exc:
            issues.append(f"{receipt_path}: cannot read receipt-bound audit ledger: {exc}")
            continue
        match = re.search(
            r"(?ms)^\[review_ledger\]\s*\npath\s*=\s*\"([^\"]+)\"",
            text,
        )
        if match is None:
            continue
        raw_path = match.group(1)
        normalized = _safe_relative_path(raw_path)
        expected_prefix = f"papers/{paper}/audit/"
        if normalized is None or normalized != raw_path:
            issues.append(
                f"{receipt_path}: review_ledger.path has an unsafe or noncanonical "
                f"audit path: {raw_path!r}"
            )
            continue
        if not normalized.startswith(expected_prefix):
            issues.append(
                f"{receipt_path}: review_ledger.path must stay beneath "
                f"{expected_prefix}: {normalized}"
            )
            continue
        if normalized not in candidate_paths:
            issues.append(
                f"{receipt_path}: receipt-bound current audit artifact is absent from "
                f"the exact candidate tree: {normalized}"
            )
            continue
        current.add(normalized)
    return current, issues


def candidate_public_artifact_policy_issues(
    repo: Path,
    candidate_ref: str = "HEAD",
) -> list[str]:
    """Apply public artifact hygiene to every path in the exact candidate tree."""

    candidate_paths = set(
        _git(repo, ["ls-tree", "-r", "--name-only", candidate_ref]).splitlines()
    )
    current_audit_artifacts, issues = _candidate_current_audit_artifacts(
        repo,
        candidate_ref,
        candidate_paths,
    )
    # This exact non-accepting envelope is validated independently against the
    # selected accepted graph, display manifest, public map, and pinned private
    # projection. It is the only new audit filename admitted by this guard.
    current_audit_artifacts.update(
        path
        for path in candidate_paths
        if len(PurePosixPath(path).parts) == 4
        and PurePosixPath(path).parts[0] == "papers"
        and PurePosixPath(path).parts[2:] == (
            "audit",
            PurePosixPath(PUBLIC_SOURCE_ROLE_PROJECTION_FILE).name,
        )
    )
    receipt_ledgers, receipt_issues = _candidate_receipt_review_ledgers(
        repo,
        candidate_ref,
        candidate_paths,
    )
    current_audit_artifacts.update(receipt_ledgers)
    issues.extend(receipt_issues)
    target_artifacts, target_issues = _candidate_corrected_target_artifacts(
        repo, candidate_ref, candidate_paths
    )
    current_audit_artifacts.update(target_artifacts)
    issues.extend(target_issues)
    graph_artifacts, graph_issues = _candidate_accepted_graph_artifacts(
        repo, candidate_ref, candidate_paths
    )
    current_audit_artifacts.update(graph_artifacts)
    issues.extend(graph_issues)
    public_source_artifacts, public_source_issues = public_arxiv_tex_artifact_paths(
        repo, candidate_ref
    )
    issues.extend(public_source_issues)
    try:
        issues.extend(
            public_release_artifact_issues(
                candidate_paths,
                current_audit_artifacts=current_audit_artifacts,
                public_source_artifacts=public_source_artifacts,
            )
        )
    except ValueError as exc:
        issues.append(f"public artifact policy configuration is invalid: {exc}")
    return issues


def changes_between(repo: Path, old_ref: str, new_ref: str) -> list[CandidateChange]:
    raw = _git(
        repo,
        [
            "diff",
            "--name-status",
            "--no-renames",
            "-z",
            "--diff-filter=ACDMT",
            old_ref,
            new_ref,
        ],
    )
    parts = [part for part in raw.split("\0") if part]
    if len(parts) % 2:
        raise RuntimeError("git name-status output was malformed")
    return sorted(
        (
            CandidateChange(parts[index][0], parts[index + 1])
            for index in range(0, len(parts), 2)
        ),
        key=lambda change: change.path,
    )


def candidate_changes(
    repo: Path, base_ref: str, candidate_ref: str
) -> list[CandidateChange]:
    """Return the final-tree delta; history validation uses ``candidate_history``."""

    return changes_between(repo, base_ref, candidate_ref)


def candidate_history(
    repo: Path, base_ref: str, candidate_ref: str
) -> tuple[list[CandidateCommit], list[str]]:
    """Return the single squashed release commit rooted at the exact public base.

    Net-tree validation cannot make a branch safe to push: a private merge or an
    add-then-delete commit still publishes the intermediate commits and blobs.
    The public candidate therefore consists of exactly one inspected commit
    whose sole parent is the exact base. Merges, stacked commits, private HEAD,
    and add-then-delete histories all fail closed.
    """

    base = resolved_commit(repo, base_ref)
    candidate = resolved_commit(repo, candidate_ref)
    ancestor = subprocess.run(
        ["git", "merge-base", "--is-ancestor", base, candidate],
        cwd=repo,
        env=_git_environment(),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    if ancestor.returncode != 0:
        return [], [f"candidate {candidate_ref} is not based on exact public base {base_ref}"]

    commits = [
        line.strip()
        for line in _git(repo, ["rev-list", "--reverse", f"{base}..{candidate}"]).splitlines()
        if line.strip()
    ]
    history: list[CandidateCommit] = []
    issues: list[str] = []
    if len(commits) != 1:
        issues.append(
            "public release candidate must be exactly one squashed commit whose parent "
            f"is the exact public base; found {len(commits)} candidate commit(s)"
        )
    expected_parent = base
    for commit in commits:
        parent_line = _git(repo, ["rev-list", "--parents", "-n", "1", commit]).split()
        if not parent_line or parent_line[0] != commit:
            issues.append(f"cannot resolve candidate commit parents: {commit}")
            continue
        parents = parent_line[1:]
        if len(parents) != 1:
            issues.append(
                f"candidate history must be linear and merge-free: {commit} has "
                f"{len(parents)} parent(s)"
            )
            continue
        parent = parents[0]
        if parent != expected_parent:
            issues.append(
                f"candidate history is not one linear chain from exact public base: "
                f"{commit} has parent {parent}, expected {expected_parent}"
            )
        history.append(
            CandidateCommit(
                commit=commit,
                parent=parent,
                changes=tuple(changes_between(repo, parent, commit)),
            )
        )
        expected_parent = commit
    if expected_parent != candidate:
        issues.append(
            "candidate history could not be traversed as one linear chain from the exact public base"
        )
    return history, issues


def _candidate_uses_public_source_display_marker(path: str, blob: bytes) -> bool:
    """Return whether a projected source map opted into the display marker.

    The marker is intentionally opt-in: papers without a current private
    display manifest retain their ordinary strict public projection.  A
    malformed candidate map simply returns ``False`` here; the exact
    projection comparison and the JSON/marker guard then report the failure.
    """

    if not path.endswith("/audit/paper_statement_map.json"):
        return False
    try:
        payload = json.loads(blob.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return False
    return isinstance(payload, dict) and PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD in payload


def _candidate_uses_corrected_target_projection_marker(path: str, blob: bytes) -> bool:
    """Whether an exact public source map declares approval-material redaction."""

    pure = PurePosixPath(path)
    if not (
        len(pure.parts) == 4
        and pure.parts[0] == "papers"
        and pure.parts[2:] == ("audit", "paper_statement_map.json")
    ):
        return False
    try:
        payload = json.loads(blob.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return False
    return (
        isinstance(payload, dict)
        and PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD in payload
    )


def source_provenance_issues(
    candidate_repo: Path,
    private_repo: Path,
    candidate_ref: str,
    changes: list[CandidateChange],
    entries: list[AllowlistEntry],
    *,
    public_base_ref: str = PUBLIC_BASE_REF,
) -> list[str]:
    """Bind each non-generated change to its exact reviewed source bytes."""

    issues: list[str] = []
    for change in changes:
        entry = matching_allowlist_entry(change.path, entries)
        pure_change_path = PurePosixPath(change.path)
        is_statement_map = (
            len(pure_change_path.parts) == 4
            and pure_change_path.parts[0] == "papers"
            and pure_change_path.parts[2:] == ("audit", "paper_statement_map.json")
        )
        if change.status != "D" and is_statement_map:
            try:
                candidate_blob_for_marker = _git_bytes(
                    candidate_repo, ["show", f"{candidate_ref}:{change.path}"]
                )
            except RuntimeError:
                candidate_blob_for_marker = b""
            if _candidate_uses_corrected_target_projection_marker(
                change.path, candidate_blob_for_marker
            ) and (entry is None or entry.provenance != "private_projection"):
                issues.append(
                    f"{change.path}: changed corrected-target projection requires "
                    "private_projection provenance"
                )
        if entry is None:
            continue
        if change.status == "D":
            if entry.provenance != "public_base_deletion":
                issues.append(
                    f"deleted path needs public_base_deletion provenance: {change.path}"
                )
            continue
        if entry.provenance == "public_base_deletion":
            issues.append(
                f"non-deleted path cannot use public_base_deletion provenance: {change.path}"
            )
            continue
        if entry.provenance == "public_generated":
            continue
        if entry.provenance == "public_base_addition":
            if change.status != "A":
                issues.append(
                    f"public_base_addition path must be an addition, not status "
                    f"{change.status}: {change.path}"
                )
            try:
                base_entry = _tree_entry(candidate_repo, public_base_ref, change.path)
                candidate_entry = _tree_entry(
                    candidate_repo, candidate_ref, change.path
                )
                candidate_blob = _git_bytes(
                    candidate_repo, ["show", f"{candidate_ref}:{change.path}"]
                )
            except RuntimeError as exc:
                issues.append(
                    f"{change.path}: cannot verify pinned public-base addition: {exc}"
                )
                continue
            if base_entry is not None:
                issues.append(
                    f"{change.path}: public_base_addition requires the path to be "
                    "absent from the public base"
                )
            if candidate_entry is None or candidate_entry.object_type != "blob":
                issues.append(
                    f"{change.path}: public_base_addition requires a candidate blob"
                )
            if _sha256_bytes(candidate_blob) != entry.candidate_blob_sha256:
                issues.append(
                    f"{change.path}: candidate blob does not match allowlisted "
                    "candidate_blob_sha256"
                )
            for source_commit in sorted(
                {
                    item.source_commit
                    for item in entries
                    if item.provenance in {"private_blob", "private_projection"}
                    and item.source_commit is not None
                }
            ):
                try:
                    source_entry = _tree_entry(
                        private_repo, source_commit, change.path
                    )
                    if source_entry is None:
                        continue
                    source_blob = _git_bytes(
                        private_repo, ["show", f"{source_commit}:{change.path}"]
                    )
                except RuntimeError as exc:
                    issues.append(
                        f"{change.path}: cannot check public-only addition against "
                        f"reviewed private source commit {source_commit}: {exc}"
                    )
                    continue
                if (
                    candidate_entry is not None
                    and candidate_entry.mode == source_entry.mode
                    and candidate_entry.object_type == source_entry.object_type
                    and candidate_blob == source_blob
                ):
                    issues.append(
                        f"{change.path}: byte-identical candidate content already "
                        f"exists at reviewed private source commit {source_commit}; "
                        "use private_blob provenance"
                    )
            continue
        if entry.provenance == "public_base_edit":
            if change.status != "M":
                issues.append(
                    f"public_base_edit path must be an in-place modification, not "
                    f"status {change.status}: {change.path}"
                )
            try:
                base_entry = _tree_entry(candidate_repo, public_base_ref, change.path)
                candidate_entry = _tree_entry(
                    candidate_repo, candidate_ref, change.path
                )
                base_blob = _git_bytes(
                    candidate_repo, ["show", f"{public_base_ref}:{change.path}"]
                )
                candidate_blob = _git_bytes(
                    candidate_repo, ["show", f"{candidate_ref}:{change.path}"]
                )
            except RuntimeError as exc:
                issues.append(
                    f"{change.path}: cannot verify pinned public-base edit: {exc}"
                )
                continue
            if base_entry is None or candidate_entry is None:
                issues.append(
                    f"{change.path}: public_base_edit requires the path to exist in "
                    "both the public base and candidate"
                )
                continue
            if (
                base_entry.object_type != "blob"
                or candidate_entry.object_type != "blob"
                or base_entry.mode != candidate_entry.mode
            ):
                issues.append(
                    f"{change.path}: public_base_edit cannot change Git mode or object type"
                )
            actual_base_sha256 = _sha256_bytes(base_blob)
            actual_candidate_sha256 = _sha256_bytes(candidate_blob)
            if actual_base_sha256 != entry.public_base_blob_sha256:
                issues.append(
                    f"{change.path}: public base blob does not match allowlisted "
                    "public_base_blob_sha256"
                )
            if actual_candidate_sha256 != entry.candidate_blob_sha256:
                issues.append(
                    f"{change.path}: candidate blob does not match allowlisted "
                    "candidate_blob_sha256"
                )
            continue
        if entry.provenance == "private_projection":
            try:
                candidate_entry = _tree_entry(candidate_repo, candidate_ref, change.path)
                source_entry = _tree_entry(private_repo, entry.source_commit or "", change.path)
                candidate_blob = _git_bytes(
                    candidate_repo, ["show", f"{candidate_ref}:{change.path}"]
                )
                source_blob = _git_bytes(
                    private_repo, ["show", f"{entry.source_commit}:{change.path}"]
                )
            except RuntimeError as exc:
                issues.append(
                    f"{change.path}: cannot verify private projection provenance: {exc}"
                )
                continue
            if candidate_entry is None or source_entry is None:
                issues.append(
                    f"{change.path}: candidate or private source tree entry is missing"
                )
                continue
            if (
                candidate_entry.mode != source_entry.mode
                or candidate_entry.object_type != source_entry.object_type
            ):
                issues.append(
                    f"{change.path}: candidate Git mode/type differs from private source "
                    f"commit {entry.source_commit}"
                )
            actual_source_sha256 = _sha256_bytes(source_blob)
            actual_candidate_sha256 = _sha256_bytes(candidate_blob)
            if actual_source_sha256 != entry.private_source_blob_sha256:
                issues.append(
                    f"{change.path}: private source blob does not match allowlisted "
                    "private_source_blob_sha256"
                )
            if actual_candidate_sha256 != entry.candidate_blob_sha256:
                issues.append(
                    f"{change.path}: candidate blob does not match allowlisted "
                    "candidate_blob_sha256"
                )
            try:
                projected_blob = project_bytes(
                    change.path,
                    source_blob,
                    include_source_display_marker=_candidate_uses_public_source_display_marker(
                        change.path, candidate_blob
                    ),
                )
            except ProjectionError as exc:
                issues.append(
                    f"{change.path}: trusted public projection failed: {exc}"
                )
                continue
            if projected_blob == source_blob:
                issues.append(
                    f"{change.path}: public projection did not change the private blob; "
                    "use private_blob provenance"
                )
            if candidate_blob != projected_blob:
                issues.append(
                    f"{change.path}: candidate blob does not equal the trusted public "
                    "projection of its private source"
                )
            continue
        assert entry.source_commit is not None
        try:
            candidate_entry = _tree_entry(candidate_repo, candidate_ref, change.path)
            source_entry = _tree_entry(private_repo, entry.source_commit, change.path)
            candidate_blob = _git_bytes(
                candidate_repo, ["show", f"{candidate_ref}:{change.path}"]
            )
            source_blob = _git_bytes(
                private_repo, ["show", f"{entry.source_commit}:{change.path}"]
            )
        except RuntimeError as exc:
            issues.append(f"{change.path}: cannot verify private blob provenance: {exc}")
            continue
        if candidate_entry is None or source_entry is None:
            issues.append(
                f"{change.path}: candidate or private source tree entry is missing"
            )
            continue
        if (
            candidate_entry.mode != source_entry.mode
            or candidate_entry.object_type != source_entry.object_type
        ):
            issues.append(
                f"{change.path}: candidate Git mode/type differs from private source commit "
                f"{entry.source_commit}"
            )
        if candidate_blob != source_blob:
            issues.append(
                f"{change.path}: candidate blob differs from private source commit "
                f"{entry.source_commit}"
            )
    return issues


def candidate_tree_entry_issues(
    candidate_repo: Path,
    candidate_ref: str,
    changes: list[CandidateChange],
) -> list[str]:
    """Reject non-regular candidate entries regardless of private provenance."""

    issues: list[str] = []
    for change in changes:
        if change.status == "D":
            continue
        try:
            entry = _tree_entry(candidate_repo, candidate_ref, change.path)
        except RuntimeError as exc:
            issues.append(f"{change.path}: cannot inspect candidate tree entry: {exc}")
            continue
        if entry is None:
            issues.append(f"{change.path}: candidate tree entry is missing")
            continue
        if entry.object_type != "blob" or entry.mode not in {"100644", "100755"}:
            issues.append(
                f"{change.path}: public candidate must contain a regular file blob, "
                f"got mode/type {entry.mode}/{entry.object_type}"
            )
        elif change.path in GENERATED_PUBLIC_STATUS_PATHS and entry.mode != "100644":
            issues.append(
                f"{change.path}: generated public status file must use mode 100644"
            )
    return issues


def private_source_commit_issues(
    private_repo: Path,
    entries: list[AllowlistEntry],
    *,
    private_base_ref: str = PRIVATE_BASE_REF,
) -> list[str]:
    issues: list[str] = []
    checked: set[str] = set()
    for entry in entries:
        if entry.provenance not in {"private_blob", "private_projection"} or entry.source_commit is None:
            continue
        if entry.source_commit in checked:
            continue
        checked.add(entry.source_commit)
        exists = subprocess.run(
            ["git", "cat-file", "-e", f"{entry.source_commit}^{{commit}}"],
            cwd=private_repo,
            env=_git_environment(),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        if exists.returncode != 0:
            issues.append(f"private source commit does not exist: {entry.source_commit}")
            continue
        reachable = subprocess.run(
            [
                "git",
                "merge-base",
                "--is-ancestor",
                entry.source_commit,
                private_base_ref,
            ],
            cwd=private_repo,
            env=_git_environment(),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        if reachable.returncode != 0:
            issues.append(
                f"private source commit is not reachable from canonical "
                f"{private_base_ref}: {entry.source_commit}"
            )
    return issues


def generated_status_freshness_issues(
    candidate_repo: Path, candidate_ref: str = "HEAD"
) -> list[str]:
    """Run the trusted status generator against only the committed candidate tree."""

    if not TRUSTED_STATUS_SYNC.is_file():
        return [f"trusted status generator is missing: {TRUSTED_STATUS_SYNC}"]
    candidate_repo = candidate_repo.resolve()
    with tempfile.TemporaryDirectory(prefix="econcslib-public-tree-") as temp_dir:
        tree_checkout = Path(temp_dir) / "candidate"
        checkout = subprocess.run(
            [
                "git",
                "worktree",
                "add",
                "--detach",
                str(tree_checkout),
                candidate_ref,
            ],
            cwd=candidate_repo,
            env=_git_environment(),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
        if checkout.returncode != 0:
            return [
                "could not materialize a tree-only public status checkout: "
                + checkout.stdout.strip()
            ]
        try:
            environment = _git_environment()
            environment["APPLIEDMODELINGLIB_REPO_ROOT"] = str(tree_checkout.resolve())
            trusted_status_sync = TRUSTED_STATUS_SYNC.resolve()
            isolated_bootstrap = (
                "import runpy, sys; "
                f"sys.path.insert(0, {str(trusted_status_sync.parent)!r}); "
                f"runpy.run_path({str(trusted_status_sync)!r}, run_name='__main__')"
            )
            result = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-c",
                    isolated_bootstrap,
                    "--repo",
                    str(tree_checkout),
                    "--check",
                ],
                cwd=tree_checkout,
                env=environment,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                check=False,
            )
        finally:
            subprocess.run(
                ["git", "worktree", "remove", "--force", str(tree_checkout)],
                cwd=candidate_repo,
                env=_git_environment(),
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                check=False,
            )
    if result.returncode == 0:
        return []
    return [
        "public status surfaces are not reproducible from the candidate inputs "
        "using the trusted private generator: "
        + result.stdout.strip()
    ]


def _candidate_explicit_lake_srcdir_modules(
    repo: Path,
    candidate_commit: str,
) -> dict[str, str]:
    """Resolve explicit Lake roots whose modules live below a custom srcDir.

    The shared dependency scanner owns ordinary root and ``papers`` modules.
    This projection adds only modules beneath an explicitly configured
    non-root ``srcDir`` and an explicit ``roots`` entry. Missing, malformed,
    or ambiguous configuration therefore grants no repository ownership.
    """

    try:
        lake = tomllib.loads(
            _git(repo, ["show", f"{candidate_commit}:lakefile.toml"])
        )
        candidate_paths = {
            path
            for path in _git(
                repo,
                ["ls-tree", "-r", "--name-only", "-z", candidate_commit],
            ).split("\0")
            if path
        }
    except (RuntimeError, UnicodeError, tomllib.TOMLDecodeError):
        return {}
    libraries = lake.get("lean_lib") if isinstance(lake, dict) else None
    if not isinstance(libraries, list):
        return {}

    candidates: dict[str, list[str]] = {}
    for library in libraries:
        if not isinstance(library, dict):
            continue
        library_name = library.get("name")
        src_dir = _safe_relative_path(library.get("srcDir"))
        roots = library.get("roots")
        if (
            not isinstance(library_name, str)
            or not re.fullmatch(
                r"[A-Za-z_][A-Za-z0-9_']*", library_name.strip()
            )
            or src_dir is None
            or not isinstance(roots, list)
            or not roots
        ):
            continue
        src_path = PurePosixPath(src_dir)
        root_modules = [
            root.strip() if isinstance(root, str) else ""
            for root in roots
        ]
        if (
            any(
                not re.fullmatch(
                    r"[A-Za-z_][A-Za-z0-9_']*"
                    r"(?:\.[A-Za-z_][A-Za-z0-9_']*)*",
                    root,
                )
                for root in root_modules
            )
            or len(root_modules) != len(set(root_modules))
        ):
            continue
        for path in candidate_paths:
            pure = PurePosixPath(path)
            if pure.suffix != ".lean":
                continue
            try:
                relative = pure.relative_to(src_path).with_suffix("")
            except ValueError:
                continue
            module = ".".join(relative.parts)
            if any(
                module == root or module.startswith(root + ".")
                for root in root_modules
            ):
                candidates.setdefault(module, []).append(path)
    return {
        module: paths[0]
        for module, paths in candidates.items()
        if len(paths) == 1
    }


def public_paper_target_issues(repo: Path, candidate_commit: str) -> list[str]:
    """Require every registered paper root in the exact exported Git tree."""

    try:
        lake = tomllib.loads(_git(repo, ["show", f"{candidate_commit}:lakefile.toml"]))
    except (RuntimeError, UnicodeError, tomllib.TOMLDecodeError) as exc:
        return [f"public Lake configuration is unavailable or malformed: {exc}"]
    paths = set(_git(repo, ["ls-tree", "-r", "--name-only", candidate_commit]).splitlines())
    issues: list[str] = []
    for library in lake.get("lean_lib", []):
        if not isinstance(library, dict) or library.get("srcDir") != "papers":
            continue
        name = library.get("name")
        roots = library.get("roots", [name])
        if not isinstance(roots, list):
            issues.append(f"public paper target {name}: roots must be a list")
            continue
        for root in roots:
            if not isinstance(root, str) or not re.fullmatch(
                r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", root
            ):
                issues.append(f"public paper target {name}: malformed root {root!r}")
                continue
            path = "papers/" + root.replace(".", "/") + ".lean"
            if path not in paths:
                issues.append(f"public paper target {name}: registered root is not exported: {path}")
    return issues


def _public_candidate_dependency_closure_issues(
    repo: Path,
    candidate_commit: str,
    *,
    extra_entrypoints: set[str],
) -> list[ImportClosureIssue]:
    """Run the shared closure check with explicit custom-srcDir Lake roots."""

    registered_modules = _candidate_explicit_lake_srcdir_modules(
        repo, candidate_commit
    )
    issues = dependency_closure_issues(
        repo,
        candidate="tree",
        treeish=candidate_commit,
        extra_entrypoints={
            *extra_entrypoints,
            *registered_modules.values(),
        },
    )
    return [
        issue
        for issue in issues
        if not (
            issue.imported_module in registered_modules
            and not issue.dependency_path
            and issue.reason
            == "import prefix is neither repository-owned nor in the explicit "
            "external-module registry"
        )
    ]


def run_guard(
    repo: Path,
    *,
    allowlist_path: Path,
    authoritative: bool = False,
) -> list[str]:
    repo = repo.resolve()
    private_repo = ROOT.resolve()
    allowlist_path = allowlist_path.resolve()
    approval_path = REVIEWER_APPROVAL_PATH.absolute()
    approval_location = approval_path.parent.resolve() / approval_path.name
    issues: list[str] = []

    if _path_is_within(allowlist_path, repo):
        return [
            "public export allowlist must remain outside the candidate "
            f"repository: {allowlist_path}"
        ]
    approval: ReleaseApproval | None = None
    if authoritative:
        if _path_is_within(approval_location, repo) or _path_is_within(
            approval_location, private_repo
        ):
            return [
                "fixed reviewer approval must remain outside both agent-writable "
                f"repositories: {approval_location}"
            ]
        try:
            approval = load_release_approval(approval_path)
        except ValueError as exc:
            return [str(exc)]
    try:
        allowlist_bytes = allowlist_path.read_bytes()
    except OSError as exc:
        return [f"cannot read public export allowlist {allowlist_path}: {exc}"]
    try:
        entries = parse_allowlist(allowlist_bytes, source=str(allowlist_path))
    except ValueError as exc:
        return [str(exc)]

    if not is_git_repository(repo):
        return [f"public release workspace is not a Git repository: {repo}"]
    if not is_git_repository(private_repo):
        return [f"canonical private ROOT is not a Git repository: {private_repo}"]

    issues.extend(
        canonical_remote_issues(
            repo,
            remote=PUBLIC_REMOTE,
            expected=PUBLIC_REMOTE_RE,
            label="public",
        )
    )
    issues.extend(
        canonical_remote_issues(
            private_repo,
            remote=PRIVATE_REMOTE,
            expected=PRIVATE_REMOTE_RE,
            label="private",
        )
    )
    issues.extend(shared_git_storage_issues(repo, private_repo))

    try:
        trusted_tooling_sha256 = _trusted_tooling_sha256()
    except RuntimeError as exc:
        return [*issues, str(exc)]
    if approval is not None:
        if _sha256_bytes(allowlist_bytes) != approval.allowlist_sha256:
            issues.append(
                "public export allowlist bytes do not match the fixed reviewer approval"
            )
        if _guard_sha256() != approval.guard_sha256:
            issues.append(
                "executed release guard does not match the reviewer-approved SHA256"
            )
        if trusted_tooling_sha256 != approval.trusted_tooling_sha256:
            issues.append(
                "executed trusted tooling bundle does not match the reviewer-approved SHA256"
            )

    status = _git(repo, ["status", "--porcelain"])
    if status.strip():
        issues.append("public release workspace is not clean")
    branch = _git(repo, ["branch", "--show-current"]).strip()
    if not branch.startswith(PUBLIC_BRANCH_PREFIX) or branch in {"main", "master"}:
        issues.append(
            f"candidate branch must use fixed prefix {PUBLIC_BRANCH_PREFIX!r} and "
            f"must not be main/master; got {branch!r}"
        )
    candidate_commit = resolved_commit(repo, "HEAD")
    public_base_commit = resolved_commit(repo, PUBLIC_BASE_REF)
    if approval is not None:
        if candidate_commit != approval.candidate_commit:
            issues.append("candidate HEAD does not match the reviewer-approved commit")
        if public_base_commit != approval.public_base_commit:
            issues.append(
                f"fixed {PUBLIC_BASE_REF} does not match the reviewer-approved public base commit"
            )

    private_source_commits = tuple(
        sorted(
            {
                entry.source_commit
                for entry in entries
                if entry.provenance in {"private_blob", "private_projection"}
                and entry.source_commit is not None
            }
        )
    )
    if approval is not None and private_source_commits != approval.private_source_commits:
        issues.append(
            "allowlist private source commits do not exactly match the fixed reviewer approval"
        )

    try:
        history, history_issues = candidate_history(
            repo, PUBLIC_BASE_REF, "HEAD"
        )
    except RuntimeError as exc:
        return [*issues, str(exc)]
    issues.extend(history_issues)
    issues.extend(
        private_source_commit_issues(
            private_repo, entries, private_base_ref=PRIVATE_BASE_REF
        )
    )
    used_entries: set[AllowlistEntry] = set()
    changed_lean_entrypoints: set[str] = set()
    for candidate_history_commit in history:
        issues.extend(
            candidate_tree_entry_issues(
                repo,
                candidate_history_commit.commit,
                list(candidate_history_commit.changes),
            )
        )
        for change in candidate_history_commit.changes:
            if change.status != "D" and change.path.endswith(".lean"):
                changed_lean_entrypoints.add(change.path)
            entry = matching_allowlist_entry(change.path, entries)
            if entry is None:
                issues.append(
                    f"commit {candidate_history_commit.commit}: changed path is not "
                    f"public-export allowlisted: {change.path}"
                )
            else:
                used_entries.add(entry)
                if (
                    change.path in GENERATED_PUBLIC_STATUS_PATHS
                    and change.status != "D"
                    and entry.provenance != "public_generated"
                ):
                    issues.append(
                        f"commit {candidate_history_commit.commit}: generated status path "
                        f"must use public_generated provenance: {change.path}"
                    )
                if (
                    entry.provenance in {"public_generated", "private_projection"}
                    and candidate_history_commit.commit != candidate_commit
                ):
                    issues.append(
                        f"generated/projection path may change only in the final candidate commit: "
                        f"{change.path} in {candidate_history_commit.commit}"
                    )
        issues.extend(
            source_provenance_issues(
                repo,
                private_repo,
                candidate_history_commit.commit,
                list(candidate_history_commit.changes),
                entries,
                public_base_ref=public_base_commit,
            )
        )
    issues.extend(unused_allowlist_issues(entries, used_entries))
    issues.extend(status_visibility_issues(repo, candidate_commit, entries=entries))
    issues.extend(
        changed_formalized_packet_issues(
            repo,
            candidate_commit,
            public_base_ref=public_base_commit,
        )
    )
    issues.extend(source_artifact_leakage_issues(repo, candidate_commit))
    issues.extend(
        public_source_display_projection_issues(
            repo,
            candidate_commit,
            entries,
            private_repo=private_repo,
        )
    )
    issues.extend(
        public_source_role_projection_issues(
            repo,
            candidate_commit,
            entries,
            private_repo=private_repo,
            public_base_ref=public_base_commit,
        )
    )
    issues.extend(forbidden_candidate_path_issues(repo, candidate_commit))
    issues.extend(session_insights_path_issues(repo, candidate_commit))
    issues.extend(
        public_artifact_content_issues(
            repo,
            candidate_commit,
        )
    )
    issues.extend(human_review_packet_pdf_content_issues(repo, candidate_commit))
    issues.extend(candidate_public_artifact_policy_issues(repo, candidate_commit))
    issues.extend(
        selected_graph_authority_registration_issues(repo, candidate_commit)
    )
    issues.extend(generated_status_freshness_issues(repo, candidate_commit))
    issues.extend(public_paper_target_issues(repo, candidate_commit))
    for issue in _public_candidate_dependency_closure_issues(
        repo,
        candidate_commit,
        extra_entrypoints=changed_lean_entrypoints,
    ):
        issues.append("Lean dependency closure: " + issue.format())
    if resolved_commit(repo, "HEAD") != candidate_commit or _git(
        repo, ["status", "--porcelain"]
    ).strip():
        issues.append("public release workspace changed while the guard was running")
    return issues


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--allowlist", type=Path, required=True)
    parser.add_argument(
        "--authoritative",
        action="store_true",
        help=(
            "also require the fixed external reviewer-approval pins; use only "
            "when a maintainer is ready to merge the reviewed candidate"
        ),
    )
    args = parser.parse_args()
    try:
        issues = run_guard(
            args.repo,
            allowlist_path=args.allowlist,
            authoritative=args.authoritative,
        )
    except RuntimeError as exc:
        parser.error(str(exc))
    for issue in issues:
        print("ERROR: " + issue, file=sys.stderr)
    if issues:
        print(f"Public release candidate guard: {len(issues)} error(s)", file=sys.stderr)
        return 1
    if args.authoritative:
        print("Public release candidate guard: OK (authoritative merge check)")
    else:
        print(
            "Public release candidate guard: OK "
            "(candidate/PR check; maintainer approval is required only before merge)"
        )
        print(f"Trusted tooling bundle SHA256: {_trusted_tooling_sha256()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
