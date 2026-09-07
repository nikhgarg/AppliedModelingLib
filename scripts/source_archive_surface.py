#!/usr/bin/env python3
"""Bind a canonical text audit surface to exact members of a source archive.

Some papers were retained locally as a TeX/archive bundle while their
statement map pointed at separate extracted files.  The extracted files are
useful for reading, but they must never silently become an unpinned alternate
source route.  This module defines a small, fail-closed provenance record for
a deterministic UTF-8 text surface reconstructed from named archive members.

The map's normal top-level ``source_artifact_path`` remains the canonical text
surface consumed by coverage and quote validators.  ``source_archive_surface``
then proves that its bytes are *exactly* the declared ordered member surface of
the separately pinned archive.  It is deliberately not a generic extraction
framework: only regular, UTF-8 archive members named by the map can enter the
surface, and every byte of the generated text is reconstructible.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
from pathlib import Path
from typing import Mapping
import tarfile

try:
    from scripts.source_artifact_companion import resolve_paper_source_artifact_path
except ModuleNotFoundError:  # pragma: no cover - direct script imports.
    from source_artifact_companion import resolve_paper_source_artifact_path


SOURCE_ARCHIVE_SURFACE_FIELD = "source_archive_surface"
SOURCE_ARCHIVE_SURFACE_SCHEMA = 1
SOURCE_ARCHIVE_SURFACE_GENERATOR = "archive-members-normalized-text-v1"
_SHA256_LEN = 64
_TOP_LEVEL_FIELDS = frozenset({"schema", "archive", "members", "generator"})
_ARCHIVE_FIELDS = frozenset({"path", "sha256"})
_MEMBER_FIELDS = frozenset({"path", "sha256"})


@dataclass(frozen=True)
class SourceArchiveSurfaceIssue:
    """One archive-surface validation error, tagged for structural checkouts."""

    message: str
    missing_bytes: bool = False


def _digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _strict_mapping(
    value: object, *, field: str, allowed: frozenset[str]
) -> tuple[Mapping[str, object] | None, list[SourceArchiveSurfaceIssue]]:
    if not isinstance(value, Mapping):
        return None, [SourceArchiveSurfaceIssue(f"{field} must be an object")]
    keys = {str(key) for key in value}
    issues: list[SourceArchiveSurfaceIssue] = []
    missing = sorted(allowed - keys)
    unknown = sorted(keys - allowed)
    if missing:
        issues.append(
            SourceArchiveSurfaceIssue(
                f"{field} is missing required field(s): {', '.join(missing)}"
            )
        )
    if unknown:
        issues.append(
            SourceArchiveSurfaceIssue(
                f"{field} has unknown field(s): {', '.join(unknown)}"
            )
        )
    return value, issues


def _sha256_text(value: object, *, field: str) -> tuple[str, list[SourceArchiveSurfaceIssue]]:
    text = value.strip().lower() if isinstance(value, str) else ""
    if len(text) != _SHA256_LEN or any(character not in "0123456789abcdef" for character in text):
        return "", [SourceArchiveSurfaceIssue(f"{field} must be a 64-character lowercase SHA-256")]
    return text, []


def _safe_member_path(value: object, *, field: str) -> tuple[str, list[SourceArchiveSurfaceIssue]]:
    path = value.strip().replace("\\", "/") if isinstance(value, str) else ""
    parts = path.split("/")
    if (
        not path
        or path.startswith("/")
        or any(part in {"", ".", ".."} for part in parts)
    ):
        return "", [
            SourceArchiveSurfaceIssue(
                f"{field} must be a nonempty archive-relative path without `..`"
            )
        ]
    return path, []


def _normalized_member_text(raw: bytes, *, field: str) -> tuple[str | None, list[SourceArchiveSurfaceIssue]]:
    try:
        return raw.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n"), []
    except UnicodeDecodeError:
        return None, [SourceArchiveSurfaceIssue(f"{field} must be UTF-8 text")]


def render_archive_surface(member_texts: list[tuple[str, str]]) -> str:
    """Render the immutable archive-member text surface.

    Member framing is deliberately source-comment syntax so the surface remains
    readable as TeX/text without masquerading as source content.  A final
    newline is always emitted, making the exact construction independent of
    whether an individual member had one.
    """

    pieces: list[str] = []
    for member, text in member_texts:
        pieces.append(f"% === archive member: {member} ===\n")
        pieces.append(text)
        if not text.endswith("\n"):
            pieces.append("\n")
        pieces.append("% === end archive member: {member} ===\n".format(member=member))
    return "".join(pieces)


def archive_surface_member_line_offsets(member_texts: list[tuple[str, str]]) -> dict[str, int]:
    """Return the first canonical-surface line for each rendered member."""

    line = 1
    offsets: dict[str, int] = {}
    for member, text in member_texts:
        line += 1  # opening delimiter
        offsets[member] = line
        line += len(text.split("\n")) - (1 if text.endswith("\n") else 0)
        line += 1  # closing delimiter
    return offsets


def archive_surface_member_texts(
    folder: Path,
    payload: object,
    *,
    repository_root: Path | None = None,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> tuple[list[tuple[str, str]] | None, list[SourceArchiveSurfaceIssue]]:
    """Return verified ordered archive member texts for an opted-in map."""

    if not isinstance(payload, Mapping) or SOURCE_ARCHIVE_SURFACE_FIELD not in payload:
        return None, []
    record, issues = _strict_mapping(
        payload.get(SOURCE_ARCHIVE_SURFACE_FIELD),
        field=SOURCE_ARCHIVE_SURFACE_FIELD,
        allowed=_TOP_LEVEL_FIELDS,
    )
    if record is None:
        return None, issues
    if record.get("schema") != SOURCE_ARCHIVE_SURFACE_SCHEMA:
        issues.append(
            SourceArchiveSurfaceIssue(
                f"{SOURCE_ARCHIVE_SURFACE_FIELD}.schema must equal {SOURCE_ARCHIVE_SURFACE_SCHEMA}"
            )
        )
    if record.get("generator") != SOURCE_ARCHIVE_SURFACE_GENERATOR:
        issues.append(
            SourceArchiveSurfaceIssue(
                f"{SOURCE_ARCHIVE_SURFACE_FIELD}.generator must equal `{SOURCE_ARCHIVE_SURFACE_GENERATOR}`"
            )
        )
    archive, archive_issues = _strict_mapping(
        record.get("archive"),
        field=f"{SOURCE_ARCHIVE_SURFACE_FIELD}.archive",
        allowed=_ARCHIVE_FIELDS,
    )
    issues.extend(archive_issues)
    archive_path: Path | None = None
    archive_raw: bytes | None = None
    if archive is not None:
        raw_path = archive.get("path")
        archive_name = raw_path.strip() if isinstance(raw_path, str) else ""
        archive_sha, sha_issues = _sha256_text(
            archive.get("sha256"), field=f"{SOURCE_ARCHIVE_SURFACE_FIELD}.archive.sha256"
        )
        issues.extend(sha_issues)
        archive_path, path_error = resolve_paper_source_artifact_path(
            folder, archive_name, repository_root=repository_root
        )
        if archive_path is None:
            issues.append(
                SourceArchiveSurfaceIssue(
                    f"{SOURCE_ARCHIVE_SURFACE_FIELD}.archive.path {path_error}"
                )
            )
        elif file_bytes_override is not None:
            archive_path = archive_path.resolve()
            if archive_path not in file_bytes_override:
                issues.append(
                    SourceArchiveSurfaceIssue(
                        f"frozen input bundle omits {SOURCE_ARCHIVE_SURFACE_FIELD}.archive.path: {archive_name}"
                    )
                )
            elif file_bytes_override[archive_path] is None:
                issues.append(
                    SourceArchiveSurfaceIssue(
                        f"{SOURCE_ARCHIVE_SURFACE_FIELD}.archive.path does not exist: {archive_name}",
                        missing_bytes=not require_source_bytes,
                    )
                )
            elif not isinstance(file_bytes_override[archive_path], bytes):
                issues.append(
                    SourceArchiveSurfaceIssue(
                        f"frozen input for {SOURCE_ARCHIVE_SURFACE_FIELD}.archive.path is not bytes: {archive_name}"
                    )
                )
            else:
                archive_raw = file_bytes_override[archive_path]
        elif not archive_path.exists():
            issues.append(
                SourceArchiveSurfaceIssue(
                    f"{SOURCE_ARCHIVE_SURFACE_FIELD}.archive.path does not exist: {archive_name}",
                    missing_bytes=not require_source_bytes,
                )
            )
        elif not archive_path.is_file():
            issues.append(
                SourceArchiveSurfaceIssue(
                    f"{SOURCE_ARCHIVE_SURFACE_FIELD}.archive.path is not a regular file: {archive_name}"
                )
            )
        else:
            try:
                archive_raw = archive_path.read_bytes()
            except OSError as exc:
                issues.append(
                    SourceArchiveSurfaceIssue(
                        f"cannot read {SOURCE_ARCHIVE_SURFACE_FIELD}.archive.path `{archive_name}`: {exc}"
                    )
                )
        if archive_raw is not None and archive_sha and _digest(archive_raw) != archive_sha:
            issues.append(
                SourceArchiveSurfaceIssue(
                    f"{SOURCE_ARCHIVE_SURFACE_FIELD}.archive.sha256 does not match current bytes"
                )
            )

    raw_members = record.get("members")
    if not isinstance(raw_members, list) or not raw_members:
        issues.append(
            SourceArchiveSurfaceIssue(f"{SOURCE_ARCHIVE_SURFACE_FIELD}.members must be a nonempty array")
        )
        return None, issues
    parsed_members: list[tuple[str, str]] = []
    seen: set[str] = set()
    for index, raw_member in enumerate(raw_members):
        field = f"{SOURCE_ARCHIVE_SURFACE_FIELD}.members[{index}]"
        member, member_issues = _strict_mapping(raw_member, field=field, allowed=_MEMBER_FIELDS)
        issues.extend(member_issues)
        if member is None:
            continue
        member_path, path_issues = _safe_member_path(member.get("path"), field=f"{field}.path")
        member_sha, sha_issues = _sha256_text(member.get("sha256"), field=f"{field}.sha256")
        issues.extend(path_issues)
        issues.extend(sha_issues)
        if member_path and member_path in seen:
            issues.append(SourceArchiveSurfaceIssue(f"{field}.path duplicates an earlier member: {member_path}"))
        if member_path:
            seen.add(member_path)
        if member_path and member_sha:
            parsed_members.append((member_path, member_sha))
    if archive_raw is None or issues:
        return None, issues
    try:
        with tarfile.open(fileobj=__import__("io").BytesIO(archive_raw), mode="r:*") as archive_file:
            archive_members = {item.name: item for item in archive_file.getmembers()}
            outputs: list[tuple[str, str]] = []
            for member_path, member_sha in parsed_members:
                archive_member = archive_members.get(member_path)
                if archive_member is None or not archive_member.isfile():
                    issues.append(
                        SourceArchiveSurfaceIssue(
                            f"{SOURCE_ARCHIVE_SURFACE_FIELD}.members path is absent or not a regular archive member: {member_path}"
                        )
                    )
                    continue
                handle = archive_file.extractfile(archive_member)
                raw_member = handle.read() if handle is not None else None
                if raw_member is None:
                    issues.append(SourceArchiveSurfaceIssue(f"could not read archive member: {member_path}"))
                    continue
                if _digest(raw_member) != member_sha:
                    issues.append(
                        SourceArchiveSurfaceIssue(
                            f"{SOURCE_ARCHIVE_SURFACE_FIELD}.members SHA-256 does not match archive member: {member_path}"
                        )
                    )
                    continue
                text, text_issues = _normalized_member_text(raw_member, field=f"{SOURCE_ARCHIVE_SURFACE_FIELD}.members `{member_path}`")
                issues.extend(text_issues)
                if text is not None:
                    outputs.append((member_path, text))
    except (tarfile.TarError, OSError) as exc:
        issues.append(SourceArchiveSurfaceIssue(f"cannot read declared source archive: {exc}"))
        return None, issues
    return (outputs if not issues else None), issues


def source_archive_surface_validation_issues(
    folder: Path,
    payload: object,
    *,
    repository_root: Path | None = None,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[SourceArchiveSurfaceIssue]:
    """Validate an optional archive-derived canonical text surface."""

    if not isinstance(payload, Mapping) or SOURCE_ARCHIVE_SURFACE_FIELD not in payload:
        return []
    member_texts, issues = archive_surface_member_texts(
        folder,
        payload,
        repository_root=repository_root,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    )
    if member_texts is None:
        return issues
    expected_text = render_archive_surface(member_texts)
    declared_path = payload.get("source_artifact_path")
    declared_sha = payload.get("source_artifact_sha256")
    source_path, path_error = resolve_paper_source_artifact_path(
        folder, declared_path, repository_root=repository_root
    )
    if source_path is None:
        issues.append(SourceArchiveSurfaceIssue(f"source_artifact_path {path_error}"))
        return issues
    expected_sha, sha_issues = _sha256_text(declared_sha, field="source_artifact_sha256")
    issues.extend(sha_issues)
    expected_bytes = expected_text.encode("utf-8")
    if expected_sha and _digest(expected_bytes) != expected_sha:
        issues.append(
            SourceArchiveSurfaceIssue(
                "source_artifact_sha256 does not match the deterministic archive-member surface"
            )
        )
    if file_bytes_override is not None:
        source_path = source_path.resolve()
        if source_path not in file_bytes_override:
            issues.append(SourceArchiveSurfaceIssue(f"frozen input bundle omits source_artifact_path: {declared_path}"))
            return issues
        actual = file_bytes_override[source_path]
        if actual is None:
            issues.append(
                SourceArchiveSurfaceIssue(
                    f"source_artifact_path does not exist: {declared_path}",
                    missing_bytes=not require_source_bytes,
                )
            )
            return issues
        if not isinstance(actual, bytes):
            issues.append(SourceArchiveSurfaceIssue("frozen source_artifact_path is not bytes"))
            return issues
    else:
        if not source_path.exists():
            issues.append(
                SourceArchiveSurfaceIssue(
                    f"source_artifact_path does not exist: {declared_path}",
                    missing_bytes=not require_source_bytes,
                )
            )
            return issues
        if not source_path.is_file():
            issues.append(SourceArchiveSurfaceIssue(f"source_artifact_path is not a regular file: {declared_path}"))
            return issues
        try:
            actual = source_path.read_bytes()
        except OSError as exc:
            issues.append(SourceArchiveSurfaceIssue(f"cannot read source_artifact_path: {exc}"))
            return issues
    if actual != expected_bytes:
        issues.append(
            SourceArchiveSurfaceIssue(
                "source_artifact_path bytes do not equal the deterministic archive-member surface"
            )
        )
    return issues


def source_archive_surface_declared_paths(payload: object) -> list[str]:
    """Return archive paths declared by a structurally parseable surface record."""

    if not isinstance(payload, Mapping):
        return []
    record = payload.get(SOURCE_ARCHIVE_SURFACE_FIELD)
    archive = record.get("archive") if isinstance(record, Mapping) else None
    path = archive.get("path") if isinstance(archive, Mapping) else None
    return [path.strip()] if isinstance(path, str) and path.strip() else []
