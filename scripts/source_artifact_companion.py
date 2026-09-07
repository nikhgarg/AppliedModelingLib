#!/usr/bin/env python3
"""Validate optional scanned-PDF/text source companions.

Most source maps have one canonical UTF-8 source artifact.  A scanned paper is
different: the visual PDF is the primary publication evidence, while an
auditable text transcript is needed for source-only named-result discovery and
line-precise quote anchors.  This module defines the deliberately small
``source_text_companion`` schema which binds those two roles without allowing a
map key, Lean declaration, or OCR heuristic to choose the reviewed surface.

The top-level ``source_artifact_path``/``source_artifact_sha256`` remains the
canonical audit identity.  When this companion is present, it must name the
same byte-pinned transcript as ``canonical_text``.  The PDF inputs and the
page-to-transcript map are provenance checks, not alternate source routes.
When the canonical transcript is materially unreadable because of an
embedded-font defect, an optional, byte-pinned visual transcription may
instead supply the semantic-review text.  That transcription is never an
unbound paraphrase: it is explicitly bound to the primary visual scan and is
part of the frozen input bundle.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
from pathlib import Path
import re
from typing import Mapping


SOURCE_TEXT_COMPANION_FIELD = "source_text_companion"
SOURCE_TEXT_COMPANION_SCHEMA = 1
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_COMPANION_FIELDS = frozenset(
    {
        "schema",
        "canonical_text",
        "visual_primary_scan",
        "transcript_input_scan",
        "extraction",
        "page_map",
        "visual_comparison_attestation",
        "semantic_review_transcription",
    }
)
_PINNED_FILE_FIELDS = frozenset({"path", "sha256"})
_EXTRACTION_FIELDS = frozenset({"tool", "options"})
_PAGE_MAP_FIELDS = frozenset(
    {"line_start", "line_end", "pdf_page", "printed_page"}
)
_VISUAL_COMPARISON_FIELDS = frozenset({"complete", "method"})
_SEMANTIC_REVIEW_TRANSCRIPTION_FIELDS = frozenset(
    {
        "schema",
        "path",
        "sha256",
        "controlling_visual_source",
        "complete_for_selected_semantic_surface",
        "method",
    }
)
_SEMANTIC_REVIEW_TRANSCRIPTION_SCHEMA = 1


@dataclass(frozen=True)
class SourceTextCompanionIssue:
    """One companion validation error, tagged when source bytes are absent."""

    message: str
    missing_bytes: bool = False


def resolve_paper_source_artifact_path(
    folder: Path,
    raw_path: object,
    *,
    repository_root: Path | None = None,
) -> tuple[Path | None, str]:
    """Resolve a portable source-artifact path without leaving ``folder``.

    This is intentionally the same policy used by the audit gates: a
    paper-local path is preferred, and a repository-relative ``papers/...``
    path is accepted only when it still resolves inside the requested paper.
    """

    if not isinstance(raw_path, str) or not raw_path.strip():
        return None, "path must be a nonempty string"
    relative_path = Path(raw_path.strip())
    if relative_path.is_absolute():
        return None, "path must be relative to the paper folder or repository root"
    if relative_path.parts[:1] == ("papers",):
        if repository_root is None:
            return None, "repository-relative path needs a repository root"
        anchor = repository_root
    else:
        anchor = folder
    try:
        candidate = (anchor / relative_path).resolve()
        candidate.relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return None, "path escapes the paper folder"
    return candidate, ""


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def semantic_review_source_identity(payload: object) -> tuple[str, str]:
    """Return the exact text identity permitted for source-to-Spec review.

    A map's top-level source artifact remains the complete canonical source for
    inventory and coverage.  A companion may additionally provide a visual
    transcription when the raw extraction is unusable for mathematical
    passages.  This helper recognizes that text only when the companion's
    declarative binding is complete; callers still run
    :func:`source_text_companion_validation_issues` to verify its bytes.
    """

    if not isinstance(payload, Mapping):
        return "", ""
    canonical_path = str(payload.get("source_artifact_path") or "").strip()
    canonical_sha256 = str(payload.get("source_artifact_sha256") or "").strip().lower()
    companion = payload.get(SOURCE_TEXT_COMPANION_FIELD)
    if not isinstance(companion, Mapping):
        return canonical_path, canonical_sha256
    transcription = companion.get("semantic_review_transcription")
    visual = companion.get("visual_primary_scan")
    if not isinstance(transcription, Mapping) or not isinstance(visual, Mapping):
        return canonical_path, canonical_sha256
    path = str(transcription.get("path") or "").strip()
    digest = str(transcription.get("sha256") or "").strip().lower()
    controlling_visual = transcription.get("controlling_visual_source")
    if not isinstance(controlling_visual, Mapping):
        return canonical_path, canonical_sha256
    if (
        transcription.get("schema") != _SEMANTIC_REVIEW_TRANSCRIPTION_SCHEMA
        or not path
        or not _SHA256_RE.fullmatch(digest)
        or transcription.get("complete_for_selected_semantic_surface") is not True
        or controlling_visual.get("path") != visual.get("path")
        or controlling_visual.get("sha256") != visual.get("sha256")
    ):
        return canonical_path, canonical_sha256
    return path, digest


def _normalized_text_line_count(raw: bytes) -> int | None:
    """Return canonical logical-line count, or ``None`` for non-UTF-8 text."""

    try:
        text = raw.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
    except UnicodeDecodeError:
        return None
    if not text:
        return 0
    lines = text.split("\n")
    if text.endswith("\n"):
        lines.pop()
    return len(lines)


def _strict_mapping(
    value: object,
    *,
    field: str,
    allowed_fields: frozenset[str],
    optional_fields: frozenset[str] = frozenset(),
) -> tuple[Mapping[str, object] | None, list[SourceTextCompanionIssue]]:
    """Read a schema object and reject unknown or missing fields explicitly."""

    if not isinstance(value, Mapping):
        return None, [SourceTextCompanionIssue(f"{field} must be an object")]
    keys = {str(key) for key in value}
    issues: list[SourceTextCompanionIssue] = []
    missing = sorted((allowed_fields - optional_fields) - keys)
    unknown = sorted(keys - allowed_fields)
    if missing:
        issues.append(
            SourceTextCompanionIssue(
                f"{field} is missing required field(s): {', '.join(missing)}"
            )
        )
    if unknown:
        issues.append(
            SourceTextCompanionIssue(
                f"{field} has unknown field(s): {', '.join(unknown)}"
            )
        )
    return value, issues


def _pinned_file_issues(
    folder: Path,
    value: object,
    *,
    field: str,
    repository_root: Path | None,
    require_source_bytes: bool,
    require_pdf: bool,
    file_bytes_override: Mapping[Path, bytes | None] | None,
    capture_bytes: bool = False,
) -> tuple[Path | None, str, bytes | None, list[SourceTextCompanionIssue]]:
    """Validate one companion file descriptor and return its verified path."""

    descriptor, issues = _strict_mapping(
        value, field=field, allowed_fields=_PINNED_FILE_FIELDS
    )
    if descriptor is None:
        return None, "", None, issues
    raw_path = descriptor.get("path")
    raw_digest = descriptor.get("sha256")
    path_text = raw_path.strip() if isinstance(raw_path, str) else ""
    digest = raw_digest.strip().lower() if isinstance(raw_digest, str) else ""
    if not path_text:
        issues.append(SourceTextCompanionIssue(f"{field}.path must be a nonempty string"))
    if not _SHA256_RE.fullmatch(digest):
        issues.append(
            SourceTextCompanionIssue(
                f"{field}.sha256 must be exactly 64 hexadecimal characters"
            )
        )
    if not path_text or not _SHA256_RE.fullmatch(digest):
        return None, path_text, None, issues
    if require_pdf and Path(path_text).suffix.lower() != ".pdf":
        issues.append(SourceTextCompanionIssue(f"{field}.path must name a PDF file"))
    resolved, path_error = resolve_paper_source_artifact_path(
        folder, path_text, repository_root=repository_root
    )
    if resolved is None:
        issues.append(SourceTextCompanionIssue(f"{field}.path {path_error}"))
        return None, path_text, None, issues

    captured: bytes | None = None
    if file_bytes_override is not None:
        resolved = resolved.resolve()
        if resolved not in file_bytes_override:
            issues.append(
                SourceTextCompanionIssue(
                    f"frozen input bundle omits {field}.path: {path_text}"
                )
            )
            return None, path_text, None, issues
        raw = file_bytes_override[resolved]
        if raw is None:
            issues.append(
                SourceTextCompanionIssue(
                    f"{field}.path does not exist: {path_text}",
                    missing_bytes=not require_source_bytes,
                )
            )
            return None, path_text, None, issues
        if not isinstance(raw, bytes):
            issues.append(
                SourceTextCompanionIssue(
                    f"frozen input for {field}.path is not bytes: {path_text}"
                )
            )
            return None, path_text, None, issues
        actual_digest = hashlib.sha256(raw).hexdigest()
        captured = raw if capture_bytes else None
    else:
        if not resolved.exists():
            issues.append(
                SourceTextCompanionIssue(
                    f"{field}.path does not exist: {path_text}",
                    missing_bytes=not require_source_bytes,
                )
            )
            return None, path_text, None, issues
        if not resolved.is_file():
            issues.append(
                SourceTextCompanionIssue(
                    f"{field}.path is not a regular file: {path_text}"
                )
            )
            return None, path_text, None, issues
        try:
            if capture_bytes:
                captured = resolved.read_bytes()
                actual_digest = hashlib.sha256(captured).hexdigest()
            else:
                actual_digest = _sha256_file(resolved)
        except OSError as error:
            issues.append(
                SourceTextCompanionIssue(
                    f"cannot read {field}.path `{path_text}`: {error}"
                )
            )
            return None, path_text, None, issues
    if actual_digest != digest:
        issues.append(
            SourceTextCompanionIssue(
                f"{field}.sha256 does not match current bytes: expected {digest}, "
                f"found {actual_digest}"
            )
        )
    return resolved, path_text, captured, issues


def source_text_companion_validation_issues(
    folder: Path,
    payload: object,
    *,
    repository_root: Path | None = None,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[SourceTextCompanionIssue]:
    """Validate an optional scanned-PDF/text companion on a source map.

    No companion is valid legacy input.  Once a map opts in, every field is
    mandatory and byte-checked.  The source transcript remains the top-level
    canonical artifact; visual scans solely prove how that transcript was
    obtained and visually checked.
    """

    if not isinstance(payload, Mapping) or SOURCE_TEXT_COMPANION_FIELD not in payload:
        return []
    raw_companion = payload.get(SOURCE_TEXT_COMPANION_FIELD)
    companion, issues = _strict_mapping(
        raw_companion,
        field=SOURCE_TEXT_COMPANION_FIELD,
        allowed_fields=_COMPANION_FIELDS,
        optional_fields=frozenset({"semantic_review_transcription"}),
    )
    if companion is None:
        return issues
    if companion.get("schema") != SOURCE_TEXT_COMPANION_SCHEMA:
        issues.append(
            SourceTextCompanionIssue(
                f"{SOURCE_TEXT_COMPANION_FIELD}.schema must equal "
                f"{SOURCE_TEXT_COMPANION_SCHEMA}"
            )
        )

    (
        canonical_path,
        canonical_path_text,
        canonical_bytes,
        canonical_issues,
    ) = _pinned_file_issues(
        folder,
        companion.get("canonical_text"),
        field=f"{SOURCE_TEXT_COMPANION_FIELD}.canonical_text",
        repository_root=repository_root,
        require_source_bytes=require_source_bytes,
        require_pdf=False,
        file_bytes_override=file_bytes_override,
        capture_bytes=True,
    )
    issues.extend(canonical_issues)
    visual_path, _visual_path_text, _visual_bytes, visual_issues = _pinned_file_issues(
        folder,
        companion.get("visual_primary_scan"),
        field=f"{SOURCE_TEXT_COMPANION_FIELD}.visual_primary_scan",
        repository_root=repository_root,
        require_source_bytes=require_source_bytes,
        require_pdf=True,
        file_bytes_override=file_bytes_override,
    )
    issues.extend(visual_issues)
    (
        transcript_input_path,
        _input_path_text,
        _input_bytes,
        transcript_input_issues,
    ) = _pinned_file_issues(
        folder,
        companion.get("transcript_input_scan"),
        field=f"{SOURCE_TEXT_COMPANION_FIELD}.transcript_input_scan",
        repository_root=repository_root,
        require_source_bytes=require_source_bytes,
        require_pdf=True,
        file_bytes_override=file_bytes_override,
    )
    issues.extend(transcript_input_issues)

    canonical_descriptor = (
        companion.get("canonical_text")
        if isinstance(companion.get("canonical_text"), Mapping)
        else {}
    )
    canonical_declared_path = str(canonical_descriptor.get("path") or "").strip()
    canonical_declared_digest = str(canonical_descriptor.get("sha256") or "").strip().lower()
    top_level_path = str(payload.get("source_artifact_path") or "").strip()
    top_level_digest = str(payload.get("source_artifact_sha256") or "").strip().lower()
    if top_level_path != canonical_declared_path:
        issues.append(
            SourceTextCompanionIssue(
                "source_artifact_path must exactly equal "
                f"{SOURCE_TEXT_COMPANION_FIELD}.canonical_text.path"
            )
        )
    if top_level_digest != canonical_declared_digest:
        issues.append(
            SourceTextCompanionIssue(
                "source_artifact_sha256 must equal "
                f"{SOURCE_TEXT_COMPANION_FIELD}.canonical_text.sha256"
            )
        )

    # A damaged raw extraction can remain the canonical full-source inventory
    # while a visually checked UTF-8 transcription supplies exact mathematical
    # passages to semantic reviewers.  This optional route is fail-closed:
    # its bytes and its primary visual source must both be pinned.
    semantic_transcription = companion.get("semantic_review_transcription")
    if semantic_transcription is not None:
        transcription, transcription_issues = _strict_mapping(
            semantic_transcription,
            field=f"{SOURCE_TEXT_COMPANION_FIELD}.semantic_review_transcription",
            allowed_fields=_SEMANTIC_REVIEW_TRANSCRIPTION_FIELDS,
        )
        issues.extend(transcription_issues)
        if transcription is not None:
            if transcription.get("schema") != _SEMANTIC_REVIEW_TRANSCRIPTION_SCHEMA:
                issues.append(
                    SourceTextCompanionIssue(
                        f"{SOURCE_TEXT_COMPANION_FIELD}.semantic_review_transcription.schema "
                        f"must equal {_SEMANTIC_REVIEW_TRANSCRIPTION_SCHEMA}"
                    )
                )
            (
                _transcription_path,
                _transcription_path_text,
                transcription_bytes,
                transcription_file_issues,
            ) = _pinned_file_issues(
                folder,
                {"path": transcription.get("path"), "sha256": transcription.get("sha256")},
                field=f"{SOURCE_TEXT_COMPANION_FIELD}.semantic_review_transcription",
                repository_root=repository_root,
                require_source_bytes=require_source_bytes,
                require_pdf=False,
                file_bytes_override=file_bytes_override,
                capture_bytes=True,
            )
            issues.extend(transcription_file_issues)
            if (
                transcription_bytes is not None
                and _normalized_text_line_count(transcription_bytes) is None
            ):
                issues.append(
                    SourceTextCompanionIssue(
                        f"{SOURCE_TEXT_COMPANION_FIELD}.semantic_review_transcription "
                        "must be UTF-8 text"
                    )
                )
            controlling_visual, controlling_visual_issues = _strict_mapping(
                transcription.get("controlling_visual_source"),
                field=(
                    f"{SOURCE_TEXT_COMPANION_FIELD}.semantic_review_transcription."
                    "controlling_visual_source"
                ),
                allowed_fields=_PINNED_FILE_FIELDS,
            )
            issues.extend(controlling_visual_issues)
            visual_descriptor = (
                companion.get("visual_primary_scan")
                if isinstance(companion.get("visual_primary_scan"), Mapping)
                else {}
            )
            if controlling_visual is not None and (
                controlling_visual.get("path") != visual_descriptor.get("path")
                or controlling_visual.get("sha256") != visual_descriptor.get("sha256")
            ):
                issues.append(
                    SourceTextCompanionIssue(
                        f"{SOURCE_TEXT_COMPANION_FIELD}.semantic_review_transcription."
                        "controlling_visual_source must exactly equal "
                        f"{SOURCE_TEXT_COMPANION_FIELD}.visual_primary_scan"
                    )
                )
            if transcription.get("complete_for_selected_semantic_surface") is not True:
                issues.append(
                    SourceTextCompanionIssue(
                        f"{SOURCE_TEXT_COMPANION_FIELD}.semantic_review_transcription."
                        "complete_for_selected_semantic_surface must be true"
                    )
                )
            method = transcription.get("method")
            if not isinstance(method, str) or not method.strip():
                issues.append(
                    SourceTextCompanionIssue(
                        f"{SOURCE_TEXT_COMPANION_FIELD}.semantic_review_transcription.method "
                        "must be a nonempty string"
                    )
                )

    extraction, extraction_issues = _strict_mapping(
        companion.get("extraction"),
        field=f"{SOURCE_TEXT_COMPANION_FIELD}.extraction",
        allowed_fields=_EXTRACTION_FIELDS,
    )
    issues.extend(extraction_issues)
    if extraction is not None:
        tool = extraction.get("tool")
        options = extraction.get("options")
        if not isinstance(tool, str) or tool.strip().lower() != "pdftotext":
            issues.append(
                SourceTextCompanionIssue(
                    f"{SOURCE_TEXT_COMPANION_FIELD}.extraction.tool must be `pdftotext`"
                )
            )
        if not isinstance(options, list) or any(
            not isinstance(option, str) or not option.strip() for option in options
        ):
            issues.append(
                SourceTextCompanionIssue(
                    f"{SOURCE_TEXT_COMPANION_FIELD}.extraction.options must be a list "
                    "of nonempty strings (an empty list records default options)"
                )
            )

    visual_attestation, attestation_issues = _strict_mapping(
        companion.get("visual_comparison_attestation"),
        field=f"{SOURCE_TEXT_COMPANION_FIELD}.visual_comparison_attestation",
        allowed_fields=_VISUAL_COMPARISON_FIELDS,
    )
    issues.extend(attestation_issues)
    if visual_attestation is not None:
        if visual_attestation.get("complete") is not True:
            issues.append(
                SourceTextCompanionIssue(
                    f"{SOURCE_TEXT_COMPANION_FIELD}.visual_comparison_attestation.complete "
                    "must be true"
                )
            )
        method = visual_attestation.get("method")
        if not isinstance(method, str) or not method.strip():
            issues.append(
                SourceTextCompanionIssue(
                    f"{SOURCE_TEXT_COMPANION_FIELD}.visual_comparison_attestation.method "
                    "must be a nonempty string"
                )
            )

    raw_page_map = companion.get("page_map")
    if not isinstance(raw_page_map, list) or not raw_page_map:
        issues.append(
            SourceTextCompanionIssue(
                f"{SOURCE_TEXT_COMPANION_FIELD}.page_map must be a nonempty array"
            )
        )
        return issues

    line_count: int | None = None
    if canonical_path is not None:
        line_count = (
            _normalized_text_line_count(canonical_bytes)
            if canonical_bytes is not None
            else None
        )
        if line_count is None:
            issues.append(
                SourceTextCompanionIssue(
                    f"{SOURCE_TEXT_COMPANION_FIELD}.canonical_text must be UTF-8 text"
                )
            )

    previous_end: int | None = None
    for index, raw_entry in enumerate(raw_page_map):
        field = f"{SOURCE_TEXT_COMPANION_FIELD}.page_map[{index}]"
        entry, entry_issues = _strict_mapping(
            raw_entry, field=field, allowed_fields=_PAGE_MAP_FIELDS
        )
        issues.extend(entry_issues)
        if entry is None:
            continue
        line_start = entry.get("line_start")
        line_end = entry.get("line_end")
        pdf_page = entry.get("pdf_page")
        printed_page = entry.get("printed_page")
        valid_line_range = (
            isinstance(line_start, int)
            and not isinstance(line_start, bool)
            and isinstance(line_end, int)
            and not isinstance(line_end, bool)
            and line_start >= 1
            and line_end >= line_start
        )
        if not valid_line_range:
            issues.append(
                SourceTextCompanionIssue(
                    f"{field}.line_start and {field}.line_end must be a positive "
                    "inclusive line range"
                )
            )
        elif line_count is not None and line_end > line_count:
            issues.append(
                SourceTextCompanionIssue(
                    f"{field}.line_end exceeds the {line_count}-line canonical text"
                )
            )
        if not isinstance(pdf_page, int) or isinstance(pdf_page, bool) or pdf_page < 1:
            issues.append(
                SourceTextCompanionIssue(f"{field}.pdf_page must be a positive integer")
            )
        if not (
            (isinstance(printed_page, int) and not isinstance(printed_page, bool) and printed_page >= 1)
            or (isinstance(printed_page, str) and printed_page.strip())
        ):
            issues.append(
                SourceTextCompanionIssue(
                    f"{field}.printed_page must be a positive integer or nonempty string"
                )
            )
        if valid_line_range:
            if previous_end is not None:
                if line_start <= previous_end:
                    issues.append(
                        SourceTextCompanionIssue(
                            f"{field} overlaps the preceding page_map article-line range"
                        )
                    )
                elif line_start != previous_end + 1:
                    issues.append(
                        SourceTextCompanionIssue(
                            f"{field} is not contiguous with the preceding page_map "
                            "article-line range"
                        )
                    )
            previous_end = line_end

    # Keep local variables referenced so readers can see that both visually
    # sourced scans are intentionally checked even when their bytes coincide.
    _ = visual_path, transcript_input_path, canonical_path_text
    return issues
