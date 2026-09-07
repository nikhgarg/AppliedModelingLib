#!/usr/bin/env python3
"""Path-semantic hygiene policy for public release candidates.

The policy is deliberately independent of paper identifiers.  A caller may
pass exact, status-referenced supplemental audit paths; the stable audit
outputs below do not need such an exception.  Explicitly historical or working
audit artifacts remain forbidden even when supplied as an exception.
"""

from __future__ import annotations

import re
from collections.abc import Iterable
from pathlib import PurePath, PurePosixPath


_CANONICAL_AUDIT_FILENAMES = frozenset(
    {
        "assumption_match_llm.json",
        "defect_support_match_llm.json",
        "lean_to_tex_llm.json",
        "paper_coverage_llm.json",
        "paper_statement_map.json",
        "public_source_display_projection.json",
        "review_surface_llm.json",
        "source_proof_fidelity.json",
        "source_record_audit.json",
        "source_record_match_llm.json",
        "statement_match_llm.json",
    }
)
_PRIVATE_DOCUMENT_PREFIXES = frozenset(
    {"formalization_plan", "paper_notes", "start_here", "handoff"}
)
_PRIVATE_SOURCE_DIRECTORIES = frozenset(
    {".audit_source", ".review_traces", "source_tex", "sources"}
)
_GENERATED_CACHE_DIRECTORIES = frozenset(
    {".cache", ".mypy_cache", ".pytest_cache", ".ruff_cache", "__pycache__"}
)
_AUDIT_WORKING_MARKERS = frozenset(
    {
        "archive",
        "archival",
        "backup",
        "before",
        "candidate",
        "draft",
        "dryrun",
        "fragment",
        "historical",
        "history",
        "legacy",
        "migration",
        "noncanonical",
        "obsolete",
        "old",
        "pre",
        "prior",
        "retired",
        "scaffold",
        "scratch",
        "seeded",
        "snapshot",
        "superseded",
        "template",
    }
)
_SOURCE_BUNDLE_RE = re.compile(
    r"^(?:source(?:[._-][^/]*)?|arxiv_source)"
    r"\.(?:txt|pdf|tex|tar|tgz|zip|gz)$",
    re.IGNORECASE,
)
_ARCHIVE_SUFFIXES = frozenset({".zip", ".tar", ".tgz", ".gz", ".bz2", ".xz", ".7z", ".rar"})
_LATEX_BUILD_SUFFIXES = frozenset(
    {
        ".aux",
        ".fdb_latexmk",
        ".fls",
        ".log",
        ".out",
        ".synctex.gz",
        ".toc",
        ".xdv",
    }
)
_TOKEN_SPLIT_RE = re.compile(r"[._-]+")
_CONTRIBUTOR_TEMPLATE_PLANS = frozenset(
    {
        "papers/TEMPLATE/docs/FORMALIZATION_PLAN.md",
        "skills/econcs-formalizer/templates/FORMALIZATION_PLAN.md",
    }
)


def _normalize_repo_path(raw_path: str | PurePath) -> str | None:
    text = str(raw_path)
    if not text or text.startswith("/") or "\\" in text:
        return None
    path = PurePosixPath(text)
    if any(part in {"", ".", ".."} for part in path.parts):
        return None
    normalized = path.as_posix()
    if normalized != text:
        return None
    return normalized


def _tokens(component: str) -> frozenset[str]:
    return frozenset(token for token in _TOKEN_SPLIT_RE.split(component.lower()) if token)


def _is_private_cache_directory(component: str) -> bool:
    lowered = component.lower()
    if lowered in _PRIVATE_SOURCE_DIRECTORIES | _GENERATED_CACHE_DIRECTORIES:
        return True
    tokens = _tokens(lowered)
    cache_tokens = {"cache", "caches"}
    source_tokens = {
        "audit",
        "extract",
        "extracted",
        "extraction",
        "review",
        "source",
        "trace",
        "traces",
    }
    if tokens & cache_tokens and tokens & source_tokens:
        return True
    return (
        {"audit", "source"} <= tokens
        or {"review", "traces"} <= tokens
        or {"source", "extraction"} <= tokens
        or {"extracted", "source"} <= tokens
    )


def _is_private_document(filename: str) -> bool:
    lowered = filename.lower()
    if any(
        lowered == prefix
        or lowered.startswith(f"{prefix}.")
        or lowered.startswith(f"{prefix}_")
        or lowered.startswith(f"{prefix}-")
        for prefix in _PRIVATE_DOCUMENT_PREFIXES
    ):
        return True
    return "handoff" in _tokens(lowered)


def _is_public_contributor_template(path: PurePosixPath) -> bool:
    """Keep the one reviewed scaffold plan, not plans under paper namespaces."""

    return path.as_posix() in _CONTRIBUTOR_TEMPLATE_PLANS


def _audit_parts(path: PurePosixPath) -> tuple[tuple[str, ...], str] | None:
    parts = path.parts
    if len(parts) < 4 or parts[0].lower() != "papers" or parts[2].lower() != "audit":
        return None
    return parts[3:-1], parts[-1]


def _is_legacy_paper_root_audit(path: PurePosixPath) -> bool:
    parts = path.parts
    return bool(
        len(parts) == 3
        and parts[0].lower() == "papers"
        and parts[-1].lower() in _CANONICAL_AUDIT_FILENAMES
    )


def _audit_working_markers(
    directories: tuple[str, ...], filename: str
) -> frozenset[str]:
    tokens: set[str] = set()
    for component in (*directories, filename):
        tokens.update(_tokens(component))
    return frozenset(tokens & _AUDIT_WORKING_MARKERS)


def _current_audit_exceptions(
    paths: Iterable[str | PurePath],
) -> frozenset[str]:
    normalized_paths: set[str] = set()
    for raw_path in paths:
        normalized = _normalize_repo_path(raw_path)
        if normalized is None:
            raise ValueError(f"invalid current audit artifact path: {raw_path}")
        audit_parts = _audit_parts(PurePosixPath(normalized))
        if audit_parts is None:
            raise ValueError(
                "current audit artifact exceptions must be beneath "
                f"papers/<paper>/audit: {normalized}"
            )
        directories, filename = audit_parts
        markers = _audit_working_markers(directories, filename)
        if markers:
            raise ValueError(
                f"current audit artifact exception is working/history material "
                f"({', '.join(sorted(markers))}): {normalized}"
            )
        normalized_paths.add(normalized)
    return frozenset(normalized_paths)


def _public_source_exceptions(
    paths: Iterable[str | PurePath],
) -> frozenset[str]:
    """Normalize the narrowly approved public-source paths from the guard.

    The caller is responsible for proving arXiv provenance and byte identity.
    This path policy only keeps that decision scoped to one paper-local TeX
    artifact; it never permits archives, extracted caches, PDFs, or a source
    directory as a whole.
    """

    approved: set[str] = set()
    for raw_path in paths:
        normalized = _normalize_repo_path(raw_path)
        if normalized is None:
            raise ValueError(f"invalid public source artifact path: {raw_path}")
        path = PurePosixPath(normalized)
        if (
            len(path.parts) != 4
            or path.parts[0] != "papers"
            or path.parts[2] != "source"
            or path.suffix.lower() != ".tex"
        ):
            raise ValueError(
                "public source artifact exceptions must name exactly "
                "papers/<paper>/source/<official-arxiv-file>.tex: " + normalized
            )
        approved.add(normalized)
    return frozenset(approved)


def public_release_artifact_issues(
    paths: Iterable[str | PurePath],
    *,
    current_audit_artifacts: Iterable[str | PurePath] = (),
    public_source_artifacts: Iterable[str | PurePath] = (),
) -> list[str]:
    """Return deterministic hygiene issues for candidate repository paths.

    ``current_audit_artifacts`` must contain exact paths obtained from the
    candidate's paper status records, receipt-bound ledgers, or validated
    corrected-target approval routes. It permits supplemental current artifacts
    with noncanonical names.  It cannot override source/cache, private-document,
    or historical/working-audit rules.
    """

    current_audit_paths = _current_audit_exceptions(current_audit_artifacts)
    public_source_paths = _public_source_exceptions(public_source_artifacts)
    issues: list[str] = []
    seen: set[tuple[str, str]] = set()

    def add(code: str, path: str, detail: str) -> None:
        key = (code, path)
        if key not in seen:
            seen.add(key)
            issues.append(f"public artifact policy [{code}]: {path}: {detail}")

    normalized_inputs: list[tuple[str, str | None]] = [
        (str(raw_path), _normalize_repo_path(raw_path)) for raw_path in paths
    ]
    normalized_paths = {
        normalized
        for _, normalized in normalized_inputs
        if normalized is not None
    }
    for raw_path, normalized in sorted(normalized_inputs, key=lambda item: item[0]):
        if normalized is None:
            add("unsafe-path", raw_path, "path is not a normalized relative POSIX path")
            continue

        path = PurePosixPath(normalized)
        directory_parts = path.parts[:-1]
        private_components = sorted(
            component
            for component in directory_parts
            if _is_private_cache_directory(component)
        )
        if private_components:
            add(
                "private-cache",
                normalized,
                "source, extraction, trace, or generated cache directory "
                f"{private_components[0]!r} must remain private",
            )
        if any(component.lower() == "source" for component in directory_parts) and normalized not in public_source_paths:
            add(
                "unapproved-source-subtree",
                normalized,
                "only one exact validated official arXiv TeX path may appear beneath papers/<paper>/source",
            )
        if path.suffix.lower() in _ARCHIVE_SUFFIXES and not normalized.lower().endswith(
            ".synctex.gz"
        ):
            add(
                "archive-artifact",
                normalized,
                "archive artifacts are not public release inputs",
            )
        # Reject TeX compiler debris only when a same-stem TeX source exists in
        # the candidate. This catches presentation build by-products without
        # treating an unrelated, intentionally versioned `.log` or `.out` data
        # file as a LaTeX artifact merely by extension.
        lowered = normalized.lower()
        latex_suffix = next(
            (suffix for suffix in _LATEX_BUILD_SUFFIXES if lowered.endswith(suffix)),
            None,
        )
        if latex_suffix is not None:
            tex_peer = normalized[: -len(latex_suffix)] + ".tex"
            if tex_peer in normalized_paths:
                add(
                    "latex-build-artifact",
                    normalized,
                    f"LaTeX build output must be regenerated locally from {tex_peer}",
                )
        if _SOURCE_BUNDLE_RE.fullmatch(path.name) and normalized not in public_source_paths:
            add(
                "private-source-bundle",
                normalized,
                "source bundle or extracted source file must remain private",
            )
        if _is_private_document(path.name) and not _is_public_contributor_template(path):
            add(
                "private-document",
                normalized,
                "formalization planning or agent-handoff document must remain private",
            )
        if _is_legacy_paper_root_audit(path):
            add(
                "legacy-root-audit-artifact",
                normalized,
                "current audit evidence must live beneath papers/<paper>/audit",
            )

        audit_parts = _audit_parts(path)
        if audit_parts is None:
            continue
        audit_directories, audit_filename = audit_parts
        markers = _audit_working_markers(audit_directories, audit_filename)
        if markers:
            add(
                "working-audit-artifact",
                normalized,
                "historical, legacy, snapshot, template, or draft audit artifact "
                f"has marker(s): {', '.join(sorted(markers))}",
            )
            continue
        if (
            audit_filename.lower() not in _CANONICAL_AUDIT_FILENAMES
            and normalized not in current_audit_paths
        ):
            add(
                "unreferenced-audit-artifact",
                normalized,
                "noncanonical audit artifact is not an exact current status reference",
            )

    return issues


__all__ = ["public_release_artifact_issues"]
