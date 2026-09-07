#!/usr/bin/env python3
"""Freeze a public display surface from a private, byte-pinned source map.

The paper audit remains private and source-byte strict.  This small projection
does not try to publish, replace, or relax that audit.  It records only the
currently selected source-item IDs and their exact byte-pinned excerpts, so a
public dashboard can display the review surface without carrying the complete
private source artifact.

The selector is deliberately imported from :mod:`review_dashboard`, rather
than reimplemented here.  Thus the projection has exactly the current coverage
semantics, including source-index and nonordinary-obligation selection.  A
projection can be written only after the current private source artifact and
every displayed anchor verify against their declared bytes.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
import re
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence

PACKAGE_ROOT = Path(__file__).resolve().parents[1]
if str(PACKAGE_ROOT) not in sys.path:
    sys.path.insert(0, str(PACKAGE_ROOT))

from scripts.public_release_projection import ProjectionError, project_bytes
from scripts.review_dashboard import paper_coverage_inventory
from scripts.source_coverage_scope import (
    _current_canonical_text_source,
    source_coverage_mode_from_map,
)
from scripts.source_artifact_companion import (
    resolve_paper_source_artifact_path,
    semantic_review_source_identity,
)
from scripts.source_manifest_validation import cited_source_artifact_registry


ROOT = Path(
    os.environ.get("APPLIEDMODELINGLIB_REPO_ROOT", Path(__file__).resolve().parents[1])
).resolve()
PAPERS_DIR = ROOT / "papers"
PAPER_STATEMENT_MAP_FILE = "audit/paper_statement_map.json"
PUBLIC_SOURCE_DISPLAY_PROJECTION_FILE = "audit/public_source_display_projection.json"
PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA = 1
PUBLIC_SOURCE_DISPLAY_PROJECTION_GENERATOR = (
    "python3 scripts/public_source_display_projection.py"
)
PUBLICATION_LOCATOR = "cited publication"
_SHA256_RE = re.compile(r"[0-9a-f]{64}")


class PublicSourceDisplayProjectionError(ValueError):
    """Raised when the private audit cannot produce a safe display projection."""


@dataclass(frozen=True)
class _RegisteredTextSource:
    """One private UTF-8 source whose exact bytes are registered by the map."""

    path: Path
    lines: tuple[str, ...]
    semantic_roles: frozenset[str] = frozenset()


@dataclass(frozen=True)
class _RegisteredSourceBundle:
    """The only source artifacts from which display anchors may be emitted."""

    primary_sources: Mapping[Path, _RegisteredTextSource]
    cited_sources: Mapping[str, _RegisteredTextSource]


def public_source_display_projection_path(folder: Path) -> Path:
    """Return the fixed paper-local display-projection path."""

    return folder / PUBLIC_SOURCE_DISPLAY_PROJECTION_FILE


def public_source_display_projection_public_path(folder: Path) -> str:
    """Return the exact repository-relative public path for this manifest."""

    return f"papers/{folder.name}/{PUBLIC_SOURCE_DISPLAY_PROJECTION_FILE}"


def _public_source_map_path(folder: Path) -> str:
    return f"papers/{folder.name}/{PAPER_STATEMENT_MAP_FILE}"


def _normalized_source_path(value: object) -> str:
    """Normalize a safe map-relative path for equality, not file access."""

    raw = str(value or "").replace("\\", "/").strip()
    while raw.startswith("./"):
        raw = raw[2:]
    if not raw or raw.startswith("/") or ".." in raw.split("/"):
        return ""
    return raw


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _canonical_json_bytes(payload: object) -> bytes:
    return (
        json.dumps(
            payload,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def _load_private_source_map(folder: Path) -> tuple[Path, bytes, dict[str, Any]]:
    map_path = folder / PAPER_STATEMENT_MAP_FILE
    try:
        raw = map_path.read_bytes()
    except OSError as exc:
        raise PublicSourceDisplayProjectionError(
            f"cannot read {PAPER_STATEMENT_MAP_FILE}: {exc}"
        ) from exc
    try:
        payload = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise PublicSourceDisplayProjectionError(
            f"{PAPER_STATEMENT_MAP_FILE} is not valid UTF-8 JSON: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise PublicSourceDisplayProjectionError(
            f"{PAPER_STATEMENT_MAP_FILE} must contain a JSON object"
        )
    return map_path, raw, payload


def _current_source(
    folder: Path, map_payload: Mapping[str, object]
) -> tuple[str, str, str, str]:
    """Return canonical source text only after the private artifact pin verifies."""

    current = _current_canonical_text_source(
        folder,
        map_payload,
        repository_root=ROOT,
    )
    if current is None:
        raise PublicSourceDisplayProjectionError(
            "cannot read the current byte-pinned canonical source artifact"
        )
    source_text, source_path, source_format = current
    source_sha256 = str(map_payload.get("source_artifact_sha256") or "").strip().lower()
    if not _SHA256_RE.fullmatch(source_sha256):
        raise PublicSourceDisplayProjectionError(
            "paper_statement_map.json has no valid source_artifact_sha256"
        )
    return source_text, source_path, source_format, source_sha256


def _normalized_source_lines(source_text: str) -> tuple[str, ...]:
    lines = source_text.split("\n")
    if source_text.endswith("\n"):
        lines.pop()
    return tuple(lines)


def _read_registered_text_source(
    path: Path,
    expected_sha256: str,
    *,
    label: str,
    semantic_roles: frozenset[str] = frozenset(),
) -> _RegisteredTextSource:
    """Read one already declared source and recheck its exact UTF-8 bytes."""

    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise PublicSourceDisplayProjectionError(
            f"cannot read {label}: {exc}"
        ) from exc
    actual_sha256 = hashlib.sha256(raw).hexdigest()
    if actual_sha256 != expected_sha256:
        raise PublicSourceDisplayProjectionError(
            f"{label} SHA-256 does not match its registered source pin"
        )
    try:
        text = raw.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
    except UnicodeDecodeError as exc:
        raise PublicSourceDisplayProjectionError(
            f"{label} is not UTF-8 text"
        ) from exc
    return _RegisteredTextSource(
        path=path,
        lines=_normalized_source_lines(text),
        semantic_roles=semantic_roles,
    )


def _registered_source_bundle(
    folder: Path,
    map_path: Path,
    map_payload: Mapping[str, object],
    *,
    canonical_text: str,
    canonical_path_text: str,
    canonical_sha256: str,
) -> _RegisteredSourceBundle:
    """Materialize only canonical, selected-semantic, and cited source pins."""

    canonical_path, path_error = resolve_paper_source_artifact_path(
        folder,
        canonical_path_text,
        repository_root=ROOT,
    )
    if canonical_path is None:
        raise PublicSourceDisplayProjectionError(
            "cannot resolve the canonical source artifact: " + path_error
        )
    primary_sources: dict[Path, _RegisteredTextSource] = {
        canonical_path: _RegisteredTextSource(
            path=canonical_path,
            lines=_normalized_source_lines(canonical_text),
        )
    }

    semantic_path_text, semantic_sha256 = semantic_review_source_identity(map_payload)
    semantic_path, semantic_path_error = resolve_paper_source_artifact_path(
        folder,
        semantic_path_text,
        repository_root=ROOT,
    )
    if semantic_path is None:
        raise PublicSourceDisplayProjectionError(
            "cannot resolve the selected semantic source artifact: "
            + semantic_path_error
        )
    if not _SHA256_RE.fullmatch(semantic_sha256):
        raise PublicSourceDisplayProjectionError(
            "selected semantic source artifact has no valid SHA-256 pin"
        )
    if semantic_path == canonical_path:
        if semantic_sha256 != canonical_sha256:
            raise PublicSourceDisplayProjectionError(
                "selected semantic source pin disagrees with the canonical source pin"
            )
    else:
        primary_sources[semantic_path] = _read_registered_text_source(
            semantic_path,
            semantic_sha256,
            label="selected semantic source artifact",
        )

    raw_cited_sources, cited_findings = cited_source_artifact_registry(
        folder,
        "formalized",
        map_path,
        map_payload,
    )
    if cited_findings:
        messages = sorted({finding.message for finding in cited_findings})
        raise PublicSourceDisplayProjectionError(
            "cited source artifact registry is invalid: " + "; ".join(messages)
        )
    cited_sources: dict[str, _RegisteredTextSource] = {}
    for source_id, source in raw_cited_sources.items():
        path = source.get("path")
        lines = source.get("lines")
        roles = source.get("semantic_roles")
        if (
            not isinstance(path, Path)
            or not isinstance(lines, list)
            or any(not isinstance(line, str) for line in lines)
            or not isinstance(roles, set)
            or any(not isinstance(role, str) for role in roles)
        ):
            raise PublicSourceDisplayProjectionError(
                f"cited source artifact `{source_id}` did not materialize as pinned UTF-8 text"
            )
        cited_sources[source_id] = _RegisteredTextSource(
            path=path,
            lines=tuple(lines),
            semantic_roles=frozenset(roles),
        )
    return _RegisteredSourceBundle(
        primary_sources=primary_sources,
        cited_sources=cited_sources,
    )


def _registered_source_for_anchor(
    folder: Path,
    private_record: Mapping[str, object],
    raw_path: object,
    sources: _RegisteredSourceBundle,
    *,
    label: str,
) -> tuple[_RegisteredTextSource | None, list[str]]:
    """Resolve an anchor through its identity-bound registered source route."""

    path, path_error = resolve_paper_source_artifact_path(
        folder,
        raw_path,
        repository_root=ROOT,
    )
    if path is None:
        return None, [f"{label} source path {path_error}"]

    raw_cited_id = private_record.get("cited_source_artifact_id")
    if raw_cited_id is not None:
        cited_id = str(raw_cited_id or "").strip()
        cited_source = sources.cited_sources.get(cited_id)
        if cited_source is None:
            return None, [
                f"{label} names unregistered cited source artifact `{cited_id}`"
            ]
        role = str(
            private_record.get("cited_source_role")
            or private_record.get("semantic_role")
            or ""
        ).strip()
        if role not in cited_source.semantic_roles:
            return None, [
                f"{label} uses cited source artifact `{cited_id}` for unregistered "
                f"semantic role `{role}`"
            ]
        if path != cited_source.path:
            return None, [
                f"{label} does not point to pinned cited source artifact `{cited_id}`"
            ]
        return cited_source, []

    source = sources.primary_sources.get(path)
    if source is None:
        return None, [
            f"{label} does not point to the canonical source artifact or its "
            "selected semantic transcription"
        ]
    return source, []


def _display_anchor(
    private_anchor: object,
    public_anchor: object,
    *,
    folder: Path,
    private_record: Mapping[str, object],
    sources: _RegisteredSourceBundle,
    label: str,
) -> tuple[dict[str, Any] | None, list[str]]:
    """Validate a private anchor and emit its matching public-map anchor.

    The private anchor supplies the only acceptable local source path and byte
    slice.  The resulting display record takes its quote/digest from the
    deterministic public source-map projection, so the public map and display
    manifest cannot silently disagree about an excerpt.
    """

    if not isinstance(private_anchor, Mapping):
        return None, [f"{label} is not an object"]
    if not isinstance(public_anchor, Mapping):
        return None, [f"{label} has no corresponding public-map source anchor"]
    path = private_anchor.get("path")
    line_start = private_anchor.get("line_start")
    line_end = private_anchor.get("line_end")
    quote = private_anchor.get("quoted_text")
    recorded_sha = str(private_anchor.get("quoted_text_sha256") or "").strip().lower()
    errors: list[str] = []
    source: _RegisteredTextSource | None = None
    if not isinstance(path, str) or not _normalized_source_path(path):
        errors.append(f"{label} has no valid source path")
    else:
        source, source_errors = _registered_source_for_anchor(
            folder,
            private_record,
            path,
            sources,
            label=label,
        )
        errors.extend(source_errors)
    if not isinstance(line_start, int) or isinstance(line_start, bool) or line_start < 1:
        errors.append(f"{label} has no valid line_start")
    if (
        not isinstance(line_end, int)
        or isinstance(line_end, bool)
        or not isinstance(line_start, int)
        or isinstance(line_start, bool)
        or line_end < line_start
    ):
        errors.append(f"{label} has no valid line_end")
    if not isinstance(quote, str) or not quote:
        errors.append(f"{label} has no quoted_text")
    if not _SHA256_RE.fullmatch(recorded_sha):
        errors.append(f"{label} has no valid quoted_text_sha256")
    if errors:
        return None, errors

    normalized_quote = quote.replace("\r\n", "\n").replace("\r", "\n")
    actual_sha = _sha256_text(normalized_quote)
    if actual_sha != recorded_sha:
        errors.append(f"{label} quoted_text_sha256 does not match quoted_text")
    if source is None:
        pass
    elif line_end > len(source.lines):
        errors.append(f"{label} line range is outside the registered source artifact")
    elif normalized_quote != "\n".join(source.lines[line_start - 1 : line_end]):
        errors.append(f"{label} quoted_text does not equal the current source slice")
    public_quote = public_anchor.get("quoted_text")
    public_sha = str(public_anchor.get("quoted_text_sha256") or "").strip().lower()
    if "path" in public_anchor:
        errors.append(f"{label} public-map anchor retains a local path")
    if not isinstance(public_quote, str) or not public_quote:
        errors.append(f"{label} public-map anchor has no quoted_text")
    elif not _SHA256_RE.fullmatch(public_sha) or _sha256_text(public_quote) != public_sha:
        errors.append(f"{label} public-map quoted_text_sha256 does not match quoted_text")
    elif public_quote != normalized_quote or public_sha != actual_sha:
        errors.append(f"{label} public-map anchor quote does not match private source bytes")
    if public_anchor.get("line_start") != line_start or public_anchor.get("line_end") != line_end:
        errors.append(f"{label} public-map anchor line range does not match private source bytes")
    if public_anchor.get("publication_locator") != PUBLICATION_LOCATOR:
        errors.append(f"{label} public-map anchor has no public publication locator")
    if errors:
        return None, errors
    return {
        "line_end": public_anchor["line_end"],
        "line_start": public_anchor["line_start"],
        "publication_locator": public_anchor["publication_locator"],
        "quoted_text": public_quote,
        "quoted_text_sha256": public_sha,
    }, []


def _display_anchor_bundle(
    private_anchors: object,
    public_anchors: object,
    *,
    folder: Path,
    private_record: Mapping[str, object],
    sources: _RegisteredSourceBundle,
    label: str,
) -> tuple[list[dict[str, Any]], list[str]]:
    if not isinstance(private_anchors, list) or not private_anchors:
        return [], [f"{label} has no source_anchor_evidence"]
    if not isinstance(public_anchors, list):
        return [], [f"{label} public-map source_anchor_evidence is not a list"]
    if len(private_anchors) != len(public_anchors):
        return [], [f"{label} public-map source anchor count differs from private map"]
    displayed: list[dict[str, Any]] = []
    errors: list[str] = []
    for index, private_anchor in enumerate(private_anchors):
        result, anchor_errors = _display_anchor(
            private_anchor,
            public_anchors[index],
            folder=folder,
            private_record=private_record,
            sources=sources,
            label=f"{label} source anchor {index}",
        )
        errors.extend(anchor_errors)
        if result is not None:
            displayed.append(result)
    return displayed, errors


def _display_context_requirements(
    private_item: Mapping[str, object],
    public_item: Mapping[str, object],
    *,
    folder: Path,
    sources: _RegisteredSourceBundle,
    label: str,
) -> tuple[list[dict[str, Any]], list[str]]:
    """Project raw semantic context without carrying explanatory paraphrases."""

    private_requirements = private_item.get("semantic_context_requirements")
    public_requirements = public_item.get("semantic_context_requirements")
    if private_requirements is None and public_requirements is None:
        return [], []
    if not isinstance(private_requirements, list):
        return [], [f"{label} semantic_context_requirements is not a list"]
    if not isinstance(public_requirements, list):
        return [], [f"{label} public-map semantic_context_requirements is not a list"]
    if len(private_requirements) != len(public_requirements):
        return [], [f"{label} public-map semantic context count differs from private map"]
    displayed: list[dict[str, Any]] = []
    errors: list[str] = []
    for index, private_requirement in enumerate(private_requirements):
        requirement_label = f"{label} semantic context {index}"
        public_requirement = public_requirements[index]
        if not isinstance(private_requirement, Mapping):
            errors.append(f"{requirement_label} is not an object")
            continue
        if not isinstance(public_requirement, Mapping):
            errors.append(f"{requirement_label} has no corresponding public-map record")
            continue
        role = str(private_requirement.get("semantic_role") or "").strip()
        if not role:
            errors.append(f"{requirement_label} has no semantic_role")
            continue
        public_role = str(public_requirement.get("semantic_role") or "").strip()
        if public_role != role:
            errors.append(f"{requirement_label} public-map semantic_role differs from private map")
            continue
        anchors, anchor_errors = _display_anchor_bundle(
            private_requirement.get("source_anchor_evidence"),
            public_requirement.get("source_anchor_evidence"),
            folder=folder,
            private_record=private_requirement,
            sources=sources,
            label=requirement_label,
        )
        errors.extend(anchor_errors)
        if not anchor_errors:
            displayed.append(
                {
                    "semantic_role": public_role,
                    "source_anchors": anchors,
                }
            )
    return displayed, errors


def build_public_source_display_projection(folder: Path) -> dict[str, Any]:
    """Build the deterministic display projection from current private evidence.

    The selected IDs come from :func:`review_dashboard.paper_coverage_inventory`
    exactly.  This function never widens, narrows, or otherwise reinterprets
    the coverage selector.
    """

    folder = folder.resolve()
    _map_path, map_bytes, map_payload = _load_private_source_map(folder)
    try:
        public_map_bytes = project_bytes(
            _public_source_map_path(folder),
            map_bytes,
            include_source_display_marker=True,
        )
        public_map_payload = json.loads(public_map_bytes.decode("utf-8"))
    except (ProjectionError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise PublicSourceDisplayProjectionError(
            f"cannot build the deterministic public source-map projection: {exc}"
        ) from exc
    if not isinstance(public_map_payload, Mapping):
        raise PublicSourceDisplayProjectionError(
            "deterministic public source-map projection is not a JSON object"
        )
    mode, mode_error = source_coverage_mode_from_map(map_payload)
    if mode_error:
        raise PublicSourceDisplayProjectionError(mode_error)
    source_text, source_path, _source_format, source_sha256 = _current_source(
        folder, map_payload
    )
    sources = _registered_source_bundle(
        folder,
        _map_path,
        map_payload,
        canonical_text=source_text,
        canonical_path_text=source_path,
        canonical_sha256=source_sha256,
    )
    try:
        _full_inventory, selected_inventory, selected_mode, selection_error = (
            paper_coverage_inventory(folder)
        )
    except Exception as exc:  # pragma: no cover - defensive boundary for CLI users.
        raise PublicSourceDisplayProjectionError(
            f"cannot apply current coverage semantics: {exc}"
        ) from exc
    if selection_error:
        raise PublicSourceDisplayProjectionError(selection_error)
    if selected_mode != mode:
        raise PublicSourceDisplayProjectionError(
            "current coverage selector returned a mode different from the source map"
        )
    raw_items = map_payload.get("items")
    if not isinstance(raw_items, Mapping):
        raise PublicSourceDisplayProjectionError(
            "paper_statement_map.json items must be an object"
        )
    public_items = public_map_payload.get("items")
    if not isinstance(public_items, Mapping):
        raise PublicSourceDisplayProjectionError(
            "deterministic public source-map projection items must be an object"
        )

    selected_ids = sorted(str(item_id) for item_id in selected_inventory)
    if len(selected_ids) != len(set(selected_ids)) or any(not item_id for item_id in selected_ids):
        raise PublicSourceDisplayProjectionError(
            "current coverage selector returned invalid source-item IDs"
        )

    selected_items: dict[str, dict[str, Any]] = {}
    errors: list[str] = []
    for item_id in selected_ids:
        raw_item = raw_items.get(item_id)
        public_item = public_items.get(item_id)
        label = f"selected source item `{item_id}`"
        if not isinstance(raw_item, Mapping):
            errors.append(f"{label} is absent from the current private source map")
            continue
        if not isinstance(public_item, Mapping):
            errors.append(f"{label} is absent from the deterministic public source map")
            continue
        anchors, anchor_errors = _display_anchor_bundle(
            raw_item.get("source_anchor_evidence"),
            public_item.get("source_anchor_evidence"),
            folder=folder,
            private_record=raw_item,
            sources=sources,
            label=label,
        )
        contexts, context_errors = _display_context_requirements(
            raw_item,
            public_item,
            folder=folder,
            sources=sources,
            label=label,
        )
        errors.extend(anchor_errors)
        errors.extend(context_errors)
        if anchor_errors or context_errors:
            continue
        item_payload: dict[str, Any] = {
            "source_anchors": anchors,
            "source_kind": str(public_item.get("source_kind") or "").strip(),
        }
        if contexts:
            item_payload["semantic_context"] = contexts
        selected_items[item_id] = item_payload
    if errors:
        raise PublicSourceDisplayProjectionError("; ".join(sorted(set(errors))))

    # This explicit false is a safety invariant rather than a convention: the
    # complete private text artifact is deliberately absent.  The only source
    # text carried here is the checked anchor excerpts above.
    return {
        "generator": PUBLIC_SOURCE_DISPLAY_PROJECTION_GENERATOR,
        "paper_id": folder.name,
        "private_source_map_sha256": hashlib.sha256(map_bytes).hexdigest(),
        "public_manifest_path": public_source_display_projection_public_path(folder),
        "public_source_map_sha256": hashlib.sha256(public_map_bytes).hexdigest(),
        "raw_source_artifact_included": False,
        "raw_source_display_material": "selected_byte_pinned_source_anchor_quotes",
        "schema": PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA,
        "selected_source_item_ids": selected_ids,
        "selected_source_items": selected_items,
        "source_artifact_sha256": source_sha256,
        "source_coverage_mode": mode,
    }


def public_source_display_projection_bytes(folder: Path) -> bytes:
    """Return canonical bytes for the current deterministic projection."""

    return _canonical_json_bytes(build_public_source_display_projection(folder))


def write_public_source_display_projection(folder: Path) -> Path:
    """Write the fixed paper-local projection after all private checks pass."""

    output = public_source_display_projection_path(folder)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(public_source_display_projection_bytes(folder))
    return output


def _anchor_validation_errors(
    actual: object,
    expected: object,
    *,
    label: str,
) -> list[str]:
    """Report a stale/altered displayed-anchor record before exact comparison."""

    if not isinstance(actual, list):
        return [f"{label} source_anchors is not a list"]
    if not isinstance(expected, list):  # Builder invariant, retained defensively.
        return [f"{label} expected source_anchors is not a list"]
    errors: list[str] = []
    if len(actual) != len(expected):
        errors.append(f"{label} source anchor count does not match current source map")
    for index, anchor in enumerate(actual):
        anchor_label = f"{label} source anchor {index}"
        if not isinstance(anchor, Mapping):
            errors.append(f"{anchor_label} is not an object")
            continue
        quote = anchor.get("quoted_text")
        recorded_sha = str(anchor.get("quoted_text_sha256") or "").strip().lower()
        if not isinstance(quote, str) or not quote:
            errors.append(f"{anchor_label} has no quoted_text")
        elif not _SHA256_RE.fullmatch(recorded_sha) or _sha256_text(quote) != recorded_sha:
            errors.append(f"{anchor_label} quoted_text_sha256 is invalid")
        if index < len(expected) and anchor != expected[index]:
            errors.append(f"{anchor_label} does not match the current source anchor")
    return errors


def _projection_payload_validation_errors(
    actual: object, expected: Mapping[str, Any]
) -> list[str]:
    """Validate semantic bindings with useful diagnostics before byte equality."""

    if not isinstance(actual, Mapping):
        return ["public source display projection is not a JSON object"]
    errors: list[str] = []
    for field in (
        "schema",
        "generator",
        "paper_id",
        "source_coverage_mode",
        "private_source_map_sha256",
        "public_source_map_sha256",
        "source_artifact_sha256",
        "public_manifest_path",
        "raw_source_artifact_included",
        "raw_source_display_material",
    ):
        if actual.get(field) != expected.get(field):
            errors.append(f"projection {field} does not match current private evidence")
    actual_ids = actual.get("selected_source_item_ids")
    expected_ids = expected.get("selected_source_item_ids")
    if actual_ids != expected_ids:
        errors.append("projection selected source-item IDs do not match current coverage semantics")
    actual_items = actual.get("selected_source_items")
    expected_items = expected.get("selected_source_items")
    if not isinstance(actual_items, Mapping):
        errors.append("projection selected_source_items is not an object")
        return errors
    if not isinstance(expected_items, Mapping):  # Builder invariant.
        errors.append("expected selected_source_items is not an object")
        return errors
    if set(actual_items) != set(expected_items):
        errors.append("projection selected source-item records do not match current coverage semantics")
    for item_id, expected_item in expected_items.items():
        actual_item = actual_items.get(item_id)
        label = f"selected source item `{item_id}`"
        if not isinstance(actual_item, Mapping):
            errors.append(f"{label} is missing from the projection")
            continue
        errors.extend(
            _anchor_validation_errors(
                actual_item.get("source_anchors"),
                expected_item.get("source_anchors"),
                label=label,
            )
        )
        actual_contexts = actual_item.get("semantic_context", [])
        expected_contexts = expected_item.get("semantic_context", [])
        if not isinstance(actual_contexts, list):
            errors.append(f"{label} semantic_context is not a list")
            continue
        if len(actual_contexts) != len(expected_contexts):
            errors.append(f"{label} semantic context count does not match current source map")
        for index, expected_context in enumerate(expected_contexts):
            context_label = f"{label} semantic context {index}"
            if index >= len(actual_contexts) or not isinstance(
                actual_contexts[index], Mapping
            ):
                errors.append(f"{context_label} is missing from the projection")
                continue
            actual_context = actual_contexts[index]
            if actual_context.get("semantic_role") != expected_context.get(
                "semantic_role"
            ):
                errors.append(f"{context_label} semantic_role does not match current source map")
            errors.extend(
                _anchor_validation_errors(
                    actual_context.get("source_anchors"),
                    expected_context.get("source_anchors"),
                    label=context_label,
                )
            )
    return sorted(set(errors))


def validate_public_source_display_projection(folder: Path) -> list[str]:
    """Return current-source validation issues for a saved display projection.

    Validation recomputes the display projection from the current private map
    and source bytes.  It therefore rechecks selected IDs, map/artifact hashes,
    coverage mode, direct and contextual anchor quote SHA-256s, and canonical
    deterministic serialization.
    """

    try:
        expected = build_public_source_display_projection(folder)
        expected_bytes = _canonical_json_bytes(expected)
    except PublicSourceDisplayProjectionError as exc:
        return [str(exc)]
    path = public_source_display_projection_path(folder)
    try:
        actual_bytes = path.read_bytes()
    except OSError as exc:
        return [f"cannot read {PUBLIC_SOURCE_DISPLAY_PROJECTION_FILE}: {exc}"]
    try:
        actual = json.loads(actual_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        return [f"{PUBLIC_SOURCE_DISPLAY_PROJECTION_FILE} is not valid UTF-8 JSON: {exc}"]
    errors = _projection_payload_validation_errors(actual, expected)
    if actual_bytes != expected_bytes:
        errors.append(
            "public source display projection is not the current deterministic serialization"
        )
    return sorted(set(errors))


def _paper_folder_from_id(paper_id: str) -> Path:
    value = str(paper_id or "").strip()
    if not value or Path(value).name != value:
        raise PublicSourceDisplayProjectionError("--paper must be one paper directory name")
    folder = PAPERS_DIR / value
    if not folder.is_dir():
        raise PublicSourceDisplayProjectionError(f"unknown paper `{value}`")
    return folder


def main(argv: Sequence[str] | None = None) -> int:
    """CLI entry point: write, check, or print one deterministic projection."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True, help="paper directory name under papers/")
    action = parser.add_mutually_exclusive_group()
    action.add_argument(
        "--write",
        action="store_true",
        help=f"write {PUBLIC_SOURCE_DISPLAY_PROJECTION_FILE}",
    )
    action.add_argument(
        "--check",
        action="store_true",
        help="validate the saved projection against current private evidence",
    )
    args = parser.parse_args(argv)
    try:
        folder = _paper_folder_from_id(args.paper)
        if args.write:
            output = write_public_source_display_projection(folder)
            try:
                print(output.relative_to(ROOT))
            except ValueError:
                # The importable API deliberately supports an isolated paper
                # folder in tests and release staging tools.
                print(output)
            return 0
        if args.check:
            issues = validate_public_source_display_projection(folder)
            if issues:
                for issue in issues:
                    print(f"error: {issue}", file=sys.stderr)
                return 1
            print(f"{PUBLIC_SOURCE_DISPLAY_PROJECTION_FILE}: current")
            return 0
        sys.stdout.buffer.write(public_source_display_projection_bytes(folder))
        return 0
    except PublicSourceDisplayProjectionError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":  # pragma: no cover - exercised through ``main``.
    raise SystemExit(main())
