"""Read and authenticate public source excerpts for display only.

The local byte validator remains the first path. A valid recorded public
manifest permits an exact excerpt display, never source-byte or audit credit.
The shared immutable read context preserves frozen historical readers without
depending on the dashboard registry or any discovery/producer implementation.
"""
from __future__ import annotations

import hashlib
import re
from pathlib import Path
from typing import Any, Mapping

from scripts.dashboard_audit_inputs import (
    _dashboard_file_bytes_override,
    _dashboard_json_payload,
    _dashboard_read_bytes,
)
from scripts.semantic_prerequisite_projection import (
    LOCAL_SOURCE_CONNECTION_STATE,
    PUBLIC_SOURCE_DISPLAY_PROJECTION_STATE,
)
from scripts.source_coverage_scope import source_coverage_mode_from_map
from scripts.source_review_input import (
    SEMANTIC_CONTEXT_ROLES,
    source_anchor_file_error,
    source_semantic_input_bundle,
)

PAPER_STATEMENT_MAP_FILE = "audit/paper_statement_map.json"
PUBLIC_SOURCE_DISPLAY_PROJECTION_FILE = "audit/public_source_display_projection.json"
PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA = 1
PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD = "publication_source_display_projection"
PUBLIC_SOURCE_DISPLAY_PROJECTION_GENERATOR = "python3 scripts/public_source_display_projection.py"
PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST = "audit/public_source_display_projection.json"
PUBLICATION_SOURCE_LOCATOR = "cited publication"

def _public_display_anchor_bundle(
    anchors: object,
    *,
    label: str,
) -> tuple[tuple[tuple[int, int, str, str, str], ...], str]:
    """Return one safe public-excerpt anchor bundle, or a precise error.

    This is intentionally not a substitute for :func:`source_anchor_file_error`.
    It validates only the self-contained release excerpt identity that a public
    packet can display after the private audit has removed the source file.
    """

    if not isinstance(anchors, list) or not anchors:
        return (), f"{label} has no source anchors"
    out: list[tuple[int, int, str, str, str]] = []
    for index, raw_anchor in enumerate(anchors):
        anchor_label = f"{label} source anchor {index}"
        if not isinstance(raw_anchor, Mapping):
            return (), f"{anchor_label} is not an object"
        # A public display projection must never retain a filesystem path.  A
        # map that still has one must use the strict local-byte path instead.
        if "path" in raw_anchor:
            return (), f"{anchor_label} retains a local source path"
        line_start = raw_anchor.get("line_start")
        line_end = raw_anchor.get("line_end")
        locator = str(raw_anchor.get("publication_locator") or "").strip()
        quote = raw_anchor.get("quoted_text")
        digest = str(raw_anchor.get("quoted_text_sha256") or "").strip().lower()
        if (
            not isinstance(line_start, int)
            or isinstance(line_start, bool)
            or line_start < 1
            or not isinstance(line_end, int)
            or isinstance(line_end, bool)
            or line_end < line_start
        ):
            return (), f"{anchor_label} lacks a valid line span"
        if locator != PUBLICATION_SOURCE_LOCATOR:
            return (), f"{anchor_label} has no public publication locator"
        if not isinstance(quote, str) or not quote:
            return (), f"{anchor_label} has no quoted_text"
        normalized_quote = quote.replace("\r\n", "\n").replace("\r", "\n")
        actual_digest = hashlib.sha256(normalized_quote.encode("utf-8")).hexdigest()
        if not re.fullmatch(r"[0-9a-f]{64}", digest) or digest != actual_digest:
            return (), f"{anchor_label} quoted_text_sha256 is stale"
        out.append((line_start, line_end, locator, normalized_quote, digest))
    return tuple(out), ""


def _public_display_context_bundles(
    record: Mapping[str, Any],
    *,
    field: str,
    label: str,
) -> tuple[tuple[tuple[str, tuple[tuple[int, int, str, str, str], ...]], ...], str]:
    """Return ordered display-only semantic-context identities.

    ``paper_statement_map.json`` uses ``semantic_context_requirements``;
    the frozen public manifest uses the shorter ``semantic_context``.  The
    two representations intentionally carry only a role and exact anchors.
    """

    raw_contexts = record.get(field)
    if raw_contexts is None:
        return (), ""
    if not isinstance(raw_contexts, list):
        return (), f"{label} {field} is not a list"
    out: list[tuple[str, tuple[tuple[int, int, str, str, str], ...]]] = []
    for index, raw_context in enumerate(raw_contexts):
        context_label = f"{label} semantic context {index}"
        if not isinstance(raw_context, Mapping):
            return (), f"{context_label} is not an object"
        role = str(raw_context.get("semantic_role") or "").strip()
        if role not in SEMANTIC_CONTEXT_ROLES:
            return (), f"{context_label} has no permitted semantic_role"
        anchors, error = _public_display_anchor_bundle(
            raw_context.get("source_anchor_evidence")
            if field == "semantic_context_requirements"
            else raw_context.get("source_anchors"),
            label=context_label,
        )
        if error:
            return (), error
        out.append((role, anchors))
    return tuple(out), ""


def _public_display_record_matches_manifest(
    source_record: Mapping[str, Any],
    manifest_item: Mapping[str, Any],
    *,
    label: str,
) -> str:
    """Check one projected source record against its frozen manifest entry."""

    actual_anchors, actual_error = _public_display_anchor_bundle(
        source_record.get("source_anchor_evidence"), label=label
    )
    if actual_error:
        return actual_error
    expected_anchors, expected_error = _public_display_anchor_bundle(
        manifest_item.get("source_anchors"), label=f"{label} manifest"
    )
    if expected_error:
        return expected_error
    if actual_anchors != expected_anchors:
        return f"{label} source anchors do not match the frozen public manifest"
    actual_contexts, actual_context_error = _public_display_context_bundles(
        source_record,
        field="semantic_context_requirements",
        label=label,
    )
    if actual_context_error:
        return actual_context_error
    expected_contexts, expected_context_error = _public_display_context_bundles(
        manifest_item,
        field="semantic_context",
        label=f"{label} manifest",
    )
    if expected_context_error:
        return expected_context_error
    if actual_contexts != expected_contexts:
        return f"{label} semantic context does not match the frozen public manifest"
    return ""


def public_source_display_projection_state(folder: Path) -> dict[str, Any]:
    """Validate a release-only source-excerpt manifest without source bytes.

    The private audit's byte-level source checks intentionally do *not* call
    this helper.  It exists solely for a public dashboard/packet to identify a
    cryptographically bound, frozen display surface after raw source files and
    private source paths have been omitted from the release.
    """

    source_map = _dashboard_json_payload(folder / PAPER_STATEMENT_MAP_FILE) or {}
    marker = source_map.get(PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD)
    if marker is None:
        return {
            "active": False,
            "valid": False,
            "errors": (),
            "selected_source_item_ids": (),
            "source_coverage_mode": "",
        }
    errors: list[str] = []
    if not isinstance(marker, Mapping):
        errors.append("public source display marker is not an object")
    else:
        if marker.get("schema") != PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA:
            errors.append("public source display marker has an unsupported schema")
        if marker.get("manifest") != PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST:
            errors.append("public source display marker names an unexpected manifest")
        if marker.get("raw_source_bytes_included") is not False:
            errors.append("public source display marker does not declare omitted raw source bytes")

    map_path = folder / PAPER_STATEMENT_MAP_FILE
    try:
        map_sha256 = hashlib.sha256(_dashboard_read_bytes(map_path)).hexdigest()
    except OSError as exc:
        errors.append("cannot read public paper statement map: " + str(exc))
        map_sha256 = ""
    manifest_path = folder / PUBLIC_SOURCE_DISPLAY_PROJECTION_FILE
    manifest = _dashboard_json_payload(manifest_path)
    if manifest is None:
        errors.append("public source display manifest is unreadable")
        manifest = {}

    expected_manifest_path = (
        f"papers/{folder.name}/{PUBLIC_SOURCE_DISPLAY_PROJECTION_FILE}"
    )
    source_mode, source_mode_error = source_coverage_mode_from_map(source_map)
    if source_mode_error:
        errors.append("public source display map has an invalid source coverage mode")
    if manifest:
        if manifest.get("schema") != PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA:
            errors.append("public source display manifest has an unsupported schema")
        if manifest.get("generator") != PUBLIC_SOURCE_DISPLAY_PROJECTION_GENERATOR:
            errors.append("public source display manifest has an unexpected generator")
        if str(manifest.get("paper_id") or "").strip() != folder.name:
            errors.append("public source display manifest names a different paper")
        if manifest.get("public_manifest_path") != expected_manifest_path:
            errors.append("public source display manifest has an unexpected public path")
        if manifest.get("raw_source_artifact_included") is not False:
            errors.append("public source display manifest does not declare omitted raw source bytes")
        if (
            manifest.get("raw_source_display_material")
            != "selected_byte_pinned_source_anchor_quotes"
        ):
            errors.append("public source display manifest has an unexpected source material policy")
        if str(manifest.get("public_source_map_sha256") or "").strip().lower() != map_sha256:
            errors.append("public source display manifest does not match the public source map")
        for field in (
            "private_source_map_sha256",
            "public_source_map_sha256",
            "source_artifact_sha256",
        ):
            if not re.fullmatch(
                r"[0-9a-f]{64}", str(manifest.get(field) or "").strip().lower()
            ):
                errors.append(f"public source display manifest has no valid {field}")
        if source_mode and manifest.get("source_coverage_mode") != source_mode:
            errors.append("public source display manifest source coverage mode differs from the map")

    raw_ids = manifest.get("selected_source_item_ids") if manifest else None
    raw_items = manifest.get("selected_source_items") if manifest else None
    selected_ids: list[str] = []
    if not isinstance(raw_ids, list):
        errors.append("public source display manifest selected_source_item_ids is not a list")
    else:
        selected_ids = [str(item_id).strip() for item_id in raw_ids]
        if any(not item_id for item_id in selected_ids):
            errors.append("public source display manifest has an empty selected source-item ID")
        if selected_ids != sorted(selected_ids) or len(selected_ids) != len(set(selected_ids)):
            errors.append("public source display manifest selected source-item IDs are not unique sorted IDs")
    if not isinstance(raw_items, Mapping):
        errors.append("public source display manifest selected_source_items is not an object")
        raw_items = {}
    if set(raw_items) != set(selected_ids):
        errors.append("public source display manifest item records do not match selected source-item IDs")
    map_items = source_map.get("items") if isinstance(source_map.get("items"), Mapping) else {}
    for item_id in selected_ids:
        map_item = map_items.get(item_id)
        manifest_item = raw_items.get(item_id)
        if not isinstance(map_item, Mapping):
            errors.append(f"public source display item `{item_id}` is absent from the map")
            continue
        if not isinstance(manifest_item, Mapping):
            errors.append(f"public source display item `{item_id}` is not an object")
            continue
        error = _public_display_record_matches_manifest(
            map_item,
            manifest_item,
            label=f"public source display item `{item_id}`",
        )
        if error:
            errors.append(error)

    valid = not errors
    return {
        "active": True,
        "valid": valid,
        "errors": tuple(sorted(set(errors))),
        "manifest": manifest if valid else {},
        "selected_source_item_ids": tuple(selected_ids) if valid else (),
        "source_coverage_mode": source_mode if valid else "",
        "state": PUBLIC_SOURCE_DISPLAY_PROJECTION_STATE if valid else "",
    }


def public_source_display_coverage_surface(folder: Path) -> dict[str, Any]:
    """Return the frozen source-item denominator for browser display only.

    This helper intentionally does not call :func:`paper_coverage_inventory`.
    In a public release there is no raw source artifact to re-index, and using
    this frozen selection must never make a CLI source-index or audit gate pass.
    """

    state = public_source_display_projection_state(folder)
    if not state.get("valid"):
        return {
            "available": False,
            "state": "",
            "selected_source_item_ids": (),
            "source_item_count": 0,
            "source_coverage_mode": "",
            "display_only": False,
            "raw_source_locally_revalidated": False,
            "audit_current": False,
        }
    selected_ids = tuple(state.get("selected_source_item_ids") or ())
    return {
        "available": True,
        "state": PUBLIC_SOURCE_DISPLAY_PROJECTION_STATE,
        "selected_source_item_ids": selected_ids,
        "source_item_count": len(selected_ids),
        "source_coverage_mode": str(state.get("source_coverage_mode") or ""),
        "display_only": True,
        "raw_source_locally_revalidated": False,
        "audit_current": False,
    }


def source_anchor_display_state(
    folder: Path,
    source_record: Mapping[str, Any],
    *,
    source_item_key: str = "",
) -> tuple[str, str]:
    """Return a rendering-only source-connection state or the strict error.

    A local checkout always takes the exact byte-reading path first.  Only a
    valid public marker plus a manifest whose excerpts exactly bind this
    record can use ``release_projected_excerpt``.  Callers must keep that
    state display-only; it is not a current audit or source-byte receipt.
    """

    strict_error = source_anchor_file_error(
        folder, source_record, file_bytes_override=_dashboard_file_bytes_override()
    )
    if not strict_error:
        return LOCAL_SOURCE_CONNECTION_STATE, ""
    state = public_source_display_projection_state(folder)
    if not state.get("valid"):
        return "", strict_error
    manifest = state.get("manifest")
    selected_items = (
        manifest.get("selected_source_items")
        if isinstance(manifest, Mapping)
        and isinstance(manifest.get("selected_source_items"), Mapping)
        else {}
    )
    key = str(source_item_key or "").strip()
    if key and isinstance(selected_items.get(key), Mapping):
        error = _public_display_record_matches_manifest(
            source_record,
            selected_items[key],
            label=f"source item `{key}`",
        )
        if not error:
            return PUBLIC_SOURCE_DISPLAY_PROJECTION_STATE, ""
    # A material library primitive may be connected directly to a source
    # definition that serves as context for a selected source claim rather
    # than to that claim's primary presentation.  Allow that exact individual
    # excerpt bundle too, but never a subset or a rearrangement of a bundle.
    actual_anchors, actual_error = _public_display_anchor_bundle(
        source_record.get("source_anchor_evidence"), label="source connection"
    )
    actual_contexts, actual_context_error = _public_display_context_bundles(
        source_record,
        field="semantic_context_requirements",
        label="source connection",
    )
    if not actual_error and not actual_context_error and not actual_contexts:
        for item_id, raw_item in selected_items.items():
            if not isinstance(raw_item, Mapping):
                continue
            expected_anchors, expected_error = _public_display_anchor_bundle(
                raw_item.get("source_anchors"),
                label=f"public source display item `{item_id}`",
            )
            if not expected_error and actual_anchors == expected_anchors:
                return PUBLIC_SOURCE_DISPLAY_PROJECTION_STATE, ""
            raw_contexts = raw_item.get("semantic_context")
            if not isinstance(raw_contexts, list):
                continue
            for context_index, raw_context in enumerate(raw_contexts):
                if not isinstance(raw_context, Mapping):
                    continue
                context_anchors, context_error = _public_display_anchor_bundle(
                    raw_context.get("source_anchors"),
                    label=(
                        f"public source display item `{item_id}` "
                        f"semantic context {context_index}"
                    ),
                )
                if not context_error and actual_anchors == context_anchors:
                    return PUBLIC_SOURCE_DISPLAY_PROJECTION_STATE, ""
    return "", strict_error


def _project_public_library_source_excerpts(
    folder: Path,
    entries: list[dict[str, Any]],
    *,
    ledger_items: Mapping[str, Any],
    source_items: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """Populate release excerpts for display without granting audit credit."""

    for entry in entries:
        if not entry.get("source_connection_error"):
            continue
        lean_name = str(entry.get("lean_name") or "").strip()
        raw = ledger_items.get(lean_name)
        if not isinstance(raw, Mapping):
            raw = next(
                (
                    candidate
                    for candidate in ledger_items.values()
                    if isinstance(candidate, Mapping)
                    and str(candidate.get("library_declaration") or "").strip()
                    == lean_name
                ),
                {},
            )
        raw = raw if isinstance(raw, Mapping) else {}
        source_item_key = str(entry.get("source_item") or "").strip()
        source_record = source_items.get(source_item_key)
        if source_record is None and isinstance(raw.get("source_anchor_evidence"), list):
            source_record = raw
        if source_record is None:
            continue
        state, display_error = source_anchor_display_state(
            folder,
            source_record,
            source_item_key=source_item_key,
        )
        if display_error or state != PUBLIC_SOURCE_DISPLAY_PROJECTION_STATE:
            continue
        source_input, source_digest, bundle_error = source_semantic_input_bundle(
            source_record, require_context_roles=True
        )
        if bundle_error:
            continue
        entry.update(
            {
                "verbatim_source_input": source_input,
                "source_input_bundle_sha256": source_digest,
                "source_connection_error": "",
                "source_connection_state": state,
                "source_connection_display_only": True,
                "semantic_current": False,
                "semantic_status": "release-projected excerpt (display only)",
            }
        )
    return entries
