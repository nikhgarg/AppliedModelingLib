"""Deterministic projection of settled maintainer decisions into review input."""

from __future__ import annotations

import copy
import json
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from scripts.source_review_input import (
    APPROVED_REVIEW_CONTEXTS_FIELD,
    APPROVED_REVIEW_CONTEXT_SCHEMA_FIELD,
    materialize_approved_review_contexts,
)

ROOT_SCHEMA_FIELD = "approved_review_context_schema"
AUTHORITY_FIELDS = (
    "model_convention_ids",
    "accepted_additional_assumptions",
)


def _load_object(path: Path, *, required: bool) -> tuple[Mapping[str, Any] | None, str]:
    if not path.is_file() and not required:
        return None, ""
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        return None, f"could not read {path.name}: {exc}"
    if not isinstance(payload, Mapping):
        return None, f"{path.name} is not an object"
    return payload, ""


def expected_approved_review_context_projection(
    folder: Path,
    source_map: Mapping[str, Any],
) -> tuple[dict[str, Any] | None, str]:
    """Build the exact approval-only source-map projection for closeout.

    This deliberately does not infer a mathematical relationship from prose.
    Curators cite stable convention ids on source items. The v11 preparation
    config is consulted only to carry such explicit citations onto newly
    introduced source items before their first review.
    """

    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping) or any(
        not isinstance(item, Mapping) for item in raw_items.values()
    ):
        return None, "paper statement map has no valid items object"
    items = {
        str(key): copy.deepcopy(dict(item))
        for key, item in raw_items.items()
        if isinstance(item, Mapping)
    }

    config, error = _load_object(
        folder / "audit" / "v11_source_map_preparation_config.json",
        required=False,
    )
    if error:
        return None, error
    if config is not None:
        configured_items = config.get("add_source_items", {})
        if not isinstance(configured_items, Mapping):
            return None, "v11 source-map preparation config has invalid add_source_items"
        for raw_key, raw_configured in configured_items.items():
            if not isinstance(raw_configured, Mapping):
                return None, f"configured source item `{raw_key}` is not an object"
            if "model_convention_ids" not in raw_configured:
                continue
            key = str(raw_key)
            if key not in items:
                return None, (
                    f"configured source item `{key}` is absent; run the tracked "
                    "v11 source-map preparer before closeout"
                )
            items[key]["model_convention_ids"] = copy.deepcopy(
                raw_configured["model_convention_ids"]
            )
        configured_routes = config.get(
            "model_convention_ids_by_source_item", {}
        )
        if not isinstance(configured_routes, Mapping):
            return None, (
                "v11 source-map preparation config has invalid "
                "model_convention_ids_by_source_item"
            )
        for raw_key, raw_ids in configured_routes.items():
            key = str(raw_key).strip()
            if not key or key not in items:
                return None, (
                    "configured model-convention route names absent source item "
                    f"`{key}`"
                )
            items[key]["model_convention_ids"] = copy.deepcopy(raw_ids)

    needs_ledger = any("model_convention_ids" in item for item in items.values())
    ledger: Mapping[str, Any] | None = None
    if needs_ledger:
        ledger, error = _load_object(
            folder / "audit" / "source_proof_fidelity.json",
            required=True,
        )
        if error:
            return None, error

    projected_items: dict[str, dict[str, Any]] = {}
    for key, item in sorted(items.items()):
        contexts, error = materialize_approved_review_contexts(
            item,
            source_proof_fidelity=ledger,
        )
        if error:
            return None, f"source item `{key}`: {error}"
        projection = {
            field: copy.deepcopy(item[field])
            for field in AUTHORITY_FIELDS
            if field in item
        }
        if contexts:
            projection[APPROVED_REVIEW_CONTEXT_SCHEMA_FIELD] = 1
            projection[APPROVED_REVIEW_CONTEXTS_FIELD] = contexts
        if projection:
            projected_items[key] = projection
    return {
        ROOT_SCHEMA_FIELD: 1,
        "items": projected_items,
    }, ""


def current_approved_review_context_projection(
    source_map: Mapping[str, Any],
) -> dict[str, Any]:
    """Extract the approval-only projection from a prepared source map."""

    raw_items = source_map.get("items")
    items = raw_items if isinstance(raw_items, Mapping) else {}
    projected_items: dict[str, dict[str, Any]] = {}
    fields = AUTHORITY_FIELDS + (
        APPROVED_REVIEW_CONTEXT_SCHEMA_FIELD,
        APPROVED_REVIEW_CONTEXTS_FIELD,
    )
    for raw_key, raw_item in sorted(items.items(), key=lambda pair: str(pair[0])):
        if not isinstance(raw_item, Mapping):
            continue
        projection = {
            field: copy.deepcopy(raw_item[field])
            for field in fields
            if field in raw_item
        }
        if projection:
            projected_items[str(raw_key)] = projection
    return {
        ROOT_SCHEMA_FIELD: source_map.get(ROOT_SCHEMA_FIELD),
        "items": projected_items,
    }


def apply_approved_review_context_projection(
    source_map: Mapping[str, Any],
    projection: Mapping[str, Any],
) -> dict[str, Any]:
    """Return a source map changed only in approval-projection fields."""

    result = copy.deepcopy(dict(source_map))
    raw_items = result.get("items")
    if not isinstance(raw_items, dict):
        raise ValueError("paper statement map has no mutable items object")
    projected_items = projection.get("items")
    if not isinstance(projected_items, Mapping):
        raise ValueError("approved review context projection has no items object")
    fields = AUTHORITY_FIELDS + (
        APPROVED_REVIEW_CONTEXT_SCHEMA_FIELD,
        APPROVED_REVIEW_CONTEXTS_FIELD,
    )
    for item in raw_items.values():
        if isinstance(item, dict):
            for field in fields:
                item.pop(field, None)
    for raw_key, raw_projection in projected_items.items():
        key = str(raw_key)
        if key not in raw_items or not isinstance(raw_items[key], dict):
            raise ValueError(f"approved review context source item `{key}` is absent")
        if not isinstance(raw_projection, Mapping):
            raise ValueError(f"approved review context source item `{key}` is invalid")
        for field in fields:
            if field in raw_projection:
                raw_items[key][field] = copy.deepcopy(raw_projection[field])
    result[ROOT_SCHEMA_FIELD] = 1
    return result


__all__ = [
    "apply_approved_review_context_projection",
    "current_approved_review_context_projection",
    "expected_approved_review_context_projection",
]
