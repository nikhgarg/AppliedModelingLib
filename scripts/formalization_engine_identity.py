#!/usr/bin/env python3
"""Validate the registered closeout-engine identity.

This module is deliberately independent of historical closeout-wave and raw
source-record machinery.  Current closeout consumers need only the clean,
registered engine projection; importing that projection must not initialize or
expose a legacy transition protocol.
"""

from __future__ import annotations

from pathlib import Path
from typing import Mapping

try:
    from scripts.check_formalization_engine_revision import (
        EngineRevisionError,
        validate_runtime_engine_registration,
    )
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from check_formalization_engine_revision import (
        EngineRevisionError,
        validate_runtime_engine_registration,
    )


_ENGINE_PROJECTION_FIELDS = (
    "engine_tree_sha256",
    "review_semantic_class_sha256",
    "revision_sequence",
    "registration_kind",
    "engine_file_count",
)


def _valid_sha256(value: object) -> bool:
    text = str(value or "").strip().lower()
    return len(text) == 64 and all(
        character in "0123456789abcdef" for character in text
    )


def normalized_engine_projection(value: object) -> tuple[dict[str, object] | None, str]:
    """Validate the exact registered-engine fields used by closeout."""

    if not isinstance(value, Mapping):
        return None, "engine projection is not an object"
    projection = {field: value.get(field) for field in _ENGINE_PROJECTION_FIELDS}
    if projection["registration_kind"] is None and isinstance(
        value.get("relation_to_previous"), str
    ):
        # Read an old operational snapshot long enough for legacy tooling to
        # identify it.  This does not authorize an engine-pair bridge.
        projection["registration_kind"] = "legacy_linked_revision"
    if not _valid_sha256(projection["engine_tree_sha256"]):
        return None, "engine projection has an invalid engine_tree_sha256"
    if not _valid_sha256(projection["review_semantic_class_sha256"]):
        return None, "engine projection has an invalid review_semantic_class_sha256"
    if not isinstance(projection["revision_sequence"], int) or projection[
        "revision_sequence"
    ] < 1:
        return None, "engine projection has an invalid revision_sequence"
    if not isinstance(projection["registration_kind"], str) or not projection[
        "registration_kind"
    ].strip():
        return None, "engine projection has an invalid registration_kind"
    if not isinstance(projection["engine_file_count"], int) or projection[
        "engine_file_count"
    ] < 0:
        return None, "engine projection has an invalid engine_file_count"
    return projection, ""


def current_registered_engine_projection(
    root: Path,
) -> tuple[dict[str, object] | None, str]:
    """Return the clean, registered engine projection, or a stable error."""

    try:
        registration = validate_runtime_engine_registration(root.resolve())
    except EngineRevisionError as exc:
        return None, str(exc)
    projection, error = normalized_engine_projection(
        {
            "engine_tree_sha256": registration.engine_tree_sha256,
            "review_semantic_class_sha256": registration.review_semantic_class_sha256,
            "revision_sequence": registration.revision_sequence,
            "registration_kind": registration.registration_kind,
            "engine_file_count": registration.engine_file_count,
        }
    )
    if projection is None:
        return None, "registered engine projection is malformed: " + error
    return projection, ""
