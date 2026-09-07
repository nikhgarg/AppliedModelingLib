#!/usr/bin/env python3
"""Current repository material for exact obligation-semantic rebinding.

This module is an I/O adapter, not an acceptance authority. It resolves exact
source bundles from the frozen paper transaction and returns the small typed
projection consumed by the pure resolver. Declaration semantics and ownership
come from the retained Lean graph, not from this module.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.obligation_resolution import (
    CurrentSourceSemanticMaterial,
)
from scripts.source_review_input import (
    source_anchor_file_error,
    source_semantic_input_bundle,
)


class ObligationCurrentMaterialError(ValueError):
    """Current source material cannot be reproduced exactly."""


def current_source_semantic_material(
    *,
    paper_dir: Path,
    source_map: object,
    source_route_navigation: Mapping[str, tuple[str, ...]],
) -> Mapping[str, CurrentSourceSemanticMaterial]:
    """Recompute every exact source bundle around already projected atom leaves."""

    if not isinstance(source_map, Mapping) or not isinstance(
        source_map.get("items"), Mapping
    ):
        raise ObligationCurrentMaterialError("paper statement map has no item ledger")
    items = source_map["items"]
    if set(items) != set(source_route_navigation):
        raise ObligationCurrentMaterialError(
            "source-route projection differs from current statement map"
        )
    result: dict[str, CurrentSourceSemanticMaterial] = {}
    for raw_source_item_id, raw_item in sorted(items.items(), key=lambda entry: str(entry[0])):
        source_item_id = str(raw_source_item_id)
        if not isinstance(raw_item, Mapping):
            raise ObligationCurrentMaterialError(
                f"source item {source_item_id} is not an object"
            )
        source_error = source_anchor_file_error(paper_dir, raw_item)
        if source_error:
            raise ObligationCurrentMaterialError(
                f"source item {source_item_id}: {source_error}"
            )
        _text, source_digest, source_error = (
            source_semantic_input_bundle(
                raw_item,
                require_context_roles=True,
            )
        )
        if source_error or not source_digest:
            raise ObligationCurrentMaterialError(
                f"source item {source_item_id}: "
                + (source_error or "source bundle digest is unavailable")
            )
        result[source_item_id] = CurrentSourceSemanticMaterial(
            source_input_bundle_sha256=source_digest,
            source_atom_leaf_sha256s=source_route_navigation[source_item_id],
        )
    return result
