#!/usr/bin/env python3
"""Portable identity of the Lean-owned declaration-graph producer.

The graph request and imported Lean closure are bound separately by the v11
checkpoint.  This module therefore identifies only code that can change the
Lean graph's mathematical output: the native declaration graph, the semantic
signature implementation it imports, and the exact semantic-hash tool selected
by that request.

Python transport, validators, caches, packets, and legacy manifest helpers are
deliberately outside this identity.  They revalidate a retained graph but do
not produce its declaration closure.  A change to one of those consumers must
not discard a multi-minute Lean acquisition.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
from typing import Mapping


LEAN_DECLARATION_GRAPH_PRODUCER_SOURCES = (
    "AppliedModelingLib/Audit/DeclarationGraph.lean",
    "AppliedModelingLib/Audit/SignatureManifest.lean",
    "scripts/lean_signature_manifest_helper.lean",
)


def lean_declaration_graph_producer_identity(
    root: Path,
    *,
    semantic_hash_tool_identity: Mapping[str, object],
) -> dict[str, object]:
    """Return the exact portable identity of the native graph producer.

    The caller owns the typed request and Lean import-closure identities.  This
    function owns no cache and performs no discovery; it only fingerprints the
    native implementation that interprets that request.
    """

    repository = root.resolve()
    rows: list[dict[str, object]] = []
    for relative in LEAN_DECLARATION_GRAPH_PRODUCER_SOURCES:
        path = repository / relative
        try:
            content = path.read_bytes()
        except OSError as exc:
            raise ValueError(
                f"Lean declaration-graph producer source is unavailable: {relative}"
            ) from exc
        rows.append(
            {
                "path": relative,
                "sha256": hashlib.sha256(content).hexdigest(),
                "byte_length": len(content),
            }
        )
    if not semantic_hash_tool_identity:
        raise ValueError("Lean declaration-graph semantic hash tool is unavailable")
    return {
        "schema": 1,
        "sources": rows,
        "semantic_hash_tool_identity": dict(semantic_hash_tool_identity),
    }
