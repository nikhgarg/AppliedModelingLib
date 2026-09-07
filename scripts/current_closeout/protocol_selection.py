#!/usr/bin/env python3
"""Select the one current closeout protocol from explicit paper inputs.

Current closeout does not inspect trusted historical trees or infer an engine
pair transition.  A paper with an accepted historical graph returns through
the canonical receipt validator before prospective planning.  Every other
paper either exposes the graph-native source-to-Spec contract in its current
status/map or receives the ordinary migration action.

This module performs no I/O, Lean work, evidence validation, or semantic
judgment.  It is deliberately safe to import from the planner and exact-input
transaction builder.
"""

from __future__ import annotations

from scripts.source_coverage_scope import (
    explicit_raw_source_spec_screening_requested,
)


def current_v11_protocol_selected(
    status_payload: object,
    source_map_payload: object | None = None,
) -> bool:
    """Return whether current inputs explicitly select graph-native closeout."""

    return explicit_raw_source_spec_screening_requested(
        status_payload,
        source_map_payload,
    )
