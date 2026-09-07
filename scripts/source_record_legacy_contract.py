#!/usr/bin/env python3
"""Immutable schema constants shared with the historical source-record lane.

Current-v11 audit code may need these values to read old configured status or
to preserve public module exports, but it must not import the historical raw
receipt readers, replay engines, overlays, or migration CLIs merely to obtain a
string or tuple.  Keep this module data-only.
"""

from __future__ import annotations


SOURCE_RECORD_ITEM_DIGEST_SCHEMA = 5

SOURCE_RECORD_REUSABLE_ITEM_SECTIONS = (
    "boundary_input_items",
    "theorem_facing_input_items",
    "conclusion_dependency_items",
    "type_valued_certificate_result_items",
    "recursive_field_items",
    "semantic_model_items",
    "source_premise_consistency_items",
)

SOURCE_RECORD_SEMANTIC_REUSE_POLICY = (
    "current-verifier-canonical-semantic-reuse-v1"
)
SOURCE_RECORD_SEMANTIC_VALIDATION_BASENAME = (
    "source_record_semantic_validation.json"
)

SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME = (
    "source_record_administrative_projection_rebind.json"
)

EXPLICIT_DIRECT_SOURCE_ROUTE_ORIGIN = "explicit_source_map_direct_route"
EXPLICIT_DIRECT_SOURCE_ROUTE_ROLE = "direct_source_route"
SOURCE_CLAIM_ATOM_ROUTE_ORIGIN = "source_claim_atom_route"
SOURCE_CLAIM_ATOM_ROUTE_ROLE = "source_claim_atom_route"
SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD = "source_claim_atom_association"


__all__ = (
    "EXPLICIT_DIRECT_SOURCE_ROUTE_ORIGIN",
    "EXPLICIT_DIRECT_SOURCE_ROUTE_ROLE",
    "SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD",
    "SOURCE_CLAIM_ATOM_ROUTE_ORIGIN",
    "SOURCE_CLAIM_ATOM_ROUTE_ROLE",
    "SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME",
    "SOURCE_RECORD_ITEM_DIGEST_SCHEMA",
    "SOURCE_RECORD_REUSABLE_ITEM_SECTIONS",
    "SOURCE_RECORD_SEMANTIC_REUSE_POLICY",
    "SOURCE_RECORD_SEMANTIC_VALIDATION_BASENAME",
)
