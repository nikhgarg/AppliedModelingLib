#!/usr/bin/env python3
"""Validate historical raw-producer provenance records.

The source-record fingerprint keeps exact producer code identities for
forensic provenance. Historical engine revisions also contain the former
producer-specific compatibility grants, whose shape remains append-only and is
validated here. Cache admission no longer traverses those grants: the one
registered formalization-engine classification and the exact non-producer
fingerprint are the current authorities.
"""

from __future__ import annotations

from typing import Mapping

try:
    from scripts.source_record_producer_provenance import raw_producer_identity_set
except ModuleNotFoundError:  # pragma: no cover - direct-script import support.
    from source_record_producer_provenance import raw_producer_identity_set


RAW_PRODUCER_COMPATIBILITY_SCHEMA = 1
RAW_PRODUCER_COMPATIBILITY_INVARIANT = (
    "same-nonproducer-source-record-fingerprint-v1"
)
RAW_PRODUCER_COMPATIBILITY_FIELD = "raw_producer_compatibility"


def raw_producer_compatibility_grant_error(value: object) -> str:
    """Return a structural error for one append-only compatibility grant."""

    if not isinstance(value, Mapping):
        return "raw-producer compatibility grant is not an object"
    expected_fields = {
        "schema",
        "invariant",
        "predecessor_raw_producer_code_identity_sets",
        "successor_raw_producer_code_identities",
    }
    if set(value) != expected_fields:
        return "raw-producer compatibility grant fields are malformed"
    if value.get("schema") != RAW_PRODUCER_COMPATIBILITY_SCHEMA:
        return "raw-producer compatibility grant has an unsupported schema"
    if value.get("invariant") != RAW_PRODUCER_COMPATIBILITY_INVARIANT:
        return "raw-producer compatibility grant has an unsupported invariant"
    predecessors = value.get("predecessor_raw_producer_code_identity_sets")
    if not isinstance(predecessors, list) or not predecessors:
        return "raw-producer compatibility grant has no predecessor identity sets"
    normalized_predecessors: set[tuple[tuple[str, str, str], ...]] = set()
    for index, predecessor in enumerate(predecessors):
        normalized = raw_producer_identity_set(predecessor)
        if normalized is None:
            return (
                "raw-producer compatibility grant has a malformed predecessor "
                f"identity set at index {index}"
            )
        if normalized in normalized_predecessors:
            return "raw-producer compatibility grant repeats a predecessor identity set"
        normalized_predecessors.add(normalized)
    successor = raw_producer_identity_set(
        value.get("successor_raw_producer_code_identities")
    )
    if successor is None:
        return "raw-producer compatibility grant has a malformed successor identity set"
    if successor in normalized_predecessors:
        return "raw-producer compatibility successor duplicates a predecessor"
    return ""
