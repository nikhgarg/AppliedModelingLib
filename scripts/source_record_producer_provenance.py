#!/usr/bin/env python3
"""Project source-record fingerprints away from forensic producer provenance.

Producer code identities record which implementation issued a raw receipt.
They are not paper semantics.  Active reuse consumers call this module to
remove only that complete, validated provenance bundle before comparing the
remaining source, map, Lean, review, and protocol coordinates.
"""

from __future__ import annotations

import copy
import re
from typing import Any, Mapping


RAW_PRODUCER_IDENTITY_SCHEMA = 1
RAW_PRODUCER_IDENTITY_FIELDS = frozenset({"path", "sha256", "status"})
RAW_PRODUCER_FINGERPRINT_FIELDS = frozenset(
    {"raw_producer_code_identity_schema", "raw_producer_code_identities"}
)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


def raw_producer_identity_set(
    value: object,
) -> tuple[tuple[str, str, str], ...] | None:
    """Normalize one complete producer-provenance identity set."""

    if not isinstance(value, list) or not value:
        return None
    records: list[tuple[str, str, str]] = []
    paths: set[str] = set()
    for raw_identity in value:
        if (
            not isinstance(raw_identity, Mapping)
            or set(raw_identity) != RAW_PRODUCER_IDENTITY_FIELDS
        ):
            return None
        path = raw_identity.get("path")
        sha256 = raw_identity.get("sha256")
        status = raw_identity.get("status")
        if (
            not isinstance(path, str)
            or not path.strip()
            or not isinstance(sha256, str)
            or not SHA256_RE.fullmatch(sha256.strip().lower())
            or status != "present"
        ):
            return None
        normalized_path = path.strip()
        if normalized_path in paths:
            return None
        paths.add(normalized_path)
        records.append((normalized_path, sha256.strip().lower(), "present"))
    return tuple(sorted(records))


def fingerprint_without_raw_producer_provenance(
    value: object,
) -> dict[str, Any] | None:
    """Project a schema-10 fingerprint onto non-producer audit inputs."""

    if not isinstance(value, Mapping) or value.get("schema") != 10:
        return None
    if value.get("raw_producer_code_identity_schema") != RAW_PRODUCER_IDENTITY_SCHEMA:
        return None
    if raw_producer_identity_set(value.get("raw_producer_code_identities")) is None:
        return None
    projection = copy.deepcopy(dict(value))
    for field in RAW_PRODUCER_FINGERPRINT_FIELDS:
        projection.pop(field, None)
    return projection
