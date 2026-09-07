#!/usr/bin/env python3
"""Canonical, machine-independent identities for durable audit evidence.

Runtime locators and mutation accelerators are useful while a closeout command
is running, but they are not mathematical or source evidence. This module is
the single boundary where those operational details are projected away before
durable identities are computed. Callers must select an explicit typed
projection; silently hashing arbitrary dictionaries is deliberately not an
API.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any, Mapping


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class PortableEvidenceIdentityError(ValueError):
    """A proposed durable identity contains machine-local material."""


def canonical_json_bytes(value: object) -> bytes:
    """Return the canonical JSON encoding used by durable evidence hashes."""

    try:
        encoded = json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        )
    except (TypeError, ValueError) as exc:
        raise PortableEvidenceIdentityError(
            "durable evidence is not canonical JSON"
        ) from exc
    return encoded.encode("utf-8")


def portable_evidence_sha256(value: object) -> str:
    """Hash one already-typed, portable evidence projection."""

    _reject_runtime_objects(value)
    return hashlib.sha256(canonical_json_bytes(value)).hexdigest()


def _reject_runtime_objects(value: object, *, location: str = "$") -> None:
    """Fail closed on Python/path objects that cannot be durable evidence.

    Typed projectors below remove known runtime fields. This final recursive
    check prevents a caller from accidentally relying on ``default=str`` and
    thereby serializing a machine-specific ``Path`` or another opaque object.
    Repository-relative path strings remain valid when a typed schema says the
    spelling is part of the source or build obligation.
    """

    if isinstance(value, Path):
        raise PortableEvidenceIdentityError(
            f"durable evidence contains a Path object at {location}"
        )
    if value is None or isinstance(value, (str, int, float, bool)):
        return
    if isinstance(value, Mapping):
        for key, item in value.items():
            if not isinstance(key, str):
                raise PortableEvidenceIdentityError(
                    f"durable evidence has a non-string key at {location}"
                )
            _reject_runtime_objects(item, location=f"{location}.{key}")
        return
    if isinstance(value, (list, tuple)):
        for index, item in enumerate(value):
            _reject_runtime_objects(item, location=f"{location}[{index}]")
        return
    raise PortableEvidenceIdentityError(
        f"durable evidence contains {type(value).__name__} at {location}"
    )


def portable_semantic_hash_tool_identity(value: object) -> dict[str, str]:
    """Project an authenticated SHA-256 implementation without its location.

    Historical carriers may contain ``resolved_path``. The executable bytes,
    version output, and known-vector behavior authenticate the tool; its
    installation path does not. Invalid or incomplete inputs fail closed by
    returning an empty projection, matching the manifest validators' existing
    convention.
    """

    if not isinstance(value, Mapping):
        return {}
    required = (
        "command",
        "executable_sha256",
        "version_stdout_sha256",
        "version_banner",
        "known_vector",
        "known_vector_sha256",
    )
    projected = {field: str(value.get(field) or "").strip() for field in required}
    if (
        projected["command"] != "sha256sum"
        or projected["known_vector"] != "sha256(abc)"
        or any(not projected[field] for field in required)
        or any(
            not SHA256_RE.fullmatch(projected[field])
            for field in (
                "executable_sha256",
                "version_stdout_sha256",
                "known_vector_sha256",
            )
        )
    ):
        return {}
    return {"schema": "2", **projected}


def portable_lean_closure_identity(value: object) -> dict[str, Any]:
    """Project a Lean closeout closure onto path-independent content facts.

    The Lean-authored closure already pins repository sources by relative path
    and bytes and external modules by their aggregate artifact digest. Search
    roots, selected absolute candidates, symlink targets, and stat tuples are
    only local mutation accelerators and are intentionally excluded.
    """

    if value == {"state": "not_bound"}:
        return {"schema": 1, "state": "not_bound"}
    if not isinstance(value, Mapping):
        raise PortableEvidenceIdentityError(
            "Lean closure identity requires an operational projection"
        )
    closure = value.get("lean_import_closure")
    if value.get("state") != "present" or not isinstance(closure, Mapping):
        raise PortableEvidenceIdentityError(
            "Lean closure operational projection is malformed"
        )
    projection = {
        "schema": 1,
        "state": "present",
        "lean_import_closure": dict(closure),
    }
    _reject_runtime_objects(projection)
    return projection
