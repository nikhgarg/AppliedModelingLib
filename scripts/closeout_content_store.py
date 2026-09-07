#!/usr/bin/env python3
"""Content-addressed storage for non-authoritative closeout payloads.

The closeout planner and worker pass several large immutable JSON objects.  A
receipt should bind those bytes, not copy them into every operational file.
This module provides one deliberately small storage contract: canonical JSON
bytes are addressed by SHA-256, written atomically, and re-read with both path
and digest validation.  Stored objects are scheduling inputs only; neither an
object nor a reference can grant paper-closeout acceptance.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import tempfile
from pathlib import Path
from typing import Any, Mapping


CONTENT_OBJECT_REFERENCE_SCHEMA = 1
CONTENT_OBJECT_STORE_RELATIVE = Path(".lake") / "closeout-objects" / "sha256"
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class CloseoutContentStoreError(ValueError):
    """A closeout object or reference is malformed, missing, or corrupt."""


def canonical_json_bytes(value: object) -> bytes:
    """Return the one byte representation accepted by the object store."""

    return (
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


def content_sha256(value: object) -> str:
    return hashlib.sha256(canonical_json_bytes(value)).hexdigest()


def _object_relative_path(digest: str) -> Path:
    if not SHA256_RE.fullmatch(digest):
        raise CloseoutContentStoreError("closeout object digest is not SHA-256")
    return CONTENT_OBJECT_STORE_RELATIVE / digest[:2] / f"{digest}.json"


def _safe_object_path(root: Path, relative: object) -> Path:
    text = str(relative or "").strip()
    candidate = Path(text)
    if not text or candidate.is_absolute() or ".." in candidate.parts:
        raise CloseoutContentStoreError("closeout object path is not repository-relative")
    root = root.resolve()
    path = (root / candidate).resolve()
    try:
        path.relative_to(root)
    except ValueError as exc:
        raise CloseoutContentStoreError("closeout object path escapes the repository") from exc
    return path


def _atomic_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, raw_temp = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temp = Path(raw_temp)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temp, path)
    finally:
        try:
            temp.unlink()
        except FileNotFoundError:
            pass


def store_closeout_object(root: Path, value: object, *, kind: str) -> dict[str, Any]:
    """Store canonical JSON once and return a compact exact-byte reference."""

    kind = str(kind).strip()
    if not kind or not re.fullmatch(r"[a-z][a-z0-9_]*", kind):
        raise CloseoutContentStoreError("closeout object kind is invalid")
    payload = canonical_json_bytes(value)
    digest = hashlib.sha256(payload).hexdigest()
    relative = _object_relative_path(digest)
    path = _safe_object_path(root, relative)
    try:
        existing = path.read_bytes()
    except FileNotFoundError:
        _atomic_write(path, payload)
    except OSError as exc:
        raise CloseoutContentStoreError(f"could not read closeout object: {exc}") from exc
    else:
        if existing != payload:
            raise CloseoutContentStoreError(
                "content-addressed closeout object path contains different bytes"
            )
    return {
        "schema": CONTENT_OBJECT_REFERENCE_SCHEMA,
        "acceptance_credential": False,
        "operational_scheduling_only": True,
        "kind": kind,
        "sha256": digest,
        "byte_length": len(payload),
        "path": relative.as_posix(),
    }


def load_closeout_object(
    root: Path,
    reference: object,
    *,
    expected_kind: str,
) -> object:
    """Load and authenticate an exact stored object, failing closed on drift."""

    if not isinstance(reference, Mapping):
        raise CloseoutContentStoreError("closeout object reference is not an object")
    required = {
        "schema",
        "acceptance_credential",
        "operational_scheduling_only",
        "kind",
        "sha256",
        "byte_length",
        "path",
    }
    if set(reference) != required:
        raise CloseoutContentStoreError("closeout object reference fields are malformed")
    digest = str(reference.get("sha256") or "")
    if (
        reference.get("schema") != CONTENT_OBJECT_REFERENCE_SCHEMA
        or reference.get("acceptance_credential") is not False
        or reference.get("operational_scheduling_only") is not True
        or reference.get("kind") != expected_kind
        or not SHA256_RE.fullmatch(digest)
        or not isinstance(reference.get("byte_length"), int)
        or isinstance(reference.get("byte_length"), bool)
        or int(reference["byte_length"]) < 0
        or str(reference.get("path") or "") != _object_relative_path(digest).as_posix()
    ):
        raise CloseoutContentStoreError("closeout object reference is invalid")
    path = _safe_object_path(root, reference["path"])
    try:
        payload = path.read_bytes()
    except OSError as exc:
        raise CloseoutContentStoreError(f"closeout object is unavailable: {exc}") from exc
    if (
        len(payload) != reference["byte_length"]
        or hashlib.sha256(payload).hexdigest() != digest
    ):
        raise CloseoutContentStoreError("closeout object bytes do not match their reference")
    try:
        value = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CloseoutContentStoreError("closeout object is not canonical JSON") from exc
    if canonical_json_bytes(value) != payload:
        raise CloseoutContentStoreError("closeout object is not canonically encoded")
    return value


def is_closeout_object_reference(value: object, *, kind: str = "") -> bool:
    """Recognize a reference shape without reading storage."""

    return isinstance(value, Mapping) and (
        value.get("schema") == CONTENT_OBJECT_REFERENCE_SCHEMA
        and value.get("acceptance_credential") is False
        and value.get("operational_scheduling_only") is True
        and (not kind or value.get("kind") == kind)
        and SHA256_RE.fullmatch(str(value.get("sha256") or "")) is not None
    )
