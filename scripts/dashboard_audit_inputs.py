#!/usr/bin/env python3
"""Immutable exact-input transaction boundary for dashboard audit consumers."""

from __future__ import annotations

import json
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field as dataclass_field
from pathlib import Path
from threading import Lock
from types import MappingProxyType
from typing import Any, Iterator, Mapping


class DashboardFrozenInputError(RuntimeError):
    """A strict dashboard read was not present in its immutable input bundle."""


def _immutable_json_mutation(*_args: object, **_kwargs: object) -> None:
    raise TypeError("frozen dashboard JSON cannot be mutated")


class _FrozenJsonDict(dict[str, Any]):
    """A ``dict``-compatible recursively immutable JSON object."""

    __setitem__ = _immutable_json_mutation
    __delitem__ = _immutable_json_mutation
    clear = _immutable_json_mutation
    pop = _immutable_json_mutation
    popitem = _immutable_json_mutation
    setdefault = _immutable_json_mutation
    update = _immutable_json_mutation
    __ior__ = _immutable_json_mutation


class _FrozenJsonList(list[Any]):
    """A ``list``-compatible recursively immutable JSON array."""

    __setitem__ = _immutable_json_mutation
    __delitem__ = _immutable_json_mutation
    append = _immutable_json_mutation
    clear = _immutable_json_mutation
    extend = _immutable_json_mutation
    insert = _immutable_json_mutation
    pop = _immutable_json_mutation
    remove = _immutable_json_mutation
    reverse = _immutable_json_mutation
    sort = _immutable_json_mutation
    __iadd__ = _immutable_json_mutation
    __imul__ = _immutable_json_mutation


def _freeze_dashboard_json(value: Any) -> Any:
    """Freeze parsed JSON while preserving ``dict``/``list`` compatibility."""

    if isinstance(value, dict):
        frozen = _FrozenJsonDict()
        for key, item in value.items():
            dict.__setitem__(frozen, key, _freeze_dashboard_json(item))
        return frozen
    if isinstance(value, list):
        frozen_list = _FrozenJsonList()
        list.extend(frozen_list, (_freeze_dashboard_json(item) for item in value))
        return frozen_list
    return value


@dataclass(frozen=True)
class DashboardAuditInputs:
    """Exact file bytes used by one strict dashboard extraction.

    ``file_snapshots`` is the complete authority for dashboard-facing file
    reads while this bundle is active. Values are immutable bytes; ``None``
    explicitly records that a path was absent when the transaction started.
    A path omitted from the mapping is not treated as absent: a direct read of
    it fails closed. This distinction prevents a closeout from silently mixing
    frozen status/sidecar inputs with later live repository contents.

    Paths may be absolute or relative to ``repository_root``. Each JSON object
    is parsed at most once and retained as a recursively immutable, ordinary
    ``dict``/``list``-compatible value shared by all dashboard lanes.
    """

    repository_root: Path
    file_snapshots: Mapping[str, bytes | None]
    _json_payload_cache: dict[str, dict[str, Any] | None] = dataclass_field(
        init=False,
        repr=False,
        compare=False,
    )
    _json_payload_lock: Lock = dataclass_field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        root = self.repository_root.resolve()
        normalized: dict[str, bytes | None] = {}
        for raw_path, raw_value in self.file_snapshots.items():
            path = Path(raw_path)
            if not path.is_absolute():
                path = root / path
            try:
                key = path.resolve().relative_to(root).as_posix()
            except (OSError, RuntimeError, ValueError) as exc:
                raise ValueError(
                    f"dashboard audit input is outside repository root: {raw_path}"
                ) from exc
            if key in normalized:
                raise ValueError(f"duplicate dashboard audit input path: {key}")
            if raw_value is not None and not isinstance(raw_value, bytes):
                raise TypeError(
                    "dashboard audit input values must be bytes or None; "
                    f"got {type(raw_value).__name__} for {key}"
                )
            normalized[key] = raw_value
        object.__setattr__(self, "repository_root", root)
        object.__setattr__(self, "file_snapshots", MappingProxyType(normalized))
        object.__setattr__(self, "_json_payload_cache", {})
        object.__setattr__(self, "_json_payload_lock", Lock())

    @classmethod
    def from_file_snapshots(
        cls,
        repository_root: Path,
        snapshots: Mapping[Path | str, bytes | str | None],
    ) -> DashboardAuditInputs:
        """Build an immutable bundle from caller-acquired exact snapshots."""

        encoded: dict[str, bytes | None] = {}
        for path, value in snapshots.items():
            encoded[str(path)] = value.encode("utf-8") if isinstance(value, str) else value
        return cls(repository_root=repository_root, file_snapshots=encoded)

    def _key(self, path: Path) -> str:
        try:
            return path.resolve().relative_to(self.repository_root).as_posix()
        except (OSError, RuntimeError, ValueError) as exc:
            raise DashboardFrozenInputError(
                f"dashboard attempted to read outside frozen repository: {path}"
            ) from exc

    def has_snapshot(self, path: Path) -> bool:
        """Whether the transaction explicitly recorded ``path``."""

        return self._key(path) in self.file_snapshots

    def is_file(self, path: Path) -> bool:
        """Return frozen file presence, rejecting an unrecorded path."""

        key = self._key(path)
        if key not in self.file_snapshots:
            raise DashboardFrozenInputError(
                f"missing frozen dashboard input: {key}"
            )
        return self.file_snapshots[key] is not None

    def read_bytes(self, path: Path) -> bytes:
        """Return exact frozen bytes, rejecting absent or unrecorded paths."""

        key = self._key(path)
        if key not in self.file_snapshots:
            raise DashboardFrozenInputError(
                f"missing frozen dashboard input: {key}"
            )
        value = self.file_snapshots[key]
        if value is None:
            raise DashboardFrozenInputError(
                f"frozen dashboard input was absent: {key}"
            )
        return value

    def read_text(self, path: Path) -> str:
        """Decode exact frozen bytes as UTF-8."""

        try:
            return self.read_bytes(path).decode("utf-8")
        except UnicodeDecodeError as exc:
            raise DashboardFrozenInputError(
                f"frozen dashboard input is not UTF-8: {self._key(path)}"
            ) from exc

    def json_payload(self, path: Path) -> dict[str, Any] | None:
        """Return one cached immutable JSON object; absence returns ``None``."""

        if not self.is_file(path):
            return None
        key = self._key(path)
        with self._json_payload_lock:
            if key in self._json_payload_cache:
                return self._json_payload_cache[key]
            try:
                payload = json.loads(self.read_bytes(path))
            except json.JSONDecodeError as exc:
                raise DashboardFrozenInputError(
                    f"invalid frozen dashboard JSON: {key}"
                ) from exc
            frozen = (
                _freeze_dashboard_json(payload)
                if isinstance(payload, dict)
                else None
            )
            self._json_payload_cache[key] = frozen
            return frozen

    def existing_files_under(
        self, folder: Path, *, suffix: str | None = None
    ) -> tuple[Path, ...]:
        """Return frozen-present files directly below ``folder``."""

        folder_key = self._key(folder).rstrip("/")
        prefix = f"{folder_key}/" if folder_key else ""
        paths: list[Path] = []
        for key, value in self.file_snapshots.items():
            if value is None or not key.startswith(prefix):
                continue
            relative = key[len(prefix) :]
            if not relative or "/" in relative:
                continue
            path = self.repository_root / key
            if suffix is None or path.suffix.lower() == suffix.lower():
                paths.append(path)
        return tuple(sorted(paths))

    def file_bytes_override(self) -> Mapping[Path, bytes | None]:
        """Return a read-only absolute-path view for exact-byte validators."""

        return MappingProxyType(
            {
                self.repository_root / relative_path: value
                for relative_path, value in self.file_snapshots.items()
            }
        )


_ACTIVE_DASHBOARD_AUDIT_INPUTS: ContextVar[DashboardAuditInputs | None] = ContextVar(
    "active_dashboard_audit_inputs", default=None
)


@contextmanager
def dashboard_audit_input_scope(
    audit_inputs: DashboardAuditInputs | None,
) -> Iterator[None]:
    """Activate exact dashboard inputs for nested legacy helper calls."""

    if audit_inputs is None:
        yield
        return
    token = _ACTIVE_DASHBOARD_AUDIT_INPUTS.set(audit_inputs)
    try:
        yield
    finally:
        _ACTIVE_DASHBOARD_AUDIT_INPUTS.reset(token)


def _dashboard_audit_inputs() -> DashboardAuditInputs | None:
    return _ACTIVE_DASHBOARD_AUDIT_INPUTS.get()


def _dashboard_is_file(path: Path) -> bool:
    inputs = _dashboard_audit_inputs()
    return inputs.is_file(path) if inputs is not None else path.is_file()


def _dashboard_read_bytes(path: Path) -> bytes:
    inputs = _dashboard_audit_inputs()
    return inputs.read_bytes(path) if inputs is not None else path.read_bytes()


def _dashboard_read_text(path: Path) -> str:
    inputs = _dashboard_audit_inputs()
    return inputs.read_text(path) if inputs is not None else path.read_text(encoding="utf-8")


def _dashboard_file_bytes_override() -> Mapping[Path, bytes | None] | None:
    """Return the active transaction's exact bytes for shared validators."""

    inputs = _dashboard_audit_inputs()
    return inputs.file_bytes_override() if inputs is not None else None


def _dashboard_json_payload(path: Path) -> dict[str, Any] | None:
    inputs = _dashboard_audit_inputs()
    if inputs is not None:
        return inputs.json_payload(path)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, dict) else None
