#!/usr/bin/env python3
"""Lazy import boundary for historical raw source-record authorities."""

from __future__ import annotations

from typing import Any, Callable


def legacy_source_record_authorities() -> Any:
    """Load the historical authority bundle only when its protocol executes."""

    from scripts import legacy_source_record_authorities as authorities

    return authorities


def deferred_legacy_source_record_callable(name: str) -> Callable[..., Any]:
    """Return a stable callable facade whose first invocation loads legacy code."""

    def invoke(*args: Any, **kwargs: Any) -> Any:
        return getattr(legacy_source_record_authorities(), name)(*args, **kwargs)

    invoke.__name__ = name
    invoke.__qualname__ = name
    return invoke


__all__ = (
    "deferred_legacy_source_record_callable",
    "legacy_source_record_authorities",
)
