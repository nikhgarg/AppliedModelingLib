#!/usr/bin/env python3
"""Fail closed on Lean diagnostics that a process exit code can miss."""

from __future__ import annotations

import re

from scripts.formalization_protocol import EXPECTED_CLEAN_LEAN_OUTPUT_BYTES


MAX_CLEAN_LEAN_OUTPUT_BYTES = EXPECTED_CLEAN_LEAN_OUTPUT_BYTES

_FATAL_DIAGNOSTIC_PATTERNS: tuple[tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"(?mi)^\s*PANIC(?:\s+at|\b)"), "Lean PANIC output"),
    (re.compile(r"(?i)\binternal error\b"), "Lean internal-error output"),
    (re.compile(r"(?mi)^\s*backtrace:\s*$"), "Lean crash backtrace output"),
)

_EXCERPT_FOCUS_PATTERNS: tuple[re.Pattern[str], ...] = (
    re.compile(r"(?mi)^\s*(?:PANIC(?:\s+at|\b)|internal error\b|backtrace:)"),
    re.compile(r"(?mi)^.*\.lean:\d+:\d+:\s*error:"),
    re.compile(r"(?m)^\s*✖"),
    re.compile(r"(?mi)^\s*error:(?!\s*build failed\b)"),
    re.compile(r"(?mi)^\s*error:"),
)


def lean_diagnostic_failure_reason(
    stdout: str | None,
    stderr: str | None,
    *,
    max_output_bytes: int = MAX_CLEAN_LEAN_OUTPUT_BYTES,
) -> str:
    """Return why captured Lean output is not a clean successful diagnostic.

    Lean and tactics can occasionally emit a panic/backtrace while the outer
    process still exits zero.  Acceptance callers must inspect the complete
    captured stream before issuing build or elaboration evidence.
    """

    if max_output_bytes <= 0:
        raise ValueError("max_output_bytes must be positive")
    output = "\n".join(part for part in (stdout or "", stderr or "") if part)
    for pattern, reason in _FATAL_DIAGNOSTIC_PATTERNS:
        if pattern.search(output):
            return reason
    size = len(output.encode("utf-8", errors="replace"))
    if size > max_output_bytes:
        return (
            "pathologically large Lean diagnostic output "
            f"({size} bytes; clean-output limit {max_output_bytes})"
        )
    return ""


def bounded_lean_diagnostic_excerpt(
    stdout: str | None,
    stderr: str | None,
    *,
    max_lines: int = 8,
    max_chars: int = 1200,
) -> str:
    """Return a bounded operator-facing excerpt without replaying huge logs."""

    output = "\n".join(part for part in (stderr or "", stdout or "") if part)
    for pattern in _EXCERPT_FOCUS_PATTERNS:
        focus = pattern.search(output)
        if focus is not None:
            output = output[focus.start() :]
            break
    lines = output.splitlines()
    return " ".join(lines[:max_lines])[:max_chars]
