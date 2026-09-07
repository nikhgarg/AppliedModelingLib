#!/usr/bin/env python3
"""Lightweight controlled-status checks for human-facing final reports.

The closeout planner uses these lightweight checks before expensive evidence
or Lean work. Public reports and the website share the same display policy;
the underlying mathematical status and evidence are unchanged.
"""

from __future__ import annotations

import json
import os
import re
from collections.abc import Mapping
from pathlib import Path


CONTROLLED_PAPER_STATUSES = frozenset(
    {
        "formalized",
        "formalized with caveat",
        "conditional",
        "partially formalized",
        "not formalized",
        "paper draft",
        "not started",
    }
)
FINAL_REPORT_STATUS_LINE_RE = re.compile(
    r"^\s*(?:[-*+]\s*)?(?:Completion status|Lean formalization status)\s*:\s*"
    r"(?P<status>.+?)\s*$"
)
FINAL_REPORT_CLOSEOUT_STATUS_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?Closeout\s+Status\b"
)
_STATUS_LABELS = (
    "partially formalized",
    "formalized with caveat",
    "not formalized",
    "paper draft",
    "not started",
    "formalized",
    "conditional",
    "complete",
    "completed",
)


def normalized_paper_status(value: object) -> str:
    """Return one status spelling suitable for exact controlled comparisons."""

    return value.strip().lower() if isinstance(value, str) else ""


def public_display_status(
    status: str, *, paper_id: str | None = None, preserve_partial_status: object = ()
) -> str:
    """Return the public reader label without changing technical disposition."""

    if not isinstance(preserve_partial_status, (list, tuple)) or any(
        not isinstance(value, str) or not value.strip()
        for value in preserve_partial_status
    ):
        raise ValueError("preserve_partial_status must list paper IDs")
    if paper_id in preserve_partial_status and status in {
        "partially formalized", "conditional"
    }:
        return "partially formalized"
    if status in {
        "formalized", "formalized with caveat", "partially formalized", "conditional"
    }:
        return "formalized"
    return status


def _report_expected_status(status: object) -> str:
    if not isinstance(status, Mapping):
        return normalized_paper_status(status)
    technical_status = normalized_paper_status(status.get("status"))
    if status.get("repository_visibility") != "public":
        return technical_status
    root = Path(os.environ.get(
        "APPLIEDMODELINGLIB_REPO_ROOT", Path(__file__).resolve().parents[1]
    ))
    catalog = json.loads((root / "papers" / "catalog.json").read_text(encoding="utf-8"))
    if not isinstance(catalog, dict) or catalog.get("schema") != 1:
        raise ValueError("papers/catalog.json must be a schema-1 object")
    return public_display_status(
        technical_status,
        paper_id=status.get("id"),
        preserve_partial_status=catalog.get("preserve_partial_status", []),
    )


def final_report_declared_statuses(report_text: str) -> set[str]:
    """Extract controlled whole-paper statuses from the Closeout Status section.

    Historical discussion and fenced examples do not count. The parser accepts
    ordinary Markdown emphasis around a controlled status and a trailing
    explanatory clause, but never derives status from theorem text.
    """

    statuses: set[str] = set()
    heading_level: int | None = None
    in_fence = False
    for raw_line in report_text.splitlines():
        stripped = raw_line.lstrip()
        if stripped.startswith(("```", "~~~")):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        if heading_level is None:
            heading = FINAL_REPORT_CLOSEOUT_STATUS_RE.match(raw_line)
            if heading is None:
                continue
            marker = re.match(r"^(#+)", raw_line)
            if marker is None:
                continue
            heading_level = len(marker.group(1))
            continue
        next_heading = re.match(r"^(#+)\s+", raw_line)
        if next_heading is not None and len(next_heading.group(1)) <= heading_level:
            break
        line = re.sub(r"[`*_]", "", raw_line)
        match = FINAL_REPORT_STATUS_LINE_RE.match(line)
        if match is None:
            continue
        value = match.group("status").strip().lower()
        for label in _STATUS_LABELS:
            if re.match(rf"{re.escape(label)}(?=$|[\s.;,:/])", value):
                statuses.add("formalized" if label in {"complete", "completed"} else label)
                break
    return statuses


def report_status_alignment_errors(status: object, report_text: str) -> tuple[str, ...]:
    """Check the reader label from a status payload, or a legacy status string.

    Public payloads use the canonical catalog's display exceptions. Private
    payloads and string-only callers retain exact technical-status comparison.
    """

    try:
        normalized_status = _report_expected_status(status)
    except (OSError, ValueError) as exc:
        return (f"final validation report display policy is unreadable: {exc}",)
    declared = final_report_declared_statuses(report_text)
    errors: list[str] = []
    if len(declared) > 1:
        errors.append(
            "final validation report has mutually exclusive whole-paper status "
            "declarations in its Closeout Status section: "
            + ", ".join(sorted(declared))
        )
    if normalized_status not in CONTROLLED_PAPER_STATUSES:
        return tuple(errors)
    if not declared:
        errors.append(
            "final validation report has no parseable controlled whole-paper status "
            "in its Closeout Status section; its expected reader label is "
            f"(`{normalized_status}`)"
        )
    elif declared != {normalized_status}:
        errors.append(
            "final validation report declares `"
            + ", ".join(sorted(declared))
            + "` in its Closeout Status section, but the reader label derived "
            + f"from paper-local status.json is `{normalized_status}`"
        )
    return tuple(errors)
