"""Keep generated semantic-review context out of final validation reports.

The report links each material source reading to its paper-local clarification
memo.  Review-context records remain audit evidence and packet material; they
must not be copied into a generated report block beside the human explanation.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping
from pathlib import Path
from typing import Any

try:
    from source_review_input import validated_approved_review_contexts
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.source_review_input import validated_approved_review_contexts

from scripts.report_context_presentation import (
    ReportContextPresentation,
    context_presentation_summary,
    report_context_presentation,
)


BEGIN = "<!-- BEGIN GENERATED SETTLED REVIEW CONTEXT -->"
END = "<!-- END GENERATED SETTLED REVIEW CONTEXT -->"
SECTION_HEADING_RE = re.compile(
    r"(?m)^## 10\. Source Clarifications and Exact Readings\s*$"
)
NEXT_SECTION_RE = re.compile(r"(?m)^## 11\.")


def _load_object(path: Path) -> Mapping[str, Any] | None:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, Mapping) else None


def approved_review_contexts_for_report(
    folder: Path,
) -> tuple[list[dict[str, Any]], str]:
    source_map_path = folder / "audit" / "paper_statement_map.json"
    if not source_map_path.is_file():
        # Intake/report-template fixtures can legitimately precede a source
        # map. Completed-paper closeout has a separate hard requirement for
        # that map, so absence here must not invent context or block scaffolds.
        return [], ""
    source_map = _load_object(source_map_path)
    if source_map is None:
        return [], "paper statement map is unavailable"
    schema = source_map.get("approved_review_context_schema")
    if schema is None:
        return [], ""
    if schema != 1:
        return [], "paper statement map has an unknown approved-review-context schema"
    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        return [], "paper statement map has no items object"
    unique: dict[tuple[str, str, str], dict[str, Any]] = {}
    identity_by_name: dict[tuple[str, str], str] = {}
    for source_item, raw in raw_items.items():
        if not isinstance(raw, Mapping):
            return [], f"source item `{source_item}` is not an object"
        contexts, error = validated_approved_review_contexts(raw)
        if error:
            return [], f"source item `{source_item}`: {error}"
        for context in contexts:
            kind = str(context.get("kind") or "").strip()
            context_id = str(context.get("id") or "").strip()
            digest = str(context.get("record_sha256") or "").strip().lower()
            name = (kind, context_id)
            # A model-convention id is a repository-wide stable reference and
            # therefore must name exactly one record.  Additional assumptions
            # are deliberately source-item scoped: several result/model rows
            # may carry distinct maintainer-approved additions under the same
            # generic kind.  Their record digest is the identity in the report
            # projection, so preserve each rather than falsely treating them
            # as inconsistent global conventions.
            prior = identity_by_name.get(name)
            if (
                kind == "source_model_convention"
                and prior is not None
                and prior != digest
            ):
                return [], (
                    f"approved review context `{context_id}` has inconsistent "
                    "records across source items"
                )
            if kind == "source_model_convention":
                identity_by_name[name] = digest
            unique[(kind, context_id, digest)] = context
    return [unique[key] for key in sorted(unique)], ""


def _block_identity(contexts: list[dict[str, Any]]) -> str:
    projection = [
        {
            "kind": context["kind"],
            "id": context["id"],
            "record_sha256": context["record_sha256"],
        }
        for context in contexts
    ]
    return hashlib.sha256(
        json.dumps(
            projection,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def render_approved_review_context_block(
    contexts: list[dict[str, Any]],
    *,
    presentation: ReportContextPresentation,
) -> str:
    displayed_lines: list[str] = []
    displayed: set[str] = set()
    for context in contexts:
        if context.get("kind") == "source_model_convention":
            context_id = str(context.get("id") or "").strip()
            if context_id in presentation.omitted_convention_ids:
                continue
            # A historical model-convention record can describe an added
            # condition or an unproved connection. Its storage kind is not a
            # reader-facing mathematical classification.
            line = (
                "- "
                + context_presentation_summary(
                    context, presentation.summaries_by_id
                )
            )
        else:
            conditions = "; ".join(
                str(value).strip() for value in context.get("conditions", [])
            )
            summary = presentation.assumption_summaries_by_record.get(
                str(context.get("record_sha256") or ""), conditions + "."
            )
            line = "- **Additional assumptions.** " + summary
        # Several independently bound records can concern the same issue. An
        # identical display summary is one explanation; the block identity
        # above still binds every underlying record, including grouped ones.
        if line not in displayed:
            displayed_lines.append(line)
            displayed.add(line)
    if not displayed_lines:
        return ""
    lines = [
        BEGIN,
        f"<!-- settled-review-context-sha256: {_block_identity(contexts)} -->",
        (
            "<!-- settled-review-context-presentation-sha256: "
            f"{presentation.presentation_sha256} -->"
        ),
        "### Source readings and additional assumptions",
        "",
        *displayed_lines,
    ]
    lines.append(END)
    return "\n".join(lines)


def replace_approved_review_context_block(
    text: str, *, contexts: list[dict[str, Any]], path: Path
) -> str:
    """Remove the retired generated context block, preserving report prose.

    ``contexts`` stays in this stable interface because packet and historical
    callers share it, but the reader-facing report has one substantive home for
    a clarification: its linked memo.
    """

    del contexts
    if BEGIN in text or END in text:
        if text.count(BEGIN) != 1 or text.count(END) != 1:
            raise ValueError(f"{path} has malformed settled-review-context markers")
        before, rest = text.split(BEGIN, 1)
        _old, after = rest.split(END, 1)
        return before.rstrip() + "\n\n" + after.lstrip()
    return text


def current_approved_review_context_report_errors(folder: Path) -> tuple[str, ...]:
    report = folder / "FINAL_VALIDATION_REPORT.md"
    try:
        text = report.read_text(encoding="utf-8")
    except OSError as exc:
        return (f"final validation report is unavailable: {exc}",)
    if BEGIN in text or END in text:
        return (
            (
                "final validation report contains a generated settled-review-context "
                "block; keep the explanation in its linked clarification memo"
            ),
        )
    return ()
