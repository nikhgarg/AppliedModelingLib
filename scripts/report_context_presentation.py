"""Validate reader-facing wording for settled source-review contexts.

Semantic context records remain the authority for source interpretation and
review reuse.  This module owns a separate, paper-local presentation layer so
editors can improve report, packet, and dashboard wording without changing a
source-review input or an accepted semantic identity.
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from types import MappingProxyType
from typing import Any


REPORT_CONTEXT_SUMMARIES_PATH = Path("docs/REPORT_CONTEXT_SUMMARIES.json")
REPORT_MEMO_COVERAGE_PATH = Path("docs/REPORT_MEMO_COVERAGE.json")
REPORT_CONTEXT_SUMMARIES_SCHEMA = 1
ROW_CONTEXT_PRESENTATION_SCHEMA = 2
LEGACY_ROW_CONTEXT_PRESENTATION_SCHEMA = 1


def _digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def _fallback_summary(context: Mapping[str, Any]) -> str:
    """Return the established report wording when no override is supplied."""

    summary = str(context.get("report_summary") or "").strip()
    if summary:
        return summary
    formal_meaning = str(context.get("formal_meaning") or "").strip()
    if not formal_meaning:
        return "A settled source reading is recorded in the typed source map."
    sentence = formal_meaning.split(". ", 1)[0].strip()
    return sentence + ("." if not sentence.endswith(".") else "")


@dataclass(frozen=True)
class ReportContextPresentation:
    """One validated display-only summary projection for a paper."""

    paper: str
    summaries_by_id: Mapping[str, str]
    presentation_sha256: str
    assumption_summaries_by_record: Mapping[str, str] = field(
        default_factory=lambda: MappingProxyType({})
    )
    omitted_convention_ids: frozenset[str] = field(default_factory=frozenset)


def _omission_coverage_reason(folder: Path, context_id: str) -> tuple[str, str]:
    """Return the reviewed non-material reason for one display omission.

    ``REPORT_CONTEXT_SUMMARIES`` controls only presentation.  It may omit a
    settled convention only when the independent report-coverage ledger has
    already classified that exact convention as non-material.  Material
    conventions therefore remain subject to the ordinary memo requirement.
    """

    path = folder / REPORT_MEMO_COVERAGE_PATH
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return "", (
            f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} omits `{context_id}` "
            "without a report-coverage assessment"
        )
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        return "", f"cannot read {REPORT_MEMO_COVERAGE_PATH.as_posix()}: {exc}"
    if not isinstance(payload, Mapping):
        return "", f"{REPORT_MEMO_COVERAGE_PATH.as_posix()} is not an object"
    items = payload.get("items")
    if not isinstance(items, Mapping):
        return "", f"{REPORT_MEMO_COVERAGE_PATH.as_posix()} has no items object"
    item = items.get(f"convention/{context_id}")
    if not isinstance(item, Mapping):
        return "", (
            f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} omits `{context_id}` "
            "without a report-coverage assessment"
        )
    if item.get("disposition") != "not_material":
        return "", (
            f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} may omit `{context_id}` "
            "only when its report-coverage assessment is not_material"
        )
    reason = item.get("reason")
    if not isinstance(reason, str) or not reason.strip():
        return "", (
            f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} omits `{context_id}` "
            "without the required non-material reason"
        )
    return reason.strip(), ""


def report_context_presentation(
    folder: Path,
    contexts: Sequence[Mapping[str, Any]],
) -> tuple[ReportContextPresentation | None, str]:
    """Load and validate display wording against the known convention IDs.

    The optional JSON file may override any subset of known model conventions.
    All other conventions retain their existing ``report_summary`` (or the
    historical concise fallback).  Unknown IDs fail closed so a typo cannot
    silently create an unused reader-facing clarification.
    """

    model_contexts: dict[str, Mapping[str, Any]] = {}
    identities: dict[str, str] = {}
    for index, context in enumerate(contexts):
        if not isinstance(context, Mapping):
            return None, f"approved review context {index} is not an object"
        if context.get("kind") != "source_model_convention":
            continue
        context_id = str(context.get("id") or "").strip()
        record_sha256 = str(context.get("record_sha256") or "").strip().lower()
        if not context_id:
            return None, f"approved review context {index} has no id"
        prior = identities.get(context_id)
        if prior is not None and prior != record_sha256:
            return None, (
                f"approved review context `{context_id}` has inconsistent "
                "records across source items"
            )
        identities[context_id] = record_sha256
        model_contexts[context_id] = context

    overrides: dict[str, str] = {}
    assumption_overrides: dict[str, str] = {}
    omitted_convention_ids: set[str] = set()
    assumption_records = {
        str(context.get("record_sha256") or "")
        for context in contexts
        if context.get("kind") == "maintainer_approved_additional_assumptions"
    }
    path = folder / REPORT_CONTEXT_SUMMARIES_PATH
    if path.exists():
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as exc:
            return None, f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} is unreadable: {exc}"
        if not isinstance(payload, Mapping):
            return None, f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} is not an object"
        expected_keys = {"schema", "paper", "summaries"}
        if set(payload) not in (
            expected_keys,
            expected_keys | {"assumption_summaries"},
            expected_keys | {"omitted_conventions"},
            expected_keys | {"assumption_summaries", "omitted_conventions"},
        ):
            return None, (
                f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} must contain exactly "
                "schema, paper, and summaries, with optional assumption_summaries "
                "and omitted_conventions"
            )
        if (
            isinstance(payload.get("schema"), bool)
            or payload.get("schema") != REPORT_CONTEXT_SUMMARIES_SCHEMA
        ):
            return None, f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} has an unknown schema"
        if str(payload.get("paper") or "").strip() != folder.name:
            return None, f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} names another paper"
        raw_summaries = payload.get("summaries")
        raw_assumptions = payload.get("assumption_summaries", {})
        raw_omissions = payload.get("omitted_conventions", [])
        if not isinstance(raw_assumptions, Mapping):
            return None, "assumption_summaries must be an object"
        if not isinstance(raw_omissions, list):
            return None, "omitted_conventions must be a list"
        if not isinstance(raw_summaries, Mapping) or (
            not raw_summaries and not raw_assumptions and not raw_omissions
        ):
            return None, (
                f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} summaries must be a "
                "nonempty object unless assumption_summaries or "
                "omitted_conventions supplies display content"
            )
        for raw_id, raw_summary in raw_summaries.items():
            if not isinstance(raw_id, str) or not raw_id.strip():
                return None, (
                    f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} has an invalid "
                    "convention id"
                )
            context_id = raw_id.strip()
            if raw_id != context_id:
                return None, (
                    f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} convention ids "
                    "must not contain surrounding whitespace"
                )
            if context_id not in model_contexts:
                return None, (
                    f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} cites unknown "
                    f"model convention `{context_id}`"
                )
            if not isinstance(raw_summary, str) or not raw_summary.strip():
                return None, (
                    f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} summary for "
                    f"`{context_id}` must be a nonempty string"
                )
            overrides[context_id] = raw_summary.strip()
        for raw_id in raw_omissions:
            if not isinstance(raw_id, str) or not raw_id.strip():
                return None, "omitted_conventions contains an invalid convention id"
            context_id = raw_id.strip()
            if raw_id != context_id:
                return None, "omitted_conventions ids must not contain surrounding whitespace"
            if context_id not in model_contexts:
                return None, (
                    f"omitted_conventions cites unknown model convention `{context_id}`"
                )
            if context_id in omitted_convention_ids:
                return None, f"omitted_conventions repeats `{context_id}`"
            if context_id in overrides:
                return None, (
                    f"{REPORT_CONTEXT_SUMMARIES_PATH.as_posix()} both summarizes "
                    f"and omits `{context_id}`"
                )
            _reason, omission_error = _omission_coverage_reason(folder, context_id)
            if omission_error:
                return None, omission_error
            omitted_convention_ids.add(context_id)
        for record, summary in raw_assumptions.items():
            if record not in assumption_records:
                return None, f"unknown additional-assumption record `{record}`"
            if not isinstance(summary, str) or not summary.strip():
                return None, f"assumption summary for `{record}` must be nonempty"
            assumption_overrides[record] = summary.strip()

    summaries = {
        context_id: overrides.get(context_id, _fallback_summary(context))
        for context_id, context in sorted(model_contexts.items())
        if context_id not in omitted_convention_ids
    }
    identity_payload = {
        "schema": REPORT_CONTEXT_SUMMARIES_SCHEMA,
        "paper": folder.name,
        "summaries": summaries,
    }
    if assumption_overrides:
        identity_payload["assumption_summaries"] = dict(
            sorted(assumption_overrides.items())
        )
    if omitted_convention_ids:
        identity_payload["omitted_conventions"] = sorted(omitted_convention_ids)
    return (
        ReportContextPresentation(
            paper=folder.name,
            summaries_by_id=MappingProxyType(summaries),
            presentation_sha256=_digest(identity_payload),
            assumption_summaries_by_record=MappingProxyType(assumption_overrides),
            omitted_convention_ids=frozenset(omitted_convention_ids),
        ),
        "",
    )


def row_context_presentation(
    contexts: object,
    presentation: ReportContextPresentation,
) -> dict[str, Any]:
    """Project only the display summaries used by one review card."""

    raw_contexts = contexts if isinstance(contexts, list) else []
    summaries: dict[str, str] = {}
    omitted_convention_ids: set[str] = set()
    for context in raw_contexts:
        if not isinstance(context, Mapping):
            continue
        if context.get("kind") != "source_model_convention":
            continue
        context_id = str(context.get("id") or "").strip()
        if context_id in presentation.omitted_convention_ids:
            omitted_convention_ids.add(context_id)
            continue
        summary = presentation.summaries_by_id.get(context_id)
        if context_id and summary:
            summaries[context_id] = summary
    payload = {
        "schema": ROW_CONTEXT_PRESENTATION_SCHEMA,
        "summaries_by_id": summaries,
        "omitted_convention_ids": sorted(omitted_convention_ids),
    }
    return {**payload, "presentation_sha256": _digest(payload)}


def validated_row_context_presentation(
    contexts: object,
    raw_presentation: object,
) -> tuple[Mapping[str, str], frozenset[str], str, str]:
    """Validate a derived review-card projection for a pure renderer."""

    raw_contexts = contexts if isinstance(contexts, list) else []
    known_ids = {
        str(context.get("id") or "").strip()
        for context in raw_contexts
        if isinstance(context, Mapping)
        and context.get("kind") == "source_model_convention"
        and str(context.get("id") or "").strip()
    }
    if raw_presentation is None:
        # Historical renderer fixtures and old public payloads retain their
        # established semantic-record summary until regenerated.
        summaries = {
            str(context.get("id") or "").strip(): _fallback_summary(context)
            for context in raw_contexts
            if isinstance(context, Mapping)
            and context.get("kind") == "source_model_convention"
            and str(context.get("id") or "").strip()
        }
        payload = {
            "schema": LEGACY_ROW_CONTEXT_PRESENTATION_SCHEMA,
            "summaries_by_id": summaries,
        }
        return MappingProxyType(summaries), frozenset(), _digest(payload), ""
    if not isinstance(raw_presentation, Mapping):
        return MappingProxyType({}), frozenset(), "", "review-context presentation is not an object"
    schema = raw_presentation.get("schema")
    if isinstance(schema, bool) or schema not in {
        LEGACY_ROW_CONTEXT_PRESENTATION_SCHEMA,
        ROW_CONTEXT_PRESENTATION_SCHEMA,
    }:
        return MappingProxyType({}), frozenset(), "", "review-context presentation has an unknown schema"
    expected_fields = (
        {"schema", "summaries_by_id", "presentation_sha256"}
        if schema == LEGACY_ROW_CONTEXT_PRESENTATION_SCHEMA
        else {
            "schema",
            "summaries_by_id",
            "omitted_convention_ids",
            "presentation_sha256",
        }
    )
    if set(raw_presentation) != expected_fields:
        return MappingProxyType({}), frozenset(), "", "review-context presentation fields are malformed"
    raw_summaries = raw_presentation.get("summaries_by_id")
    if not isinstance(raw_summaries, Mapping):
        return MappingProxyType({}), frozenset(), "", "review-context summaries are not an object"
    summaries: dict[str, str] = {}
    for raw_id, raw_summary in raw_summaries.items():
        if (
            not isinstance(raw_id, str)
            or raw_id not in known_ids
            or not isinstance(raw_summary, str)
            or not raw_summary.strip()
        ):
            return MappingProxyType({}), frozenset(), "", "review-context summaries are malformed"
        summaries[raw_id] = raw_summary.strip()
    omitted_convention_ids: frozenset[str] = frozenset()
    if schema == ROW_CONTEXT_PRESENTATION_SCHEMA:
        raw_omissions = raw_presentation.get("omitted_convention_ids")
        if (
            not isinstance(raw_omissions, list)
            or any(
                not isinstance(raw_id, str)
                or raw_id not in known_ids
                for raw_id in raw_omissions
            )
            or raw_omissions != sorted(raw_omissions)
            or len(set(raw_omissions)) != len(raw_omissions)
        ):
            return MappingProxyType({}), frozenset(), "", "review-context omissions are malformed"
        omitted_convention_ids = frozenset(raw_omissions)
    if set(summaries) != known_ids - omitted_convention_ids:
        return MappingProxyType({}), frozenset(), "", "review-context summaries do not cover the displayed row exactly"
    payload = {
        "schema": schema,
        "summaries_by_id": summaries,
    }
    if schema == ROW_CONTEXT_PRESENTATION_SCHEMA:
        payload["omitted_convention_ids"] = sorted(omitted_convention_ids)
    actual = _digest(payload)
    recorded = str(raw_presentation.get("presentation_sha256") or "").strip().lower()
    if recorded != actual:
        return MappingProxyType({}), frozenset(), "", "review-context presentation digest is stale"
    return MappingProxyType(summaries), omitted_convention_ids, actual, ""


def context_presentation_summary(
    context: Mapping[str, Any], summaries_by_id: Mapping[str, str]
) -> str:
    """Return the display text for one already validated row context."""

    if context.get("kind") == "source_model_convention":
        context_id = str(context.get("id") or "").strip()
        return summaries_by_id.get(context_id) or _fallback_summary(context)
    conditions = context.get("conditions")
    if isinstance(conditions, list):
        return "; ".join(str(value).strip() for value in conditions if str(value).strip())
    return ""


__all__ = [
    "REPORT_CONTEXT_SUMMARIES_PATH",
    "ReportContextPresentation",
    "context_presentation_summary",
    "report_context_presentation",
    "row_context_presentation",
    "validated_row_context_presentation",
]
