#!/usr/bin/env python3
"""Content-pinned source regions and one appendix-aware review-scope selector.

The source inventory, rather than section titles, Lean names, or proof imports,
owns main-text/appendix classification.  This module materializes and validates
one complete line partition of the canonical text source, assigns every source
inventory entry to a region, and exposes the projections used by terminal
review.  It grants no source-to-Lean judgment and never parses Lean source.
"""

from __future__ import annotations

import hashlib
import re
from collections.abc import Iterable, Mapping
from pathlib import Path, PurePosixPath
from typing import Any

from scripts.formalization_protocol import (
    CLOSEOUT_REVIEW_POLICY_FIELD,
    CLOSEOUT_REPEAT_SCOPE_ALL_SELECTED,
    CLOSEOUT_REPEAT_SCOPE_MAIN_PRIMARY,
    CLOSEOUT_SOURCE_SCOPE_ALL_PROSE,
    CLOSEOUT_SOURCE_SCOPE_MAIN_NAMED_THEORY,
    FormalizationProtocolError,
    ResolvedCloseoutReviewPolicy,
    explicit_closeout_review_policy_from_source_map,
)
from scripts.source_coverage_scope import (
    DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
    USER_APPROVED_SCOPE_EXCLUSION_KEY,
    current_canonical_text_source,
    source_coverage_mode_from_map,
    source_item_is_named_theoretical_statement,
    source_named_result_environment_kinds_from_map,
    source_prose_definition_presentation_sha256,
)
from scripts.source_review_input import (
    SourceReviewInputError,
    canonical_source_anchor_evidence,
)


SOURCE_REGION_PARTITION_FIELD = "source_region_partition"
SOURCE_REGION_PARTITION_SCHEMA = 1
SOURCE_REGION_KINDS = frozenset({"main_text", "appendix", "supplement"})
SOURCE_PRIMARY_REGION_KIND = "main_text"
SOURCE_ITEM_REGIONS_FIELD = "source_item_regions"
CANDIDATE_PRESENTATION_REGIONS_FIELD = "candidate_presentation_regions"
PROSE_DEFINITION_PRESENTATION_REGIONS_FIELD = (
    "prose_definition_presentation_regions"
)
PROMOTED_SOURCE_ITEMS_FIELD = "promoted_source_items"
_ISO_LIKE_UTC_TIMESTAMP_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z$"
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class SourceReviewScopeError(ValueError):
    """The chosen source partition or appendix classification is invalid."""


def _nonempty(value: object, *, label: str) -> str:
    text = str(value or "").strip()
    if not text:
        raise SourceReviewScopeError(f"{label} is required")
    return text


def _normalized_path(value: object) -> str:
    text = str(value or "").replace("\\", "/").strip()
    while text.startswith("./"):
        text = text[2:]
    path = PurePosixPath(text)
    if (
        not text
        or path.is_absolute()
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        return ""
    return path.as_posix()


def _paper_local_path(folder: Path, value: object) -> Path | None:
    text = _normalized_path(value)
    if not text:
        return None
    paper_root = folder.resolve()
    repository_root = paper_root.parents[1]
    raw = Path(text)
    candidates = {
        (paper_root / raw).resolve(),
        (repository_root / raw).resolve(),
    }
    valid = sorted(
        {
            candidate
            for candidate in candidates
            if candidate.is_relative_to(paper_root) and candidate.is_file()
        },
        key=lambda path: path.as_posix(),
    )
    return valid[0] if len(valid) == 1 else None


def _canonical_anchor(
    folder: Path,
    locator: object,
    *,
    canonical_source_path: str,
) -> dict[str, Any]:
    try:
        anchors = canonical_source_anchor_evidence(
            folder, _nonempty(locator, label="source region source_locator")
        )
    except SourceReviewInputError as exc:
        raise SourceReviewScopeError(str(exc)) from exc
    if len(anchors) != 1:
        raise SourceReviewScopeError(
            "each source region source_locator must identify exactly one source slice"
        )
    anchor = dict(anchors[0])
    if _paper_local_path(folder, anchor.get("path")) != _paper_local_path(
        folder, canonical_source_path
    ):
        raise SourceReviewScopeError(
            "every source region must belong to the canonical text source"
        )
    anchor["path"] = canonical_source_path
    return anchor


def _region_for_line(
    regions: Iterable[Mapping[str, Any]], line_start: int, line_end: int
) -> str:
    matches = [
        str(region["id"])
        for region in regions
        if int(region["source_anchor"]["line_start"]) <= line_start
        and line_end <= int(region["source_anchor"]["line_end"])
    ]
    return matches[0] if len(matches) == 1 else ""


def _anchor_region_ids(
    folder: Path,
    anchors: object,
    *,
    canonical_source_path: str,
    source_text: str,
    regions: list[Mapping[str, Any]],
) -> set[str]:
    if not isinstance(anchors, list):
        return set()
    canonical_file = _paper_local_path(folder, canonical_source_path)
    result: set[str] = set()
    for raw in anchors:
        if not isinstance(raw, Mapping):
            continue
        if _paper_local_path(folder, raw.get("path")) != canonical_file:
            continue
        line_start = raw.get("line_start")
        line_end = raw.get("line_end")
        quote = raw.get("quoted_text")
        quote_digest = str(raw.get("quoted_text_sha256") or "").strip().lower()
        if (
            not isinstance(line_start, int)
            or isinstance(line_start, bool)
            or not isinstance(line_end, int)
            or isinstance(line_end, bool)
            or not isinstance(quote, str)
            or not quote
            or not _SHA256_RE.fullmatch(quote_digest)
            or hashlib.sha256(
                quote.replace("\r\n", "\n").replace("\r", "\n").encode("utf-8")
            ).hexdigest()
            != quote_digest
        ):
            continue
        lines = source_text.split("\n")
        if source_text.endswith("\n"):
            lines.pop()
        if (
            line_start < 1
            or line_end < line_start
            or line_end > len(lines)
            or quote.replace("\r\n", "\n").replace("\r", "\n")
            != "\n".join(lines[line_start - 1 : line_end])
        ):
            continue
        region_id = _region_for_line(regions, line_start, line_end)
        if region_id:
            result.add(region_id)
    return result


def _exact_assignment(
    value: object,
    *,
    expected_ids: set[str],
    region_ids: set[str],
    label: str,
) -> dict[str, str]:
    if not isinstance(value, Mapping):
        raise SourceReviewScopeError(f"source region partition {label} must be an object")
    result: dict[str, str] = {}
    for raw_id, raw_region in value.items():
        entry_id = _nonempty(raw_id, label=f"{label} entry id")
        region_id = _nonempty(raw_region, label=f"{label}.{entry_id}")
        if entry_id in result:
            raise SourceReviewScopeError(
                f"source region partition {label} repeats {entry_id!r}"
            )
        if region_id not in region_ids:
            raise SourceReviewScopeError(
                f"source region partition {label}.{entry_id} names an unknown region"
            )
        result[entry_id] = region_id
    if set(result) != expected_ids:
        missing = sorted(expected_ids - set(result))
        unknown = sorted(set(result) - expected_ids)
        raise SourceReviewScopeError(
            f"source region partition {label} is not exhaustive "
            f"(missing={missing}, unknown={unknown})"
        )
    return dict(sorted(result.items()))


def _scope_approval(value: object, *, label: str) -> dict[str, object]:
    if not isinstance(value, Mapping) or set(value) != {
        "schema",
        "approval_kind",
        "approval_reference",
        "approved_at",
    }:
        raise SourceReviewScopeError(f"{label}.approval fields are malformed")
    if value.get("schema") != 1 or value.get("approval_kind") != (
        "explicit_user_instruction"
    ):
        raise SourceReviewScopeError(
            f"{label}.approval must record schema 1 explicit_user_instruction"
        )
    reference = _nonempty(
        value.get("approval_reference"), label=f"{label}.approval_reference"
    )
    if len(reference) < 20:
        raise SourceReviewScopeError(
            f"{label}.approval_reference must be substantive"
        )
    approved_at = _nonempty(value.get("approved_at"), label=f"{label}.approved_at")
    if not _ISO_LIKE_UTC_TIMESTAMP_RE.fullmatch(approved_at):
        raise SourceReviewScopeError(
            f"{label}.approved_at must be an ISO-like UTC timestamp"
        )
    return {
        "schema": 1,
        "approval_kind": "explicit_user_instruction",
        "approval_reference": reference,
        "approved_at": approved_at,
    }


def materialize_source_region_partition(
    folder: Path,
    map_payload: Mapping[str, Any],
    plan: object,
    *,
    candidate_presentations: object,
    prose_presentations: object,
    prose_presentation_sha256_by_id: Mapping[str, str],
) -> dict[str, Any]:
    """Bind a curator plan to exact canonical source bytes and inventory entries."""

    if not isinstance(plan, Mapping) or set(plan) != {
        "complete",
        "validator",
        "method",
        "validated_at",
        "regions",
        SOURCE_ITEM_REGIONS_FIELD,
        CANDIDATE_PRESENTATION_REGIONS_FIELD,
        PROSE_DEFINITION_PRESENTATION_REGIONS_FIELD,
        PROMOTED_SOURCE_ITEMS_FIELD,
    }:
        raise SourceReviewScopeError("source region partition plan fields are malformed")
    if plan.get("complete") is not True:
        raise SourceReviewScopeError("source region partition plan must record complete: true")
    validator = _nonempty(plan.get("validator"), label="source region validator")
    method = _nonempty(plan.get("method"), label="source region method")
    validated_at = _nonempty(
        plan.get("validated_at"), label="source region validation timestamp"
    )
    if not _ISO_LIKE_UTC_TIMESTAMP_RE.fullmatch(validated_at):
        raise SourceReviewScopeError(
            "source region validated_at must be an ISO-like UTC timestamp"
        )
    source_artifact_sha256 = str(
        map_payload.get("source_artifact_sha256") or ""
    ).strip().lower()
    if not _SHA256_RE.fullmatch(source_artifact_sha256):
        raise SourceReviewScopeError(
            "canonical source artifact digest must be a lowercase SHA-256"
        )
    current = current_canonical_text_source(
        folder, map_payload, repository_root=folder.resolve().parents[1]
    )
    if current is None:
        raise SourceReviewScopeError(
            "cannot read the companion/archive-validated canonical text source"
        )
    source_text, source_path, _source_format = current
    raw_regions = plan.get("regions")
    if not isinstance(raw_regions, list) or not raw_regions:
        raise SourceReviewScopeError("source region partition regions must be nonempty")
    regions: list[dict[str, Any]] = []
    ids: set[str] = set()
    for index, raw in enumerate(raw_regions):
        label = f"source region {index}"
        if not isinstance(raw, Mapping) or set(raw) != {
            "id",
            "kind",
            "source_locator",
        }:
            raise SourceReviewScopeError(f"{label} fields are malformed")
        region_id = _nonempty(raw.get("id"), label=f"{label}.id")
        if region_id in ids:
            raise SourceReviewScopeError(f"source region id {region_id!r} is duplicated")
        ids.add(region_id)
        kind = _nonempty(raw.get("kind"), label=f"{label}.kind")
        if kind not in SOURCE_REGION_KINDS:
            raise SourceReviewScopeError(
                f"{label}.kind must be one of: " + ", ".join(sorted(SOURCE_REGION_KINDS))
            )
        regions.append(
            {
                "id": region_id,
                "kind": kind,
                "source_anchor": _canonical_anchor(
                    folder,
                    raw.get("source_locator"),
                    canonical_source_path=source_path,
                ),
            }
        )
    regions.sort(key=lambda row: int(row["source_anchor"]["line_start"]))
    source_lines = source_text.split("\n")
    if source_text.endswith("\n"):
        source_lines.pop()
    line_count = len(source_lines)
    expected_start = 1
    for region in regions:
        anchor = region["source_anchor"]
        if int(anchor["line_start"]) != expected_start:
            raise SourceReviewScopeError(
                "source regions must form one ordered nonoverlapping partition without gaps"
            )
        expected_start = int(anchor["line_end"]) + 1
    if expected_start != line_count + 1:
        raise SourceReviewScopeError(
            "source regions must cover every line of the canonical text source"
        )
    if not any(region["kind"] == SOURCE_PRIMARY_REGION_KIND for region in regions):
        raise SourceReviewScopeError(
            "source region partition must contain at least one main_text region"
        )

    raw_items = map_payload.get("items")
    if not isinstance(raw_items, Mapping) or any(
        not isinstance(key, str) or not key.strip() or not isinstance(value, Mapping)
        for key, value in raw_items.items()
    ):
        raise SourceReviewScopeError("source map item inventory is malformed")
    raw_candidates = candidate_presentations
    if not isinstance(raw_candidates, list) or any(
        not isinstance(row, Mapping) or not str(row.get("id") or "").strip()
        for row in raw_candidates
    ):
        raise SourceReviewScopeError("candidate presentation inventory is malformed")
    candidate_by_id = {
        str(row["id"]).strip(): row for row in raw_candidates if isinstance(row, Mapping)
    }
    if len(candidate_by_id) != len(raw_candidates):
        raise SourceReviewScopeError("candidate presentation ids are duplicated")
    prose_ids = set(prose_presentation_sha256_by_id)
    if any(
        not isinstance(key, str)
        or not key.strip()
        or not _SHA256_RE.fullmatch(str(value).strip().lower())
        for key, value in prose_presentation_sha256_by_id.items()
    ):
        raise SourceReviewScopeError("prose-definition presentation identities are malformed")

    source_item_regions = _exact_assignment(
        plan.get(SOURCE_ITEM_REGIONS_FIELD),
        expected_ids={str(key) for key in raw_items},
        region_ids=ids,
        label=SOURCE_ITEM_REGIONS_FIELD,
    )
    candidate_regions = _exact_assignment(
        plan.get(CANDIDATE_PRESENTATION_REGIONS_FIELD),
        expected_ids=set(candidate_by_id),
        region_ids=ids,
        label=CANDIDATE_PRESENTATION_REGIONS_FIELD,
    )
    prose_plan_regions = _exact_assignment(
        plan.get(PROSE_DEFINITION_PRESENTATION_REGIONS_FIELD),
        expected_ids=prose_ids,
        region_ids=ids,
        label=PROSE_DEFINITION_PRESENTATION_REGIONS_FIELD,
    )

    for item_id, region_id in source_item_regions.items():
        anchored_regions = _anchor_region_ids(
            folder,
            raw_items[item_id].get("source_anchor_evidence"),
            canonical_source_path=source_path,
            source_text=source_text,
            regions=regions,
        )
        if anchored_regions != {region_id}:
            raise SourceReviewScopeError(
                f"source item {item_id!r} does not lie wholly inside assigned region {region_id!r}"
            )
    for candidate_id, region_id in candidate_regions.items():
        anchored_regions = _anchor_region_ids(
            folder,
            [candidate_by_id[candidate_id].get("source_anchor")],
            canonical_source_path=source_path,
            source_text=source_text,
            regions=regions,
        )
        if anchored_regions != {region_id}:
            raise SourceReviewScopeError(
                f"candidate {candidate_id!r} does not lie wholly inside assigned region {region_id!r}"
            )
    if not isinstance(prose_presentations, list) or len(prose_presentations) != len(
        prose_presentation_sha256_by_id
    ):
        raise SourceReviewScopeError(
            "prose-definition presentation inventory is malformed"
        )
    definition_by_digest = {
        source_prose_definition_presentation_sha256(row): row
        for row in prose_presentations
        if isinstance(row, Mapping)
    }
    if len(definition_by_digest) != len(prose_presentations):
        raise SourceReviewScopeError(
            "prose-definition presentation identities are duplicated"
        )
    for local_id, region_id in prose_plan_regions.items():
        presentation_sha256 = prose_presentation_sha256_by_id[local_id]
        raw = definition_by_digest.get(presentation_sha256)
        anchored_regions = _anchor_region_ids(
            folder,
            [raw.get("source_anchor")] if isinstance(raw, Mapping) else None,
            canonical_source_path=source_path,
            source_text=source_text,
            regions=regions,
        )
        if anchored_regions != {region_id}:
            raise SourceReviewScopeError(
                "prose-definition presentation does not lie wholly inside its assigned region"
            )

    raw_promotions = plan.get(PROMOTED_SOURCE_ITEMS_FIELD)
    if not isinstance(raw_promotions, list):
        raise SourceReviewScopeError("promoted_source_items must be an explicit list")
    promotions: list[dict[str, object]] = []
    promoted_ids: set[str] = set()
    kind_by_region = {str(region["id"]): str(region["kind"]) for region in regions}
    for index, raw in enumerate(raw_promotions):
        label = f"promoted_source_items[{index}]"
        if not isinstance(raw, Mapping) or set(raw) != {
            "source_item",
            "reason",
            "approval",
        }:
            raise SourceReviewScopeError(f"{label} fields are malformed")
        source_item = _nonempty(raw.get("source_item"), label=f"{label}.source_item")
        if source_item not in source_item_regions or source_item in promoted_ids:
            raise SourceReviewScopeError(
                f"{label}.source_item must name one unpromoted source inventory item"
            )
        if kind_by_region[source_item_regions[source_item]] == SOURCE_PRIMARY_REGION_KIND:
            raise SourceReviewScopeError(
                f"{label}.source_item is already assigned to main_text"
            )
        reason = _nonempty(raw.get("reason"), label=f"{label}.reason")
        if len(reason) < 20:
            raise SourceReviewScopeError(f"{label}.reason must be substantive")
        promotions.append(
            {
                "source_item": source_item,
                "reason": reason,
                "approval": _scope_approval(raw.get("approval"), label=label),
            }
        )
        promoted_ids.add(source_item)

    return {
        "schema": SOURCE_REGION_PARTITION_SCHEMA,
        "complete": True,
        "validator": validator,
        "method": method,
        "validated_at": validated_at,
        "source_artifact_sha256": source_artifact_sha256,
        "canonical_source_path": source_path,
        "regions": regions,
        SOURCE_ITEM_REGIONS_FIELD: source_item_regions,
        CANDIDATE_PRESENTATION_REGIONS_FIELD: candidate_regions,
        PROSE_DEFINITION_PRESENTATION_REGIONS_FIELD: {
            str(prose_presentation_sha256_by_id[local_id]).strip().lower(): region_id
            for local_id, region_id in sorted(prose_plan_regions.items())
        },
        PROMOTED_SOURCE_ITEMS_FIELD: sorted(
            promotions, key=lambda row: str(row["source_item"])
        ),
    }


def source_region_partition_errors(
    source_map: object,
    *,
    require_explicit: bool,
) -> list[str]:
    """Validate a materialized partition without source discovery or Lean work."""

    if not isinstance(source_map, Mapping):
        return ["source map must be an object"]
    review = source_map.get("source_named_result_inventory_review")
    partition = (
        review.get(SOURCE_REGION_PARTITION_FIELD)
        if isinstance(review, Mapping)
        else None
    )
    if partition is None and not require_explicit:
        return []
    if not isinstance(partition, Mapping):
        return ["source_named_result_inventory_review.source_region_partition is required"]
    errors: list[str] = []
    expected_fields = {
        "schema",
        "complete",
        "validator",
        "method",
        "validated_at",
        "source_artifact_sha256",
        "canonical_source_path",
        "regions",
        SOURCE_ITEM_REGIONS_FIELD,
        CANDIDATE_PRESENTATION_REGIONS_FIELD,
        PROSE_DEFINITION_PRESENTATION_REGIONS_FIELD,
        PROMOTED_SOURCE_ITEMS_FIELD,
    }
    if set(partition) != expected_fields:
        errors.append("source region partition fields are malformed")
    if partition.get("schema") != SOURCE_REGION_PARTITION_SCHEMA:
        errors.append(
            f"source region partition schema must be {SOURCE_REGION_PARTITION_SCHEMA}"
        )
    if partition.get("complete") is not True:
        errors.append("source region partition complete must be true")
    for field in ("validator", "method"):
        if not str(partition.get(field) or "").strip():
            errors.append(f"source region partition {field} is required")
    validated_at = str(partition.get("validated_at") or "").strip()
    if not _ISO_LIKE_UTC_TIMESTAMP_RE.fullmatch(validated_at):
        errors.append(
            "source region partition validated_at must be an ISO-like UTC timestamp"
        )
    partition_source_sha256 = str(
        partition.get("source_artifact_sha256") or ""
    ).strip().lower()
    if not _SHA256_RE.fullmatch(partition_source_sha256):
        errors.append("source region partition source_artifact_sha256 is malformed")
    if partition_source_sha256 != str(
        source_map.get("source_artifact_sha256") or ""
    ).strip().lower():
        errors.append("source region partition does not pin the canonical source artifact")
    canonical_source_path = _normalized_path(partition.get("canonical_source_path"))
    if not canonical_source_path:
        errors.append("source region partition canonical_source_path is malformed")
    regions = partition.get("regions")
    if not isinstance(regions, list) or not regions:
        errors.append("source region partition regions must be nonempty")
        return errors
    region_ids: set[str] = set()
    previous_end = 0
    for index, raw in enumerate(regions):
        if not isinstance(raw, Mapping) or set(raw) != {"id", "kind", "source_anchor"}:
            errors.append(f"source region {index} fields are malformed")
            continue
        region_id = str(raw.get("id") or "").strip()
        kind = str(raw.get("kind") or "").strip()
        anchor = raw.get("source_anchor")
        if not region_id or region_id in region_ids:
            errors.append(f"source region {index} has a blank or duplicate id")
        region_ids.add(region_id)
        if kind not in SOURCE_REGION_KINDS:
            errors.append(f"source region {index} has an unsupported kind")
        if not isinstance(anchor, Mapping):
            errors.append(f"source region {index} has no source anchor")
            continue
        if set(anchor) != {
            "path",
            "line_start",
            "line_end",
            "quoted_text",
            "quoted_text_sha256",
        }:
            errors.append(f"source region {index} source anchor fields are malformed")
        if _normalized_path(anchor.get("path")) != canonical_source_path:
            errors.append(f"source region {index} belongs to another source artifact")
        start = anchor.get("line_start")
        end = anchor.get("line_end")
        quote = anchor.get("quoted_text")
        digest = str(anchor.get("quoted_text_sha256") or "").strip().lower()
        if (
            not isinstance(start, int)
            or isinstance(start, bool)
            or not isinstance(end, int)
            or isinstance(end, bool)
            or start != previous_end + 1
            or end < start
        ):
            errors.append("source regions overlap or leave an ambiguous boundary")
        else:
            previous_end = end
        if (
            not isinstance(quote, str)
            or not quote
            or not _SHA256_RE.fullmatch(digest)
            or hashlib.sha256(
                quote.replace("\r\n", "\n").replace("\r", "\n").encode("utf-8")
            ).hexdigest()
            != digest
        ):
            errors.append(f"source region {index} has a stale quote digest")
    if not any(
        isinstance(raw, Mapping) and raw.get("kind") == SOURCE_PRIMARY_REGION_KIND
        for raw in regions
    ):
        errors.append("source region partition has no main_text region")
    raw_items = source_map.get("items")
    raw_candidates = review.get("candidate_presentations") if isinstance(review, Mapping) else None
    raw_definitions = (
        review.get("prose_definition_presentations")
        if isinstance(review, Mapping)
        else None
    )
    expected_assignments: tuple[tuple[str, set[str]], ...] = (
        (
            SOURCE_ITEM_REGIONS_FIELD,
            set(raw_items) if isinstance(raw_items, Mapping) else set(),
        ),
        (
            CANDIDATE_PRESENTATION_REGIONS_FIELD,
            {
                str(row.get("id") or "").strip()
                for row in raw_candidates
                if isinstance(row, Mapping)
            }
            if isinstance(raw_candidates, list)
            else set(),
        ),
        (
            PROSE_DEFINITION_PRESENTATION_REGIONS_FIELD,
            {
                source_prose_definition_presentation_sha256(row)
                for row in raw_definitions
                if isinstance(row, Mapping)
            }
            if isinstance(raw_definitions, list)
            else set(),
        ),
    )
    for field, expected in expected_assignments:
        raw_assignment = partition.get(field)
        if (
            not isinstance(raw_assignment, Mapping)
            or any(
                not isinstance(key, str)
                or not key.strip()
                or key != key.strip()
                or not isinstance(value, str)
                or not value.strip()
                or value != value.strip()
                for key, value in raw_assignment.items()
            )
            or set(raw_assignment) != expected
        ):
            errors.append(f"source region partition {field} is not exhaustive")
            continue
        if any(str(value) not in region_ids for value in raw_assignment.values()):
            errors.append(f"source region partition {field} names an unknown region")
    source_item_regions = partition.get(SOURCE_ITEM_REGIONS_FIELD)
    kind_by_region = {
        str(raw.get("id") or "").strip(): str(raw.get("kind") or "").strip()
        for raw in regions
        if isinstance(raw, Mapping)
    }
    promotions = partition.get(PROMOTED_SOURCE_ITEMS_FIELD)
    if not isinstance(promotions, list):
        errors.append("promoted_source_items must be an explicit list")
    else:
        seen_promotions: set[str] = set()
        for index, raw in enumerate(promotions):
            label = f"promoted_source_items[{index}]"
            if not isinstance(raw, Mapping) or set(raw) != {
                "source_item",
                "reason",
                "approval",
            }:
                errors.append(f"{label} fields are malformed")
                continue
            source_item = str(raw.get("source_item") or "").strip()
            assigned_region = (
                str(source_item_regions.get(source_item) or "").strip()
                if isinstance(source_item_regions, Mapping)
                else ""
            )
            if (
                not source_item
                or source_item in seen_promotions
                or not isinstance(raw_items, Mapping)
                or source_item not in raw_items
                or kind_by_region.get(assigned_region) == SOURCE_PRIMARY_REGION_KIND
            ):
                errors.append(f"{label} does not identify one appendix/supplement item")
            seen_promotions.add(source_item)
            if len(str(raw.get("reason") or "").strip()) < 20:
                errors.append(f"{label}.reason must be substantive")
            try:
                _scope_approval(raw.get("approval"), label=label)
            except SourceReviewScopeError as exc:
                errors.append(str(exc))
    return errors


def current_source_region_partition_errors(
    folder: Path,
    source_map: object,
    *,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[str]:
    """Revalidate exact region bytes, total coverage, and physical assignments."""

    errors = source_region_partition_errors(source_map, require_explicit=True)
    if errors or not isinstance(source_map, Mapping):
        return errors
    current = current_canonical_text_source(
        folder,
        source_map,
        repository_root=folder.resolve().parents[1],
        file_bytes_override=file_bytes_override,
    )
    if current is None:
        return ["source region partition canonical text source is unavailable"]
    source_text, source_path, _source_format = current
    review = source_map["source_named_result_inventory_review"]
    assert isinstance(review, Mapping)
    partition = review[SOURCE_REGION_PARTITION_FIELD]
    assert isinstance(partition, Mapping)
    if _paper_local_path(folder, partition.get("canonical_source_path")) != (
        _paper_local_path(folder, source_path)
    ):
        errors.append("source region partition canonical_source_path is stale")
        return errors
    lines = source_text.split("\n")
    if source_text.endswith("\n"):
        lines.pop()
    raw_regions = partition["regions"]
    assert isinstance(raw_regions, list)
    regions = [raw for raw in raw_regions if isinstance(raw, Mapping)]
    if not regions:
        return errors
    if int(regions[-1]["source_anchor"]["line_end"]) != len(lines):
        errors.append("source regions do not cover every canonical source line")
    for index, region in enumerate(regions):
        anchor = region["source_anchor"]
        assert isinstance(anchor, Mapping)
        start = int(anchor["line_start"])
        end = int(anchor["line_end"])
        expected_quote = "\n".join(lines[start - 1 : end])
        if anchor.get("path") != source_path or anchor.get("quoted_text") != expected_quote:
            errors.append(f"source region {index} is not the exact current source slice")

    raw_items = source_map.get("items")
    assert isinstance(raw_items, Mapping)
    source_item_regions = partition[SOURCE_ITEM_REGIONS_FIELD]
    assert isinstance(source_item_regions, Mapping)
    for item_id, region_id in source_item_regions.items():
        raw_item = raw_items.get(item_id)
        anchored = _anchor_region_ids(
            folder,
            raw_item.get("source_anchor_evidence")
            if isinstance(raw_item, Mapping)
            else None,
            canonical_source_path=source_path,
            source_text=source_text,
            regions=regions,
        )
        if anchored != {str(region_id)}:
            errors.append(
                f"source item {item_id!r} does not lie wholly inside assigned region {region_id!r}"
            )

    raw_candidates = review.get("candidate_presentations")
    assert isinstance(raw_candidates, list)
    candidate_by_id = {
        str(row.get("id") or "").strip(): row
        for row in raw_candidates
        if isinstance(row, Mapping)
    }
    candidate_regions = partition[CANDIDATE_PRESENTATION_REGIONS_FIELD]
    assert isinstance(candidate_regions, Mapping)
    for candidate_id, region_id in candidate_regions.items():
        raw = candidate_by_id.get(str(candidate_id))
        anchored = _anchor_region_ids(
            folder,
            [raw.get("source_anchor")] if isinstance(raw, Mapping) else None,
            canonical_source_path=source_path,
            source_text=source_text,
            regions=regions,
        )
        if anchored != {str(region_id)}:
            errors.append(
                f"candidate {candidate_id!r} does not lie wholly inside assigned region {region_id!r}"
            )

    raw_definitions = review.get("prose_definition_presentations")
    assert isinstance(raw_definitions, list)
    definition_by_digest = {
        source_prose_definition_presentation_sha256(row): row
        for row in raw_definitions
        if isinstance(row, Mapping)
    }
    prose_regions = partition[PROSE_DEFINITION_PRESENTATION_REGIONS_FIELD]
    assert isinstance(prose_regions, Mapping)
    for presentation_sha256, region_id in prose_regions.items():
        raw = definition_by_digest.get(str(presentation_sha256))
        anchored = _anchor_region_ids(
            folder,
            [raw.get("source_anchor")] if isinstance(raw, Mapping) else None,
            canonical_source_path=source_path,
            source_text=source_text,
            regions=regions,
        )
        if anchored != {str(region_id)}:
            errors.append(
                "prose-definition presentation does not lie wholly inside its assigned region"
            )

    return errors


def current_closeout_review_policy_errors(
    folder: Path,
    source_map: object,
    *,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[str]:
    """Validate the one chosen scope policy against its complete partition.

    This is the sole appendix-tier policy reader.  Source-manifest gates call
    it after their ordinary inventory checks; presentation and Lean discovery
    do not independently reinterpret the policy.
    """

    if not isinstance(source_map, Mapping):
        return ["source map must be an object"]
    review = source_map.get("source_named_result_inventory_review")
    partition_present = (
        isinstance(review, Mapping)
        and SOURCE_REGION_PARTITION_FIELD in review
    )
    policy_present = CLOSEOUT_REVIEW_POLICY_FIELD in source_map
    if partition_present and not policy_present:
        return [
            "source region partition requires one explicit closeout_review_policy"
        ]
    if not policy_present:
        return []
    try:
        policy = explicit_closeout_review_policy_from_source_map(source_map)
    except FormalizationProtocolError as exc:
        return [str(exc)]
    assert policy is not None
    errors = current_source_region_partition_errors(
        folder,
        source_map,
        file_bytes_override=file_bytes_override,
    )
    mode, mode_error = source_coverage_mode_from_map(source_map)
    if mode_error:
        errors.append(mode_error)
    elif (
        policy.source_scope == CLOSEOUT_SOURCE_SCOPE_ALL_PROSE
        and mode != DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
    ):
        errors.append(
            "all_prose closeout review policy requires "
            "deep_paper_with_all_prose_claims coverage"
        )
    elif (
        policy.source_scope != CLOSEOUT_SOURCE_SCOPE_ALL_PROSE
        and mode == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
    ):
        errors.append(
            "named-theory closeout review policy cannot claim a deep all-prose source scope"
        )
    if errors or policy.source_scope != CLOSEOUT_SOURCE_SCOPE_MAIN_NAMED_THEORY:
        return sorted(set(errors))

    assert isinstance(review, Mapping)
    partition = review.get(SOURCE_REGION_PARTITION_FIELD)
    assert isinstance(partition, Mapping)
    regions = partition.get("regions")
    assignments = partition.get(SOURCE_ITEM_REGIONS_FIELD)
    items = source_map.get("items")
    assert isinstance(regions, list)
    assert isinstance(assignments, Mapping)
    assert isinstance(items, Mapping)
    kind_by_region = {
        str(region.get("id") or "").strip(): str(
            region.get("kind") or ""
        ).strip()
        for region in regions
        if isinstance(region, Mapping)
    }
    approval = (
        policy.scope_approval.projection()
        if policy.scope_approval is not None
        else {}
    )
    environment_kinds = source_named_result_environment_kinds_from_map(source_map)
    for raw_item_id, raw_item in items.items():
        item_id = str(raw_item_id)
        region_id = str(assignments.get(item_id) or "")
        if (
            kind_by_region.get(region_id) == SOURCE_PRIMARY_REGION_KIND
            or not isinstance(raw_item, dict)
            or not source_item_is_named_theoretical_statement(
                raw_item,
                declared_environment_kinds=environment_kinds,
            )
        ):
            continue
        exclusion = raw_item.get(USER_APPROVED_SCOPE_EXCLUSION_KEY)
        if not isinstance(exclusion, Mapping):
            errors.append(
                f"items.{item_id}: main_named_theory policy requires an exact "
                "user-approved appendix exclusion"
            )
            continue
        for field in (
            "schema",
            "approval_kind",
            "approval_reference",
            "approved_at",
        ):
            if exclusion.get(field) != approval.get(field):
                errors.append(
                    f"items.{item_id}: appendix exclusion does not reference "
                    "the chosen main_named_theory approval"
                )
                break
    return sorted(set(errors))


def source_region_partition_projection(source_map: object) -> dict[str, object]:
    """Return content and decisions that define the complete source partition."""

    errors = source_region_partition_errors(source_map, require_explicit=True)
    if errors:
        raise SourceReviewScopeError("; ".join(errors))
    assert isinstance(source_map, Mapping)
    review = source_map["source_named_result_inventory_review"]
    assert isinstance(review, Mapping)
    partition = review[SOURCE_REGION_PARTITION_FIELD]
    assert isinstance(partition, Mapping)
    return {
        "schema": SOURCE_REGION_PARTITION_SCHEMA,
        "source_artifact_sha256": partition["source_artifact_sha256"],
        "regions": [
            {
                "id": raw["id"],
                "kind": raw["kind"],
                "source_quote_sha256": raw["source_anchor"]["quoted_text_sha256"],
                "line_count": (
                    int(raw["source_anchor"]["line_end"])
                    - int(raw["source_anchor"]["line_start"])
                    + 1
                ),
            }
            for raw in partition["regions"]
        ],
        SOURCE_ITEM_REGIONS_FIELD: dict(partition[SOURCE_ITEM_REGIONS_FIELD]),
        CANDIDATE_PRESENTATION_REGIONS_FIELD: dict(
            partition[CANDIDATE_PRESENTATION_REGIONS_FIELD]
        ),
        PROSE_DEFINITION_PRESENTATION_REGIONS_FIELD: dict(
            partition[PROSE_DEFINITION_PRESENTATION_REGIONS_FIELD]
        ),
        PROMOTED_SOURCE_ITEMS_FIELD: list(partition[PROMOTED_SOURCE_ITEMS_FIELD]),
    }


def primary_source_region_projection(source_map: object) -> dict[str, object]:
    """Return only complete main-region bytes plus their classification witnesses."""

    complete = source_region_partition_projection(source_map)
    assert isinstance(source_map, Mapping)
    review = source_map["source_named_result_inventory_review"]
    assert isinstance(review, Mapping)
    partition = review[SOURCE_REGION_PARTITION_FIELD]
    assert isinstance(partition, Mapping)
    kind_by_id = {
        str(raw["id"]): str(raw["kind"])
        for raw in partition["regions"]
        if isinstance(raw, Mapping)
    }
    main_ids = {
        region_id
        for region_id, kind in kind_by_id.items()
        if kind == SOURCE_PRIMARY_REGION_KIND
    }
    primary_item_regions = {
        str(item): str(region)
        for item, region in partition[SOURCE_ITEM_REGIONS_FIELD].items()
        if str(region) in main_ids
    }
    promoted = list(partition[PROMOTED_SOURCE_ITEMS_FIELD])
    promoted_ids = {str(raw["source_item"]) for raw in promoted}
    # A promoted appendix item's exact source bundle is retained later in its
    # semantic row. Its promotion decision belongs here; unrelated appendix
    # region bytes remain outside the terminal main-review identity.
    return {
        "schema": 1,
        "main_regions": [
            region
            for region, raw in zip(
                complete["regions"], partition["regions"], strict=True
            )
            if isinstance(raw, Mapping) and raw.get("kind") == SOURCE_PRIMARY_REGION_KIND
        ],
        "primary_source_item_regions": primary_item_regions,
        "promoted_source_items": promoted,
        "primary_source_item_ids": sorted(set(primary_item_regions) | promoted_ids),
    }


def selected_terminal_source_item_ids(
    source_map: object,
    policy: ResolvedCloseoutReviewPolicy,
) -> frozenset[str] | None:
    """Select source-item seeds for one terminal review.

    ``None`` denotes all selected items. ``main_primary`` returns source-classified
    main entries and explicit promotions; semantic prerequisites governing those
    seeds are added from Lean-emitted statement/definition edges by the caller.
    """

    if policy.repeat_final_scope == CLOSEOUT_REPEAT_SCOPE_ALL_SELECTED:
        return None
    if policy.repeat_final_scope != CLOSEOUT_REPEAT_SCOPE_MAIN_PRIMARY:
        raise SourceReviewScopeError("unsupported terminal repeat/final scope")
    primary = primary_source_region_projection(source_map)
    return frozenset(str(value) for value in primary["primary_source_item_ids"])
