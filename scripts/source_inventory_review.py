#!/usr/bin/env python3
"""Materialize one reviewed source inventory without hand-authored hashes.

The input plan contains the curator-owned completeness assertion, source-only
classification decisions, and literal prose-definition locators. This module
derives exact anchors and digests from the pinned source bytes, then proves that
every independently discovered in-scope named presentation is reconciled by
the supplied statement map. It owns no Lean, semantic-match, dashboard, or
acceptance behavior.
"""

from __future__ import annotations

from collections.abc import Mapping
from copy import deepcopy
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if __package__ in {None, ""}:
    repository_root = str(ROOT)
    if repository_root not in sys.path:
        sys.path.insert(0, repository_root)

from scripts.source_coverage_scope import (
    SOURCE_PROSE_DEFINITION_EXCLUDED_SCOPE_DISPOSITIONS,
    SOURCE_PROSE_DEFINITION_EXCLUSION_APPROVAL_FIELD,
    SOURCE_PROSE_DEFINITION_EXCLUSION_JUDGMENT,
    SOURCE_PROSE_DEFINITION_NORMAL_SCOPE,
    SOURCE_PROSE_DEFINITION_REPEATED_SCOPE,
    SOURCE_PROSE_DEFINITION_REPETITION_JUDGMENT,
    current_canonical_text_source,
    source_coverage_mode_from_map,
    source_named_presentation_in_coverage_scope,
    source_prose_definition_clause_sha256,
    source_prose_definition_inventory_errors,
    source_prose_definition_presentation_errors,
    source_prose_definition_presentation_sha256,
    source_prose_definition_presentations_sha256,
    source_prose_definition_replaced_named_presentation_spans,
)
from scripts.source_named_result_index import (
    REVIEW_CANDIDATE_DISPOSITIONS,
    REVIEW_CANDIDATE_HOLISTIC_DISCOVERY,
    REVIEW_CANDIDATE_MECHANICAL_DISCOVERY,
    UNCLASSIFIED_NAMED_PRESENTATION_KIND,
    byte_pinned_anchor_covers_presentation,
    classify_source_presentation_inventory,
    extract_named_result_presentations,
    named_result_presentations_sha256,
    reconcile_named_result_presentations,
    review_candidate_presentations,
    review_candidate_visible_kind,
    source_paths_match,
    uncovered_named_result_presentations,
)
from scripts.source_review_input import (
    SourceReviewInputError,
    canonical_source_anchor_evidence,
)
from scripts.source_review_scope import (
    SOURCE_REGION_PARTITION_FIELD,
    SourceReviewScopeError,
    materialize_source_region_partition,
)


class SourceInventoryReviewError(ValueError):
    """Raised when a reviewed source-intake plan cannot be materialized."""


_REVIEW_PLAN_FIELDS = frozenset(
    {
        "complete",
        "validator",
        "method",
        "validated_at",
        "environment_kinds",
        "heading_kinds",
        "candidate_presentations",
        "prose_definition_presentations",
        SOURCE_REGION_PARTITION_FIELD,
    }
)

_CANDIDATE_PLAN_FIELDS = frozenset(
    {
        "id",
        "source_locator",
        "presentation_label",
        "scope_disposition",
        "semantic_basis",
    }
)

_PROSE_PLAN_FIELDS = frozenset(
    {
        "id",
        "source_locator",
        "defined_entity_kind",
        "defined_object",
        "definitional_clause",
        "scope_disposition",
        "scope_reason",
        "canonical_presentation_id",
        "semantic_basis",
        "validator",
        "validator_type",
        "validated_at",
        SOURCE_PROSE_DEFINITION_EXCLUSION_APPROVAL_FIELD,
    }
)


def _nonempty(value: object, *, label: str) -> str:
    text = str(value or "").strip()
    if not text:
        raise SourceInventoryReviewError(f"{label} is required")
    return text


def _review_header(plan: Mapping[str, Any]) -> dict[str, Any]:
    unexpected = sorted(
        str(field) for field in plan if field not in _REVIEW_PLAN_FIELDS
    )
    if unexpected:
        raise SourceInventoryReviewError(
            "source inventory review plan has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if plan.get("complete") is not True:
        raise SourceInventoryReviewError(
            "source inventory review plan must record complete: true"
        )
    result: dict[str, Any] = {
        "schema": 1,
        "complete": True,
        "validator": _nonempty(
            plan.get("validator"), label="inventory validator"
        ),
        "method": _nonempty(plan.get("method"), label="inventory method"),
        "validated_at": _nonempty(
            plan.get("validated_at"), label="inventory validation timestamp"
        ),
    }
    for field in ("environment_kinds", "heading_kinds"):
        value = plan.get(field)
        if value is not None:
            if not isinstance(value, Mapping):
                raise SourceInventoryReviewError(f"{field} must be an object")
            result[field] = dict(value)
    return result


def materialize_prose_definition_presentations(
    folder: Path, raw_plans: object
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    """Construct literal prose-definition records and stable local-id routes."""

    if not isinstance(raw_plans, list):
        raise SourceInventoryReviewError(
            "prose_definition_presentations must be an explicit list"
        )
    records: list[dict[str, Any]] = []
    ids: list[str] = []
    canonical_ids: list[str] = []
    for index, raw in enumerate(raw_plans):
        label = f"prose_definition_presentations[{index}]"
        if not isinstance(raw, Mapping):
            raise SourceInventoryReviewError(f"{label} must be an object")
        unexpected = sorted(
            str(field) for field in raw if field not in _PROSE_PLAN_FIELDS
        )
        if unexpected:
            raise SourceInventoryReviewError(
                f"{label} has unsupported field(s): " + ", ".join(unexpected)
            )
        local_id = _nonempty(raw.get("id"), label=f"{label}.id")
        if local_id in ids:
            raise SourceInventoryReviewError(f"{label}.id duplicates `{local_id}`")
        locator = _nonempty(
            raw.get("source_locator"), label=f"{label}.source_locator"
        )
        try:
            anchors = canonical_source_anchor_evidence(folder, locator)
        except SourceReviewInputError as error:
            raise SourceInventoryReviewError(f"{label}: {error}") from error
        if len(anchors) != 1:
            raise SourceInventoryReviewError(
                f"{label}.source_locator must identify exactly one source slice"
            )
        quote = str(anchors[0]["quoted_text"])
        record: dict[str, Any] = {
            "schema": 1,
            "presentation_kind": "definition",
            "defined_entity_kind": _nonempty(
                raw.get("defined_entity_kind"),
                label=f"{label}.defined_entity_kind",
            ),
            "defined_object": _nonempty(
                raw.get("defined_object"), label=f"{label}.defined_object"
            ),
            "definitional_clause": str(
                raw.get("definitional_clause") or quote
            ).strip(),
            "scope_disposition": _nonempty(
                raw.get("scope_disposition"),
                label=f"{label}.scope_disposition",
            ),
            "source_anchor": anchors[0],
        }
        disposition = record["scope_disposition"]
        if disposition == SOURCE_PROSE_DEFINITION_REPEATED_SCOPE:
            canonical_ids.append(
                _nonempty(
                    raw.get("canonical_presentation_id"),
                    label=f"{label}.canonical_presentation_id",
                )
            )
            record.update(
                {
                    "repetition_judgment": SOURCE_PROSE_DEFINITION_REPETITION_JUDGMENT,
                    "semantic_basis": _nonempty(
                        raw.get("semantic_basis"), label=f"{label}.semantic_basis"
                    ),
                    "validator": _nonempty(
                        raw.get("validator"), label=f"{label}.validator"
                    ),
                    "validator_type": _nonempty(
                        raw.get("validator_type"),
                        label=f"{label}.validator_type",
                    ),
                    "validated_at": _nonempty(
                        raw.get("validated_at"), label=f"{label}.validated_at"
                    ),
                }
            )
        else:
            canonical_ids.append("")
        if disposition in SOURCE_PROSE_DEFINITION_EXCLUDED_SCOPE_DISPOSITIONS:
            record.update(
                {
                    "scope_reason": _nonempty(
                        raw.get("scope_reason"), label=f"{label}.scope_reason"
                    ),
                    "scope_judgment": SOURCE_PROSE_DEFINITION_EXCLUSION_JUDGMENT,
                    "validator": _nonempty(
                        raw.get("validator"), label=f"{label}.validator"
                    ),
                    "validator_type": _nonempty(
                        raw.get("validator_type"),
                        label=f"{label}.validator_type",
                    ),
                    "validated_at": _nonempty(
                        raw.get("validated_at"), label=f"{label}.validated_at"
                    ),
                }
            )
            approval = raw.get(SOURCE_PROSE_DEFINITION_EXCLUSION_APPROVAL_FIELD)
            if approval is not None:
                record[SOURCE_PROSE_DEFINITION_EXCLUSION_APPROVAL_FIELD] = approval
        records.append(record)
        ids.append(local_id)

    normal_digest_by_id = {
        local_id: source_prose_definition_presentation_sha256(record)
        for local_id, record in zip(ids, records, strict=True)
        if record["scope_disposition"] == SOURCE_PROSE_DEFINITION_NORMAL_SCOPE
    }
    for local_id, canonical_id, record in zip(
        ids, canonical_ids, records, strict=True
    ):
        clause_digest = source_prose_definition_clause_sha256(record)
        if record["scope_disposition"] == SOURCE_PROSE_DEFINITION_REPEATED_SCOPE:
            canonical_digest = normal_digest_by_id.get(canonical_id)
            if not canonical_digest:
                raise SourceInventoryReviewError(
                    f"prose definition `{local_id}` names noncanonical or unknown "
                    f"presentation `{canonical_id}`"
                )
            record["canonical_presentation_sha256"] = canonical_digest
            record["repetition_judgment_source_sha256"] = clause_digest
        elif (
            record["scope_disposition"]
            in SOURCE_PROSE_DEFINITION_EXCLUDED_SCOPE_DISPOSITIONS
        ):
            record["scope_judgment_source_sha256"] = clause_digest
        errors = source_prose_definition_presentation_errors(record)
        if errors:
            raise SourceInventoryReviewError(
                f"prose definition `{local_id}` is invalid: " + "; ".join(errors)
            )
    return records, {
        local_id: source_prose_definition_presentation_sha256(record)
        for local_id, record in zip(ids, records, strict=True)
    }


def materialize_review_candidate_presentations(
    folder: Path,
    raw_plans: object,
    presentations: list[Any],
    *,
    source_text: str,
    source_path: str,
) -> list[dict[str, Any]]:
    """Materialize one exact source-only disposition per labelled candidate."""

    if not isinstance(raw_plans, list):
        raise SourceInventoryReviewError(
            "candidate_presentations must be an explicit list"
        )
    candidates = review_candidate_presentations(presentations)
    records: list[dict[str, Any]] = []
    used_candidate_indexes: set[int] = set()
    ids: set[str] = set()
    for index, raw in enumerate(raw_plans):
        label = f"candidate_presentations[{index}]"
        if not isinstance(raw, Mapping):
            raise SourceInventoryReviewError(f"{label} must be an object")
        unexpected = sorted(str(field) for field in raw if field not in _CANDIDATE_PLAN_FIELDS)
        if unexpected:
            raise SourceInventoryReviewError(
                f"{label} has unsupported field(s): " + ", ".join(unexpected)
            )
        local_id = _nonempty(raw.get("id"), label=f"{label}.id")
        if local_id in ids:
            raise SourceInventoryReviewError(f"{label}.id duplicates `{local_id}`")
        ids.add(local_id)
        disposition = _nonempty(
            raw.get("scope_disposition"), label=f"{label}.scope_disposition"
        )
        if disposition not in REVIEW_CANDIDATE_DISPOSITIONS:
            raise SourceInventoryReviewError(
                f"{label}.scope_disposition must be one of: "
                + ", ".join(sorted(REVIEW_CANDIDATE_DISPOSITIONS))
            )
        locator = _nonempty(
            raw.get("source_locator"), label=f"{label}.source_locator"
        )
        try:
            anchors = canonical_source_anchor_evidence(folder, locator)
        except SourceReviewInputError as error:
            raise SourceInventoryReviewError(f"{label}: {error}") from error
        if len(anchors) != 1:
            raise SourceInventoryReviewError(
                f"{label}.source_locator must identify exactly one source slice"
            )
        anchor = _canonicalize_candidate_anchor_path(
            folder,
            anchors[0],
            source_path=source_path,
        )
        matches = [
            candidate_index
            for candidate_index, candidate in enumerate(candidates)
            if source_paths_match(anchor.get("path"), source_path)
            and anchor.get("line_start") == candidate.line_start
            and anchor.get("line_end") == candidate.line_end
            and byte_pinned_anchor_covers_presentation(
                anchor,
                candidate,
                source_text=source_text,
                source_path=source_path,
            )
        ]
        if len(matches) > 1:
            raise SourceInventoryReviewError(
                f"{label}.source_locator ambiguously identifies multiple current review candidates"
            )
        if matches:
            candidate_index = matches[0]
            if candidate_index in used_candidate_indexes:
                raise SourceInventoryReviewError(
                    f"{label}.source_locator duplicates an earlier review candidate"
                )
            candidate = candidates[candidate_index]
            used_candidate_indexes.add(candidate_index)
            presentation_label = candidate.label
            visible_kind = review_candidate_visible_kind(candidate.kind)
            discovery_basis = REVIEW_CANDIDATE_MECHANICAL_DISCOVERY
        else:
            presentation_label = _nonempty(
                raw.get("presentation_label"),
                label=f"{label}.presentation_label",
            )
            visible_kind = "holistic"
            discovery_basis = REVIEW_CANDIDATE_HOLISTIC_DISCOVERY
        records.append(
            {
                "schema": 1,
                "id": local_id,
                "presentation_label": presentation_label,
                "visible_kind": visible_kind,
                "scope_disposition": disposition,
                "semantic_basis": _nonempty(
                    raw.get("semantic_basis"), label=f"{label}.semantic_basis"
                ),
                "discovery_basis": discovery_basis,
                "source_anchor": anchor,
            }
        )
    return records


def _canonicalize_candidate_anchor_path(
    folder: Path,
    anchor: Mapping[str, Any],
    *,
    source_path: str,
) -> dict[str, Any]:
    """Use the canonical text-source spelling for an equivalent local anchor.

    A curator may naturally write either ``source.txt:10`` or the repository
    relative ``papers/P/source.txt:10`` in a holistic candidate queue.  Both
    spellings are accepted by the source-anchor constructor only when they
    resolve inside the paper.  The reviewed candidate inventory, however,
    compares its anchor with the canonical text-source path exactly.  Normalize
    only when those two spellings resolve to that same file; this is not a
    basename fallback and cannot join a candidate to a different source.
    """

    normalized = dict(anchor)
    normalized["path"] = _canonicalize_current_source_path(
        folder,
        str(normalized.get("path") or ""),
        source_path=source_path,
    )
    return normalized


def _resolve_paper_local_source_path(folder: Path, path: str) -> Path | None:
    """Resolve one explicit locator spelling only when it names one paper file."""

    raw_path = Path(path)
    paper_root = folder.resolve()
    repository_root = paper_root.parents[1]
    candidates = {
        raw_path.resolve()
        if raw_path.is_absolute()
        else (folder / raw_path).resolve(),
        raw_path.resolve()
        if raw_path.is_absolute()
        else (repository_root / raw_path).resolve(),
    }
    existing = [
        candidate
        for candidate in candidates
        if candidate.is_relative_to(paper_root) and candidate.is_file()
    ]
    return existing[0] if len(existing) == 1 else None


def _canonicalize_current_source_path(
    folder: Path,
    raw_path: str,
    *,
    source_path: str,
) -> str:
    """Normalize an explicitly equivalent paper-local source locator.

    This deliberately resolves both strings beneath the current paper before
    treating them as equivalent.  It therefore supports the two explicit
    spellings that arise in practice (paper-relative and repository-relative)
    without a basename or suffix fallback.
    """

    raw_path = raw_path.strip()
    if not raw_path:
        return raw_path
    canonical_file = _resolve_paper_local_source_path(folder, source_path)
    declared_file = _resolve_paper_local_source_path(folder, raw_path)
    if canonical_file is not None and declared_file == canonical_file:
        return source_path
    return raw_path


def _canonicalize_source_location_paths(
    folder: Path,
    source_location: object,
    *,
    source_path: str,
) -> object:
    """Normalize explicit source-locator path spellings in a map location."""

    if not isinstance(source_location, str) or not source_location.strip():
        return source_location
    normalized_parts: list[str] = []
    for part in source_location.split(";"):
        prefix_length = len(part) - len(part.lstrip())
        prefix = part[:prefix_length]
        body = part[prefix_length:]
        declared_path, separator, suffix = body.partition(":")
        if not separator:
            normalized_parts.append(part)
            continue
        normalized_parts.append(
            prefix
            + _canonicalize_current_source_path(
                folder, declared_path, source_path=source_path
            )
            + separator
            + suffix
        )
    return ";".join(normalized_parts)


def _canonicalize_map_source_paths(
    folder: Path,
    source_items: object,
    *,
    source_path: str,
) -> object:
    """Prepare an in-memory map copy for current-source reconciliation only."""

    if not isinstance(source_items, Mapping):
        return source_items
    normalized = deepcopy(source_items)
    for item in normalized.values():
        if not isinstance(item, dict):
            continue
        item["source_location"] = _canonicalize_source_location_paths(
            folder, item.get("source_location"), source_path=source_path
        )
        anchors = item.get("source_anchor_evidence")
        if isinstance(anchors, list):
            for anchor in anchors:
                if isinstance(anchor, dict):
                    anchor["path"] = _canonicalize_current_source_path(
                        folder,
                        str(anchor.get("path") or ""),
                        source_path=source_path,
                    )
        relation = item.get("source_presentation_reconciliation")
        if isinstance(relation, dict):
            core_anchor = relation.get("core_anchor")
            if isinstance(core_anchor, dict):
                core_anchor["path"] = _canonicalize_current_source_path(
                    folder,
                    str(core_anchor.get("path") or ""),
                    source_path=source_path,
                )
    return normalized


def materialize_source_named_result_inventory_review(
    folder: Path,
    map_payload: Mapping[str, Any],
    plan: Mapping[str, Any],
    *,
    prose_presentations: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Derive the complete named/prose inventory receipt from reviewed inputs."""

    review = _review_header(plan)
    raw_prose_plans = plan.get("prose_definition_presentations")
    if prose_presentations is None:
        prose_presentations, prose_sha256_by_id = materialize_prose_definition_presentations(
            folder, plan.get("prose_definition_presentations")
        )
    else:
        if not isinstance(raw_prose_plans, list) or len(raw_prose_plans) != len(
            prose_presentations
        ):
            raise SourceInventoryReviewError(
                "prose-definition plan differs from its materialized inventory"
            )
        prose_sha256_by_id = {}
        for index, (raw_plan, record) in enumerate(
            zip(raw_prose_plans, prose_presentations, strict=True)
        ):
            if not isinstance(raw_plan, Mapping):
                raise SourceInventoryReviewError(
                    f"prose_definition_presentations[{index}] must be an object"
                )
            local_id = _nonempty(
                raw_plan.get("id"),
                label=f"prose_definition_presentations[{index}].id",
            )
            prose_sha256_by_id[local_id] = (
                source_prose_definition_presentation_sha256(record)
            )
    review["prose_definition_presentations"] = prose_presentations
    review["discovered_prose_definition_sha256"] = (
        source_prose_definition_presentations_sha256(prose_presentations)
    )

    completed = _complete_source_named_result_inventory_review(
        folder,
        map_payload,
        review,
        candidate_plans=(
            plan.get("candidate_presentations")
            if "candidate_presentations" in plan
            else None
        ),
    )
    partition_plan = plan.get(SOURCE_REGION_PARTITION_FIELD)
    if partition_plan is not None:
        try:
            completed[SOURCE_REGION_PARTITION_FIELD] = (
                materialize_source_region_partition(
                    folder,
                    map_payload,
                    partition_plan,
                    candidate_presentations=completed.get(
                        "candidate_presentations"
                    ),
                    prose_presentations=prose_presentations,
                    prose_presentation_sha256_by_id=prose_sha256_by_id,
                )
            )
        except SourceReviewScopeError as error:
            raise SourceInventoryReviewError(str(error)) from error
    return completed


def materialize_candidate_inventory_migration(
    folder: Path,
    map_payload: Mapping[str, Any],
    plan: Mapping[str, Any],
) -> dict[str, Any]:
    """Add the current candidate surface to one already reviewed inventory.

    Older inventories already own their prose-definition and ordinary named-result
    review.  This migration preserves those reviewed records byte-for-byte and
    asks only for the newly explicit candidate ledger plus a complete source-only
    holistic pass.  It grants no Lean or source-to-Lean semantic judgment.
    """

    existing = map_payload.get("source_named_result_inventory_review")
    if not isinstance(existing, Mapping) or existing.get("complete") is not True:
        raise SourceInventoryReviewError(
            "candidate migration requires an existing complete source inventory"
        )
    if "candidate_presentations" in existing:
        raise SourceInventoryReviewError(
            "source inventory already has an explicit candidate ledger"
        )
    prose_presentations = existing.get("prose_definition_presentations")
    if not isinstance(prose_presentations, list):
        raise SourceInventoryReviewError(
            "candidate migration requires the existing explicit prose-definition ledger"
        )
    if "candidate_presentations" not in plan:
        raise SourceInventoryReviewError(
            "candidate migration plan must contain candidate_presentations"
        )

    review = _review_header(plan)
    review["prose_definition_presentations"] = list(prose_presentations)
    review["discovered_prose_definition_sha256"] = (
        source_prose_definition_presentations_sha256(prose_presentations)
    )
    completed = _complete_source_named_result_inventory_review(
        folder,
        map_payload,
        review,
        candidate_plans=plan.get("candidate_presentations"),
    )
    if plan.get(SOURCE_REGION_PARTITION_FIELD) is not None:
        raise SourceInventoryReviewError(
            "candidate-only migration cannot introduce or replace the source region partition"
        )
    return completed


def _complete_source_named_result_inventory_review(
    folder: Path,
    map_payload: Mapping[str, Any],
    review: dict[str, Any],
    *,
    candidate_plans: object | None,
) -> dict[str, Any]:
    """Bind reviewed inventory decisions to current source bytes and coverage."""

    source_digest = str(
        map_payload.get("source_artifact_sha256") or ""
    ).strip().lower()
    repository_root = folder.resolve().parents[1]
    current_source = current_canonical_text_source(
        folder, map_payload, repository_root=repository_root
    )
    if current_source is None:
        raise SourceInventoryReviewError(
            "cannot read the exact companion/archive-validated canonical source artifact"
        )
    source_text, source_path, source_format = current_source
    review["source_artifact_sha256"] = source_digest

    payload_with_review = dict(map_payload)
    payload_with_review["source_named_result_inventory_review"] = review
    prose_errors = source_prose_definition_inventory_errors(
        folder,
        payload_with_review,
        repository_root=repository_root,
    )
    if prose_errors:
        raise SourceInventoryReviewError(
            "source prose-definition inventory is incomplete: "
            + "; ".join(prose_errors)
        )
    try:
        candidate_plan_present = candidate_plans is not None
        presentations = extract_named_result_presentations(
            source_text,
            source_format=source_format,
            environment_kinds=review.get("environment_kinds"),
            heading_kinds=review.get("heading_kinds"),
            include_review_candidates=candidate_plan_present,
        )
    except ValueError as error:
        raise SourceInventoryReviewError(
            f"source presentation classification is invalid: {error}"
        ) from error
    if candidate_plan_present:
        candidate_records = materialize_review_candidate_presentations(
            folder,
            candidate_plans,
            presentations,
            source_text=source_text,
            source_path=source_path,
        )
        review["candidate_presentations"] = candidate_records
        try:
            presentation_inventory = classify_source_presentation_inventory(
                presentations,
                source_text=source_text,
                source_path=source_path,
                candidate_dispositions=candidate_records,
            )
        except (TypeError, ValueError) as error:
            raise SourceInventoryReviewError(str(error)) from error
        review["discovered_candidate_presentation_sha256"] = (
            presentation_inventory.candidate_sha256
        )
        presentations = list(presentation_inventory.classified)
    mode, mode_error = source_coverage_mode_from_map(payload_with_review)
    if mode_error:
        raise SourceInventoryReviewError(mode_error)
    replaced_definition_spans = (
        source_prose_definition_replaced_named_presentation_spans(
            folder,
            payload_with_review,
            presentations,
            repository_root=repository_root,
        )
    )
    in_scope = [
        presentation
        for presentation in presentations
        if source_named_presentation_in_coverage_scope(presentation.kind, mode)
        and not (
            presentation.kind == "definition"
            and (presentation.line_start, presentation.line_end)
            in replaced_definition_spans
        )
    ]
    unclassified = [
        presentation
        for presentation in in_scope
        if presentation.kind == UNCLASSIFIED_NAMED_PRESENTATION_KIND
    ]
    if unclassified:
        rendered = ", ".join(
            f"{item.label}@{item.line_start}-{item.line_end}"
            for item in unclassified
        )
        raise SourceInventoryReviewError(
            "source inventory leaves named presentation(s) unclassified: "
            + rendered
        )
    reconciliation_items = _canonicalize_map_source_paths(
        folder,
        payload_with_review.get("items"),
        source_path=source_path,
    )
    reconciliations = reconcile_named_result_presentations(
        in_scope,
        reconciliation_items,
        source_text=source_text,
        source_path=source_path,
    )
    uncovered = uncovered_named_result_presentations(reconciliations)
    if uncovered:
        rendered = ", ".join(
            f"{item.label}@{item.line_start}-{item.line_end}" for item in uncovered
        )
        raise SourceInventoryReviewError(
            "source inventory has uncovered named presentation(s): " + rendered
        )
    review["discovered_named_result_sha256"] = (
        named_result_presentations_sha256(in_scope)
    )
    return review
