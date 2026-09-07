#!/usr/bin/env python3
"""Upgrade a legacy complete source inventory with the explicit candidate surface.

This command is a source-only migration.  It discovers labelled candidate
presentations from the current byte-pinned source, emits a non-evidence work
queue, requires an explicit holistic full-text confirmation, and then
materializes the reviewed candidate ledger without reopening Lean semantic
judgments or the already reviewed prose-definition inventory.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections.abc import Mapping
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.closeout_execution_state import atomic_write_json
from scripts.closeout_intake_freeze import SOURCE_INVENTORY_REVIEW_REQUIRED_FIELD
from scripts.prepare_v11_source_map import PreparationError, prepare
from scripts.source_coverage_scope import current_canonical_text_source
from scripts.source_inventory_review import (
    SourceInventoryReviewError,
    materialize_candidate_inventory_migration,
)
from scripts.source_record_artifact_io import atomic_write_text_if_changed
from scripts.source_named_result_index import (
    REVIEW_CANDIDATE_DISPOSITIONS,
    REVIEW_CANDIDATE_HOLISTIC_DISCOVERY,
    REVIEW_CANDIDATE_MECHANICAL_DISCOVERY,
    extract_named_result_presentations,
    review_candidate_presentations,
    review_candidate_presentations_sha256,
    review_candidate_visible_kind,
)
from scripts.source_review_input import (
    SourceReviewInputError,
    canonical_source_anchor_evidence,
)

QUEUE_PREFIX = "source_inventory_candidate_review_"
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class SourceInventoryCandidateReissueError(ValueError):
    """Raised when a candidate-surface review queue is stale or incomplete."""


def _digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def _write_materialized_json(path: Path, payload: Mapping[str, Any]) -> None:
    """Preserve curator-facing field order while retaining an atomic write."""

    atomic_write_text_if_changed(
        path,
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
    )


def _load(path: Path, *, label: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceInventoryCandidateReissueError(
            f"could not read {label}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceInventoryCandidateReissueError(f"{label} must be an object")
    return payload


def inventory_needs_candidate_review(source_map: Mapping[str, Any]) -> bool:
    """Return whether a complete legacy inventory lacks the explicit ledger."""

    review = source_map.get("source_named_result_inventory_review")
    return (
        isinstance(review, Mapping)
        and review.get("complete") is True
        and "candidate_presentations" not in review
    )


def _current_source(
    paper_dir: Path, source_map: Mapping[str, Any]
) -> tuple[str, str, str]:
    current = current_canonical_text_source(
        paper_dir,
        source_map,
        repository_root=paper_dir.resolve().parents[1],
    )
    if current is None:
        raise SourceInventoryCandidateReissueError(
            "cannot read the exact canonical source artifact"
        )
    return current


def decision_template(paper_dir: Path, source_map: Mapping[str, Any]) -> dict[str, Any]:
    """Return a blank, source-bound queue for the newly explicit surface."""

    review = source_map.get("source_named_result_inventory_review")
    if not inventory_needs_candidate_review(source_map) or not isinstance(
        review, Mapping
    ):
        raise SourceInventoryCandidateReissueError(
            "paper has no legacy complete inventory requiring candidate review"
        )
    source_text, source_path, source_format = _current_source(paper_dir, source_map)
    try:
        presentations = extract_named_result_presentations(
            source_text,
            source_format=source_format,
            environment_kinds=review.get("environment_kinds"),
            heading_kinds=review.get("heading_kinds"),
            include_review_candidates=True,
        )
    except ValueError as exc:
        raise SourceInventoryCandidateReissueError(str(exc)) from exc
    candidates = review_candidate_presentations(presentations)
    items: list[dict[str, Any]] = []
    for index, candidate in enumerate(candidates, start=1):
        locator = f"{source_path}:{candidate.line_start}-{candidate.line_end}"
        try:
            anchors = canonical_source_anchor_evidence(paper_dir, locator)
        except SourceReviewInputError as exc:
            raise SourceInventoryCandidateReissueError(str(exc)) from exc
        if len(anchors) != 1:
            raise SourceInventoryCandidateReissueError(
                f"candidate {index} does not resolve to one exact source anchor"
            )
        items.append(
            {
                "id": f"candidate_{index:03d}",
                "discovery_basis": REVIEW_CANDIDATE_MECHANICAL_DISCOVERY,
                "source_locator": locator,
                "source_quote_sha256": anchors[0]["quoted_text_sha256"],
                "presentation_label": candidate.label,
                "visible_kind": review_candidate_visible_kind(candidate.kind),
                "scope_disposition": "",
                "semantic_basis": "",
            }
        )
    source_sha = str(source_map.get("source_artifact_sha256") or "").lower()
    if not SHA256_RE.fullmatch(source_sha):
        raise SourceInventoryCandidateReissueError(
            "source map lacks a canonical source-artifact digest"
        )
    return {
        "schema": 1,
        "paper": paper_dir.name,
        "acceptance_credential": False,
        "source_artifact_sha256": source_sha,
        "prior_inventory_sha256": _digest(review),
        "mechanical_candidate_surface_sha256": (
            review_candidate_presentations_sha256(candidates)
        ),
        "holistic_source_review_complete": False,
        "method": "",
        "comment": (
            "Non-evidence source-only work queue. Classify every prefilled "
            "candidate, read the complete pinned source for additional material "
            "mathematical presentations, append any such exact source locators, "
            "and set holistic_source_review_complete only after that pass."
        ),
        "items": items,
    }


def current_decision_template_and_path(
    paper_dir: Path, source_map: Mapping[str, Any] | None = None
) -> tuple[dict[str, Any], Path] | None:
    """Return the current queue and its content-addressed audit path."""

    if source_map is None:
        source_map = _load(
            paper_dir / "audit" / "paper_statement_map.json",
            label="paper statement map",
        )
    if not inventory_needs_candidate_review(source_map):
        return None
    template = decision_template(paper_dir, source_map)
    path = paper_dir / "audit" / f"{QUEUE_PREFIX}{_digest(template)}.json"
    return template, path


def _queue_errors(
    paper_dir: Path,
    payload: object,
    *,
    template: Mapping[str, Any],
    require_complete: bool,
) -> list[str]:
    errors: list[str] = []
    if not isinstance(payload, Mapping):
        return ["decision queue must be an object"]
    if set(payload) != set(template):
        errors.append("decision queue fields differ from the current queue schema")
    for field in (
        "schema",
        "paper",
        "acceptance_credential",
        "source_artifact_sha256",
        "prior_inventory_sha256",
        "mechanical_candidate_surface_sha256",
    ):
        if payload.get(field) != template.get(field):
            errors.append(f"decision queue has stale {field}")
    raw_items = payload.get("items")
    if not isinstance(raw_items, list):
        return [*errors, "decision queue items must be a list"]
    expected_mechanical = [
        item for item in template.get("items", []) if isinstance(item, Mapping)
    ]
    actual_mechanical = [
        item
        for item in raw_items
        if isinstance(item, Mapping)
        and item.get("discovery_basis") == REVIEW_CANDIDATE_MECHANICAL_DISCOVERY
    ]
    identity_fields = (
        "id",
        "discovery_basis",
        "source_locator",
        "source_quote_sha256",
        "presentation_label",
        "visible_kind",
    )
    if len(actual_mechanical) != len(expected_mechanical):
        errors.append("decision queue changed the mechanical candidate row count")
    else:
        for index, (actual, expected) in enumerate(
            zip(actual_mechanical, expected_mechanical, strict=True), start=1
        ):
            if any(
                actual.get(field) != expected.get(field) for field in identity_fields
            ):
                errors.append(f"mechanical candidate {index} has stale identity")
    seen_ids: set[str] = set()
    allowed_item_fields = {
        "id",
        "discovery_basis",
        "source_locator",
        "source_quote_sha256",
        "presentation_label",
        "visible_kind",
        "scope_disposition",
        "semantic_basis",
    }
    for index, item in enumerate(raw_items, start=1):
        if not isinstance(item, Mapping):
            errors.append(f"candidate item {index} must be an object")
            continue
        unexpected = sorted(
            str(field) for field in item if field not in allowed_item_fields
        )
        if unexpected:
            errors.append(
                f"candidate item {index} has unsupported fields: "
                + ", ".join(unexpected)
            )
        item_id = str(item.get("id") or "").strip()
        if not item_id or item_id in seen_ids:
            errors.append(f"candidate item {index} has a blank or duplicate id")
        seen_ids.add(item_id)
        basis = str(item.get("discovery_basis") or "").strip()
        if basis not in {
            REVIEW_CANDIDATE_MECHANICAL_DISCOVERY,
            REVIEW_CANDIDATE_HOLISTIC_DISCOVERY,
        }:
            errors.append(f"candidate item {index} has an invalid discovery basis")
        if (
            basis == REVIEW_CANDIDATE_HOLISTIC_DISCOVERY
            and item.get("visible_kind") != "holistic"
        ):
            errors.append(
                f"holistic candidate item {index} must use visible_kind holistic"
            )
        locator = str(item.get("source_locator") or "").strip()
        label = str(item.get("presentation_label") or "").strip()
        if not locator or not label:
            errors.append(f"candidate item {index} lacks a locator or label")
        else:
            try:
                anchors = canonical_source_anchor_evidence(paper_dir, locator)
            except SourceReviewInputError as exc:
                errors.append(f"candidate item {index}: {exc}")
            else:
                if len(anchors) != 1:
                    errors.append(
                        f"candidate item {index} does not identify one source slice"
                    )
                recorded_quote = str(item.get("source_quote_sha256") or "").strip()
                if recorded_quote and (
                    len(anchors) != 1
                    or recorded_quote != anchors[0].get("quoted_text_sha256")
                ):
                    errors.append(f"candidate item {index} source quote is stale")
        disposition = str(item.get("scope_disposition") or "").strip()
        reason = str(item.get("semantic_basis") or "").strip()
        if disposition and disposition not in REVIEW_CANDIDATE_DISPOSITIONS:
            errors.append(f"candidate item {index} has an invalid disposition")
        if require_complete and (
            disposition not in REVIEW_CANDIDATE_DISPOSITIONS or not reason
        ):
            errors.append(f"candidate item {index} lacks a reviewed disposition")
    if require_complete:
        if payload.get("holistic_source_review_complete") is not True:
            errors.append("holistic full-source review is not confirmed complete")
        if not str(payload.get("method") or "").strip():
            errors.append("review method is required")
    elif payload.get("holistic_source_review_complete") not in {True, False}:
        errors.append("holistic_source_review_complete must be boolean")
    return errors


def current_decision_queue_error(
    paper_dir: Path,
    path: Path,
    *,
    template: Mapping[str, Any],
) -> str:
    """Return structural/staleness errors while allowing blank review fields."""

    try:
        payload: object = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return str(exc)
    return "; ".join(
        _queue_errors(
            paper_dir,
            payload,
            template=template,
            require_complete=False,
        )
    )


def decision_queue_ready(
    paper_dir: Path,
    path: Path,
    *,
    template: Mapping[str, Any],
) -> bool:
    """Return whether every source-only decision and holistic confirmation exists."""

    try:
        payload: object = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    return not _queue_errors(
        paper_dir,
        payload,
        template=template,
        require_complete=True,
    )


def apply_decisions(
    paper_dir: Path,
    decisions: Mapping[str, Any],
    *,
    validator: str,
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    """Materialize a complete candidate review and optional preparer config."""

    source_map_path = paper_dir / "audit" / "paper_statement_map.json"
    source_map = _load(source_map_path, label="paper statement map")
    template = decision_template(paper_dir, source_map)
    errors = _queue_errors(
        paper_dir,
        decisions,
        template=template,
        require_complete=True,
    )
    if errors:
        raise SourceInventoryCandidateReissueError("; ".join(errors))
    reviewer = validator.strip()
    if not reviewer:
        raise SourceInventoryCandidateReissueError("--validator must be nonempty")
    candidate_plans = [
        {
            field: item[field]
            for field in (
                "id",
                "source_locator",
                "presentation_label",
                "scope_disposition",
                "semantic_basis",
            )
        }
        for item in decisions["items"]
    ]
    existing_review = source_map["source_named_result_inventory_review"]
    review_plan: dict[str, Any] = {
        "complete": True,
        "validator": reviewer,
        "method": str(decisions["method"]).strip(),
        "validated_at": datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z"),
        "candidate_presentations": candidate_plans,
    }
    for field in ("environment_kinds", "heading_kinds"):
        value = existing_review.get(field)
        if isinstance(value, Mapping):
            review_plan[field] = dict(value)

    config_path = paper_dir / "audit" / "v11_source_map_preparation_config.json"
    status = _load(paper_dir / "status.json", label="paper status")
    config: dict[str, Any] | None = None
    if config_path.is_file():
        loaded_config = _load(config_path, label="source-map preparation config")
        existing_plan = loaded_config.get("source_named_result_inventory_review")
        if isinstance(existing_plan, Mapping):
            config = dict(loaded_config)
            merged_plan = dict(existing_plan)
            merged_plan.update(review_plan)
            config["source_named_result_inventory_review"] = merged_plan
            try:
                source_map = prepare(source_map, config, folder=paper_dir)
            except (PreparationError, RuntimeError, ValueError) as exc:
                raise SourceInventoryCandidateReissueError(str(exc)) from exc
    if config is None:
        if status.get(SOURCE_INVENTORY_REVIEW_REQUIRED_FIELD) is True:
            raise SourceInventoryCandidateReissueError(
                "reviewed-source-inventory authority requires its preparation plan"
            )
        try:
            migrated = materialize_candidate_inventory_migration(
                paper_dir,
                source_map,
                review_plan,
            )
        except SourceInventoryReviewError as exc:
            raise SourceInventoryCandidateReissueError(str(exc)) from exc
        source_map = dict(source_map)
        preserved_order = dict(existing_review)
        preserved_order.update(migrated)
        source_map["source_named_result_inventory_review"] = preserved_order
    return source_map, config


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--emit-current-template", action="store_true")
    mode.add_argument("--decisions", type=Path)
    parser.add_argument("--validator", default="")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()

    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    if not paper_dir.is_dir():
        raise SystemExit(f"unknown paper folder: {args.paper}")
    try:
        current = current_decision_template_and_path(paper_dir)
        if current is None:
            raise SourceInventoryCandidateReissueError(
                "paper does not need candidate-inventory migration"
            )
        template, queue_path = current
        if args.emit_current_template:
            if args.write:
                raise SourceInventoryCandidateReissueError(
                    "--write is not used with --emit-current-template"
                )
            if not queue_path.is_file():
                atomic_write_json(queue_path, template)
            print(queue_path.relative_to(root))
            return 0
        if args.decisions is None:
            raise SourceInventoryCandidateReissueError("--decisions is required")
        decision_path = (
            args.decisions if args.decisions.is_absolute() else root / args.decisions
        )
        decisions = _load(decision_path, label="candidate decision queue")
        source_map, config = apply_decisions(
            paper_dir,
            decisions,
            validator=args.validator,
        )
        if not args.write:
            print(json.dumps(source_map, indent=2, sort_keys=True))
            return 0
        if config is not None:
            _write_materialized_json(
                paper_dir / "audit" / "v11_source_map_preparation_config.json",
                config,
            )
        _write_materialized_json(
            paper_dir / "audit" / "paper_statement_map.json",
            source_map,
        )
        print(paper_dir / "audit" / "paper_statement_map.json")
        return 0
    except SourceInventoryCandidateReissueError as exc:
        raise SystemExit(str(exc)) from exc


if __name__ == "__main__":
    raise SystemExit(main())
