#!/usr/bin/env python3
"""Reissue source reviews for paper-local semantic prerequisites.

Lean identifies these structures/inductives only after expanding a source
claim's transparent paper-local definitions.  This command never decides the
source match.  It rebuilds exact Lean declaration and byte-pinned source
digests around an explicit reviewer decision, then writes the one canonical
ledger used by the packet and closeout gate.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Mapping
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import semantic_review_decision_queue as review_queue
from scripts.current_closeout.review_surface import (
    load_current_v11_review_graph_projection,
)
from scripts.semantic_prerequisite_projection import (
    PAPER_PREREQUISITE_PROMPT_VERSION,
    PAPER_PREREQUISITE_SCHEMA,
    PAPER_PREREQUISITE_TARGET_PROTOCOL,
    empty_paper_semantic_prerequisite_ledger,
    selected_paper_semantic_prerequisite_targets,
)
from scripts.corrected_target_identity import (
    APPROVED_CORRECTED_TARGET_MATCH,
    current_approved_corrected_target_metadata,
    source_requires_approved_corrected_target,
)

LEDGER_RELATIVE = Path("audit") / "paper_semantic_prerequisites.json"
VALID_VERDICTS = frozenset(
    {"matches", APPROVED_CORRECTED_TARGET_MATCH, "mismatch", "uncertain"}
)


class PaperPrerequisiteReissueError(ValueError):
    """Raised when a paper-prerequisite review cannot be validated."""


def _load(path: Path, *, label: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise PaperPrerequisiteReissueError(f"could not read {label}: {exc}") from exc
    if not isinstance(payload, dict):
        raise PaperPrerequisiteReissueError(f"{label} must be a JSON object")
    return payload


def _decisions(path: Path, *, paper: str) -> dict[str, dict[str, Any]]:
    payload = _load(path, label="decision file")
    try:
        return review_queue.normalized_decisions(
            payload,
            paper=paper,
            valid_verdicts=VALID_VERDICTS,
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise PaperPrerequisiteReissueError(str(exc)) from exc


def _merged_items(
    existing: Mapping[str, Any], decisions: Mapping[str, Mapping[str, Any]]
) -> dict[str, dict[str, Any]]:
    prior_items = existing.get("items") if isinstance(existing, Mapping) else {}
    prior_items = prior_items if isinstance(prior_items, Mapping) else {}
    merged: dict[str, dict[str, Any]] = {
        str(name): dict(row)
        for name, row in prior_items.items()
        if str(name).strip() and isinstance(row, Mapping)
    }
    for name, decision in decisions.items():
        prior = prior_items.get(name)
        row = dict(prior) if isinstance(prior, Mapping) else {}
        for field in (
            "source_item",
            "source_location",
            "source_anchor_evidence",
            "semantic_context_requirements",
        ):
            if field in decision:
                row[field] = decision[field]
        # A deliberate direct source anchor replaces an older broad
        # source-map connection.  Retaining that key would silently make the
        # packet and digest use the old bundle instead of the reviewer-selected
        # anchor.
        if "source_anchor_evidence" in decision and "source_item" not in decision:
            row.pop("source_item", None)
        merged[name] = row
    return merged


def _unchanged_semantic_judgment(
    prior: object, entry: Mapping[str, Any]
) -> dict[str, str] | None:
    """Reuse only a verdict whose source-facing semantic identities are unchanged.

    The Lean-owned supporting-declaration bundle is reviewer context, not a
    second source claim.  Its presentation may legitimately change when the
    dependency graph or packet is improved; source-to-Lean judgment identity is
    instead the exact source bundle, semantic target, and declaration identity.
    """

    return review_queue.reusable_semantic_judgment(
        prior,
        entry,
        target_protocol_field="paper_semantic_target_protocol",
        target_protocol=PAPER_PREREQUISITE_TARGET_PROTOCOL,
        prior_code_sha256_field="paper_declaration_sha256",
        current_code_sha256_field="paper_declaration_sha256",
        prior_target_sha256_field="paper_semantic_target_sha256",
        current_target_sha256_field="paper_semantic_target_sha256",
    )


def _support_material(
    review_graph: Any,
    roots: set[str],
) -> tuple[
    dict[str, dict[str, Any]],
    dict[str, tuple[str, ...]],
    dict[str, str],
]:
    """Return Lean-owned transitive reviewer support for paper prerequisites."""

    try:
        support_projection = getattr(
            review_graph,
            "paper_prerequisite_review_support",
            None,
        )
        if callable(support_projection):
            return support_projection(roots)
        material = (
            review_graph.target_material()
            if callable(getattr(review_graph, "target_material", None))
            else {
                "semantic_targets": getattr(
                    review_graph,
                    "semantic_targets",
                    {},
                ),
                "paper_prerequisite_targets": review_graph.paper_prerequisite_targets,
                "library_semantic_targets": getattr(
                    review_graph,
                    "library_semantic_targets",
                    {},
                ),
                "paper_declaration_sources": getattr(
                    review_graph,
                    "paper_declaration_sources",
                    {},
                ),
                "library_declaration_sources": getattr(
                    review_graph,
                    "library_declaration_sources",
                    {},
                ),
                "library_semantic_target_errors": getattr(
                    review_graph,
                    "library_semantic_target_errors",
                    {},
                ),
            }
        )
        support, names_by_root = review_queue.review_support_from_targets(
            material,
            root_declarations=roots,
        )
        digests = (
            {
                root: (
                    review_queue.selected_supporting_declarations_sha256(
                        support,
                        names,
                    )
                    or ""
                )
                for root, names in names_by_root.items()
            }
            if support
            else {root: "" for root in names_by_root}
        )
        return support, names_by_root, digests
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise PaperPrerequisiteReissueError(str(exc)) from exc


def _entries_with_support(
    entries: list[dict[str, Any]],
    digests: Mapping[str, str],
) -> list[dict[str, Any]]:
    """Attach each row's exact transitive reviewer-support identity."""

    return [
        {
            **entry,
            "semantic_supporting_declarations_sha256": str(
                digests.get(str(entry.get("lean_name") or "").strip()) or ""
            ),
        }
        for entry in entries
    ]


def _current_projection_row(
    current_template: Mapping[str, Any],
    prior: object,
) -> dict[str, Any]:
    """Project a row through today's typed source routes.

    A prior ledger is evidence about an earlier source/Lean identity; it is not
    authority for the current source selection.  Preserve its reviewer fields,
    but select the source from the current template.  For a genuinely
    multi-candidate current route, the prior selection remains a useful routing
    choice only while it is still one of today's candidates.
    """

    row = dict(prior) if isinstance(prior, Mapping) else dict(current_template)
    candidates = [
        str(source_item).strip()
        for source_item in current_template.get("candidate_source_items", [])
        if str(source_item).strip()
    ]
    row["candidate_source_items"] = candidates
    current_source_item = str(current_template.get("source_item") or "").strip()
    prior_source_item = str(row.get("source_item") or "").strip()
    if current_source_item:
        row["source_item"] = current_source_item
        row.pop("source_anchor_evidence", None)
    elif prior_source_item in candidates:
        row["source_item"] = prior_source_item
    elif candidates:
        row["source_item"] = ""
        row.pop("source_anchor_evidence", None)
    elif "source_anchor_evidence" not in row:
        row["source_item"] = ""
    return row
def _approved_corrected_target_metadata(
    *,
    name: str,
    decision: Mapping[str, Any],
    source_map: Mapping[str, Any],
) -> dict[str, str]:
    """Validate the only non-raw accepted prerequisite disposition.

    The reviewer must have received the frozen approved correction worksheet;
    issuance then rechecks that worksheet against the current map row.  This
    never turns a user approval into a raw-source `matches` judgment.
    """

    source_item = str(decision.get("source_item") or "").strip()
    raw_items = source_map.get("items")
    source_record = (
        raw_items.get(source_item) if isinstance(raw_items, Mapping) else None
    )
    try:
        return current_approved_corrected_target_metadata(
            source_record,
            decision.get("_reviewed_approved_corrected_target"),
        )
    except ValueError as exc:
        raise PaperPrerequisiteReissueError(f"{name}: {exc}") from exc


def current_changed_decision_template_and_path(
    paper_dir: Path,
    *,
    review_graph: Any,
) -> tuple[dict[str, Any], Path] | None:
    """Return the exact changed-row queue and its content-addressed path.

    This is the shared planner/CLI projection for a graph refresh.  Existing
    judgments survive only through their exact source-bundle and elaborated
    semantic identities; a new or changed row remains blank reviewer work.
    ``None`` means that every current graph row is already reusable.
    """

    if not review_graph.paper_prerequisite_targets:
        return None
    source_map = review_graph.context.statement_map
    semantic_targets = review_graph.semantic_targets
    prerequisite_targets = review_graph.paper_prerequisite_targets
    payload = decision_template(
        source_map,
        semantic_targets,
        prerequisite_targets,
        paper=paper_dir.name,
    )
    current_path = paper_dir / LEDGER_RELATIVE
    current = (
        _load(current_path, label="current prerequisite ledger")
        if current_path.is_file()
        else {}
    )
    raw_existing = current.get("items")
    existing_items = (
        raw_existing if isinstance(raw_existing, Mapping) else {}
    )
    provisional_items: dict[str, Any] = {}
    for name, item in payload["items"].items():
        prior = existing_items.get(name)
        provisional_items[name] = _current_projection_row(item, prior)
    provisional = {
        "schema": PAPER_PREREQUISITE_SCHEMA,
        "paper": paper_dir.name,
        "prompt_version": PAPER_PREREQUISITE_PROMPT_VERSION,
        "target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
        "items": provisional_items,
    }
    entries = list(
        review_graph.project_paper_prerequisites(
            paper_dir,
            ledger=provisional,
        )
    )
    _support, _names_by_root, support_digests = _support_material(
        review_graph,
        set(payload["items"]),
    )
    entries = _entries_with_support(entries, support_digests)
    payload, entries = review_queue.changed_only_template_surface(
        payload,
        entries,
        existing_items,
        reusable_judgment=_unchanged_semantic_judgment,
    )
    if not payload["items"]:
        return None
    support, names_by_root, support_digests = _support_material(
        review_graph,
        set(payload["items"]),
    )
    entries = _entries_with_support(entries, support_digests)
    try:
        payload = review_queue.enrich_queue(
            payload,
            paper_dir=paper_dir,
            source_map=source_map,
            material_by_name={str(entry["lean_name"]): entry for entry in entries},
            semantic_target_field="paper_semantic_target",
            semantic_target_sha256_field="paper_semantic_target_sha256",
            declaration_source_field="paper_declaration_source",
            declaration_source_sha256_field="paper_declaration_sha256",
            supporting_declarations=(support or None),
            supporting_declaration_names_by_item=(
                names_by_root if support else None
            ),
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise PaperPrerequisiteReissueError(str(exc)) from exc
    return payload, _content_addressed_queue_path(paper_dir, payload)


def current_structural_refresh_required(
    paper_dir: Path,
    *,
    review_graph: Any,
) -> bool:
    """Report stale routing metadata after every judgment semantically reuses."""

    current_path = paper_dir / LEDGER_RELATIVE
    if not current_path.is_file():
        return False
    current = _load(current_path, label="current prerequisite ledger")
    entries = review_graph.project_paper_prerequisites(
        paper_dir,
        ledger=current,
    )
    if any(entry.get("semantic_current") is not True for entry in entries):
        return True
    # An approved-context rebind can preserve a judgment while changing the
    # full source-bundle identity required by terminal acceptance. Use the
    # writer's own pure projection so the planner schedules that metadata
    # refresh without creating reviewer work or duplicating acceptance rules.
    refreshed = reissue(paper_dir, {}, validator="", review_graph=review_graph)
    return current.get("items") != refreshed.get("items")


def decision_template(
    source_map: Mapping[str, Any],
    semantic_targets: Mapping[str, Mapping[str, Any]],
    prerequisite_targets: Mapping[str, Mapping[str, Any]],
    *,
    paper: str,
) -> dict[str, Any]:
    """Return a dependency-routed, deliberately non-evidentiary work queue.

    Lean owns the declaration roots and their paper-local dependency edges.
    The typed source map owns the result/source-role routes. Combining those
    two structural inputs can narrow the source items a reviewer should inspect,
    but it cannot decide whether any source text and Lean declaration match.
    Every emitted judgment and reason is therefore blank.
    """

    _ = semantic_targets
    try:
        selected_targets = selected_paper_semantic_prerequisite_targets(
            source_map,
            prerequisite_targets,
        )
    except ValueError as exc:
        raise PaperPrerequisiteReissueError(str(exc)) from exc
    raw_explicit_sources = source_map.get("paper_semantic_prerequisite_sources", {})
    explicit_sources = {
        str(declaration).strip(): str(source_item).strip()
        for declaration, source_item in raw_explicit_sources.items()
    }

    items: dict[str, Any] = {}
    for name in sorted(selected_targets):
        source_item = explicit_sources.get(name, "")
        items[name] = {
            "source_item": source_item,
            "candidate_source_items": [source_item] if source_item else [],
            "judgment": "",
            "reason": "",
        }
    return {
        "schema": 1,
        "paper": paper,
        "comment": (
            "Non-evidence review work queue. The typed source map selects only "
            "current source-model and source-formula boundaries from Lean's full "
            "paper-local dependency closure. Internal Lean helpers remain proof "
            "support and are not standalone source-review rows. "
            "The reviewer must inspect exact source bytes and the full Lean display, "
            "select the source connection, and fill every judgment and reason."
        ),
        "unrouted_declarations": [],
        "items": items,
    }


def _template_output_path(paper_dir: Path, raw_path: Path) -> Path:
    try:
        return review_queue.template_output_path(
            paper_dir, raw_path, repository_root=ROOT
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise PaperPrerequisiteReissueError(str(exc)) from exc


def _content_addressed_queue_path(
    paper_dir: Path, payload: Mapping[str, Any]
) -> Path:
    try:
        return review_queue.content_addressed_queue_path(
            paper_dir,
            payload,
            filename_prefix="paper_semantic_prerequisite_reissue_decisions_",
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise PaperPrerequisiteReissueError(str(exc)) from exc


def reissue(
    paper_dir: Path,
    decisions: Mapping[str, Mapping[str, Any]],
    *,
    validator: str,
    review_graph: Any,
    allow_retired_decisions: bool = False,
) -> dict[str, Any]:
    if decisions and not validator.strip():
        raise PaperPrerequisiteReissueError("--validator must be nonempty")
    if not review_graph.paper_prerequisite_targets:
        if decisions:
            raise PaperPrerequisiteReissueError(
                "decisions outside the empty paper-prerequisite surface: "
                + ", ".join(sorted(decisions))
            )
        return empty_paper_semantic_prerequisite_ledger(paper_dir.name)
    current_path = paper_dir / LEDGER_RELATIVE
    existing = (
        _load(current_path, label="current prerequisite ledger")
        if current_path.is_file()
        else {}
    )
    raw_existing = existing.get("items")
    existing_items = raw_existing if isinstance(raw_existing, Mapping) else {}
    merged_decisions = _merged_items(existing, decisions)
    template = decision_template(
        review_graph.context.statement_map,
        review_graph.semantic_targets,
        review_graph.paper_prerequisite_targets,
        paper=paper_dir.name,
    )
    provisional_items: dict[str, Any] = {}
    for name, item in template["items"].items():
        if name in decisions:
            prior = merged_decisions[name]
        else:
            prior = existing_items.get(name)
        provisional_items[name] = _current_projection_row(item, prior)
    provisional = {
        "schema": PAPER_PREREQUISITE_SCHEMA,
        "paper": paper_dir.name,
        "prompt_version": PAPER_PREREQUISITE_PROMPT_VERSION,
        "target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
        "items": provisional_items,
    }
    entries = list(
        review_graph.project_paper_prerequisites(
            paper_dir,
            ledger=provisional,
        )
    )
    _support, _names_by_root, support_digests = _support_material(
        review_graph,
        set(template["items"]),
    )
    entries = _entries_with_support(entries, support_digests)
    expected = {str(entry.get("lean_name") or "").strip() for entry in entries}
    extra = sorted(set(decisions) - expected)
    if extra and not allow_retired_decisions:
        raise PaperPrerequisiteReissueError(
            "decisions outside the prerequisite surface: " + ", ".join(extra)
        )
    if extra:
        # A source-map repair may deliberately retire an implementation helper
        # from the semantic-review surface.  The writer still validates every
        # retained decision against its exact current source and Lean target;
        # this switch merely prevents a prior, broader non-evidence queue from
        # forcing the reviewer to repeat those unchanged retained rows.
        decisions = {name: decision for name, decision in decisions.items() if name in expected}
    entries_by_name = {
        str(entry.get("lean_name") or "").strip(): entry
        for entry in entries
        if str(entry.get("lean_name") or "").strip()
    }
    bindings = review_queue.unique_reusable_judgment_bindings(
        entries_by_name,
        existing_items,
        reusable_judgment=_unchanged_semantic_judgment,
    )
    missing = sorted(expected - set(decisions) - set(bindings))
    if missing:
        raise PaperPrerequisiteReissueError(
            "changed or missing semantic identity requires explicit reviewer "
            "decisions for: " + ", ".join(missing)
        )
    records: dict[str, Any] = {}
    for entry in entries:
        name = str(entry["lean_name"])
        decision = decisions.get(name)
        if not str(entry.get("paper_declaration_source") or "").strip():
            raise PaperPrerequisiteReissueError(f"{name}: exact Lean declaration is unavailable")
        if not str(entry.get("paper_semantic_target") or "").strip():
            raise PaperPrerequisiteReissueError(
                f"{name}: Lean paper-prerequisite semantic target is unavailable: "
                + str(entry.get("paper_semantic_target_error") or "")
            )
        if not str(entry.get("verbatim_source_input") or "").strip():
            raise PaperPrerequisiteReissueError(
                f"{name}: exact paper source connection is unavailable: "
                + str(entry.get("source_connection_error") or "")
            )
        if decision is not None:
            try:
                review_queue.validate_current_identity(
                    name,
                    decision,
                    entry,
                    semantic_target_sha256_field="paper_semantic_target_sha256",
                    declaration_source_sha256_field="paper_declaration_sha256",
                )
            except review_queue.SemanticReviewDecisionQueueError as exc:
                raise PaperPrerequisiteReissueError(str(exc)) from exc
            source_item = str(entry.get("source_item") or "").strip()
            source_items = review_graph.context.statement_map.get("items")
            source_record = (
                source_items.get(source_item)
                if isinstance(source_items, Mapping)
                else None
            )
            requires_corrected_target = source_requires_approved_corrected_target(
                source_record
            )
            if (
                requires_corrected_target
                and decision["judgment"] != APPROVED_CORRECTED_TARGET_MATCH
            ):
                raise PaperPrerequisiteReissueError(
                    f"{name}: corrected source route requires a "
                    "`matches_approved_corrected_target` judgment"
                )
            if (
                not requires_corrected_target
                and decision["judgment"] == APPROVED_CORRECTED_TARGET_MATCH
            ):
                raise PaperPrerequisiteReissueError(
                    f"{name}: approved-corrected-target judgment has no corrected source route"
                )
            corrected_metadata = (
                _approved_corrected_target_metadata(
                    name=name,
                    decision=decision,
                    source_map=review_graph.context.statement_map,
                )
                if decision["judgment"] == APPROVED_CORRECTED_TARGET_MATCH
                else {}
            )
            reviewer = {
                "judgment": decision["judgment"],
                "reason": decision["reason"],
                "validator": validator.strip(),
                "validator_type": "llm_as_judge",
                "validated_at": datetime.now(timezone.utc)
                .replace(microsecond=0)
                .isoformat(),
            }
            raw = provisional_items[name]
        else:
            prior_name, reviewer = bindings[name]
            raw = existing_items[prior_name]
            corrected_metadata = (
                {
                    "corrected_target_protocol": str(
                        raw.get("corrected_target_protocol") or ""
                    ).strip(),
                    "corrected_target_review_sha256": str(
                        raw.get("corrected_target_review_sha256") or ""
                    ).strip().lower(),
                }
                if reviewer.get("judgment") == APPROVED_CORRECTED_TARGET_MATCH
                else {}
            )
        record: dict[str, Any] = {}
        current_source_item = str(entry.get("source_item") or "").strip()
        if current_source_item:
            record["source_item"] = current_source_item
        elif isinstance(raw.get("source_anchor_evidence"), list):
            record["source_anchor_evidence"] = raw["source_anchor_evidence"]
        source_location = str(entry.get("source_locator") or "").strip()
        if source_location:
            record["source_location"] = source_location
        if "semantic_context_requirements" in raw:
            record["semantic_context_requirements"] = raw[
                "semantic_context_requirements"
            ]
        record.update(
            {
                "paper_declaration": name,
                "paper_source_path": entry["paper_source_path"],
                "paper_line_start": entry["paper_line_start"],
                "paper_declaration_sha256": entry["paper_declaration_sha256"],
                "paper_semantic_target_sha256": entry[
                    "paper_semantic_target_sha256"
                ],
                "elaborated_signature_sha256": entry[
                    "elaborated_signature_sha256"
                ],
                "paper_semantic_target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
                "source_input_bundle_sha256": entry["source_input_bundle_sha256"],
                "source_anchor_bundle_sha256": entry[
                    "source_anchor_bundle_sha256"
                ],
                **corrected_metadata,
                **reviewer,
            }
        )
        support_digest = str(support_digests.get(name) or "").strip()
        if support_digest:
            record["semantic_supporting_declarations_sha256"] = support_digest
        records[name] = record
    return {
        "schema": PAPER_PREREQUISITE_SCHEMA,
        "paper": paper_dir.name,
        "prompt_version": PAPER_PREREQUISITE_PROMPT_VERSION,
        "target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
        "comment": (
            "Each verdict compares a Lean-owned own-body semantic target and exact "
            "paper-local declaration with its selected byte-pinned paper-source bundle. "
            "These are semantic prerequisites, not additional paper-claim rows."
        ),
        "items": records,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--decisions", type=Path)
    mode.add_argument(
        "--emit-template",
        type=Path,
        help=(
            "write a non-evidence decision work queue from the current staged "
            "Lean cache; candidate routes are structural hints and all verdicts stay blank"
        ),
    )
    mode.add_argument(
        "--refresh-current",
        action="store_true",
        help=(
            "refresh derived routing and source-location metadata only; refuse "
            "unless every semantic judgment is exactly reusable"
        ),
    )
    parser.add_argument("--validator", default="")
    parser.add_argument(
        "--v11-review-graph",
        action="store_true",
        help=(
            "use the exact current builder-issued v11 graph targets; this loads "
            "no dashboard cache and launches no Lean discovery"
        ),
    )
    parser.add_argument(
        "--changed-only",
        action="store_true",
        help=(
            "with --emit-template, include only declarations whose exact "
            "source-bundle or Lean semantic identity cannot reuse the current "
            "ledger judgment"
        ),
    )
    parser.add_argument(
        "--allow-retired-decisions",
        action="store_true",
        help=(
            "with --decisions, discard judgments for declarations explicitly "
            "retired from the current graph surface; retained rows must still "
            "pass exact source and Lean semantic-identity validation"
        ),
    )
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    paper_dir = args.root.resolve() / "papers" / args.paper
    if not args.v11_review_graph:
        parser.error(
            "current semantic-review writing requires --v11-review-graph"
        )
    review_graph = load_current_v11_review_graph_projection(
        args.root.resolve(), paper_dir
    )
    if review_graph is None:
        raise PaperPrerequisiteReissueError(
            "no exact-current v11 review graph; prepare the unified graph first"
        )
    if args.emit_template is not None:
        if args.write or args.validator.strip():
            parser.error("--emit-template cannot be combined with --write or --validator")
        source_map = review_graph.context.statement_map
        semantic_targets = review_graph.semantic_targets
        prerequisite_targets = review_graph.paper_prerequisite_targets
        payload = decision_template(
            source_map,
            semantic_targets,
            prerequisite_targets,
            paper=args.paper,
        )
        existing_items: Mapping[str, Any] = {}
        provisional_items = payload["items"]
        if args.changed_only:
            current_path = paper_dir / LEDGER_RELATIVE
            current = (
                _load(current_path, label="current prerequisite ledger")
                if current_path.is_file()
                else {}
            )
            raw_existing = current.get("items")
            existing_items = (
                raw_existing if isinstance(raw_existing, Mapping) else {}
            )
            provisional_items = {}
            for name, item in payload["items"].items():
                prior = existing_items.get(name)
                provisional_items[name] = _current_projection_row(item, prior)
        provisional = {
            "schema": PAPER_PREREQUISITE_SCHEMA,
            "paper": args.paper,
            "prompt_version": PAPER_PREREQUISITE_PROMPT_VERSION,
            "target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
            "items": provisional_items,
        }
        entries = list(
            review_graph.project_paper_prerequisites(
                paper_dir,
                ledger=provisional,
            )
        )
        support, names_by_root, support_digests = _support_material(
            review_graph,
            set(payload["items"]),
        )
        entries = _entries_with_support(entries, support_digests)
        if args.changed_only:
            payload, entries = review_queue.changed_only_template_surface(
                payload,
                entries,
                existing_items,
                reusable_judgment=_unchanged_semantic_judgment,
            )
            if not payload["items"]:
                print(
                    f"{args.paper}: no new or semantically changed paper-local "
                    "declarations need reviewer decisions"
                )
                return 0
            support, names_by_root, support_digests = _support_material(
                review_graph,
                set(payload["items"]),
            )
            entries = _entries_with_support(entries, support_digests)
        try:
            payload = review_queue.enrich_queue(
                payload,
                paper_dir=paper_dir,
                source_map=source_map,
                material_by_name={str(entry["lean_name"]): entry for entry in entries},
                semantic_target_field="paper_semantic_target",
                semantic_target_sha256_field="paper_semantic_target_sha256",
                declaration_source_field="paper_declaration_source",
                declaration_source_sha256_field="paper_declaration_sha256",
                supporting_declarations=(support or None),
                supporting_declaration_names_by_item=(
                    names_by_root if support else None
                ),
            )
        except review_queue.SemanticReviewDecisionQueueError as exc:
            raise PaperPrerequisiteReissueError(str(exc)) from exc
        path = _template_output_path(paper_dir, args.emit_template)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(
            f"{args.paper}: wrote non-evidence decision template {path} "
            f"({len(payload['items'])} rows; "
            f"{len(payload['unrouted_declarations'])} unrouted)"
        )
        return 0
    if args.refresh_current:
        if args.validator.strip() or args.changed_only:
            parser.error(
                "--refresh-current cannot be combined with --validator or --changed-only"
            )
        payload = reissue(
            paper_dir,
            {},
            validator="",
            review_graph=review_graph,
        )
        if not args.write:
            print(
                f"{args.paper}: validated structural refresh with all "
                f"{len(payload['items'])} semantic judgments reused; rerun with --write"
            )
            return 0
        path = paper_dir / LEDGER_RELATIVE
        path.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        print(
            f"{args.paper}: refreshed {path} with all "
            f"{len(payload['items'])} semantic judgments reused"
        )
        return 0
    if not args.validator.strip():
        parser.error("--decisions requires --validator")
    if args.changed_only:
        parser.error("--changed-only is valid only with --emit-template")
    assert args.decisions is not None
    decisions = _decisions(args.decisions, paper=args.paper)
    payload = reissue(
        paper_dir,
        decisions,
        validator=args.validator,
        review_graph=review_graph,
        allow_retired_decisions=args.allow_retired_decisions,
    )
    if not args.write:
        print(f"{args.paper}: validated {len(decisions)} paper-prerequisite decisions; rerun with --write")
        return 0
    path = paper_dir / LEDGER_RELATIVE
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        f"{args.paper}: wrote {path} "
        f"({len(payload['items'])} active reissued decisions)"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except PaperPrerequisiteReissueError as exc:
        print(f"paper-prerequisite reissue refused: {exc}", file=sys.stderr)
        raise SystemExit(1)
