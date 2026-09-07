#!/usr/bin/env python3
"""Reissue current source-to-reusable-declaration semantic-review records.

The reviewer, not this command, decides whether a reusable repository
declaration matches its selected paper-source bundle.  This command requires
an explicit judgment and reason for every new or semantically changed material
library declaration on the selected PaperInterface surface. Existing rows are
reused only when their exact source bundle and Lean-produced semantic-target
identities are unchanged. The command rebuilds bounded declaration and routing
metadata and writes the one canonical paper-local ledger.

It is intentionally parallel to the v11 source-to-Spec screening writer.  It
never turns a declaration name, docstring, dashboard gloss, or old hash into a
semantic verdict.
"""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import semantic_review_decision_queue as review_queue  # noqa: E402
from scripts.current_closeout.review_surface import (  # noqa: E402
    load_current_v11_review_graph_projection,
)
from scripts.obligation_routes import (  # noqa: E402
    EvidenceRouteSet,
    ObligationRouteError,
)
from scripts.semantic_prerequisite_projection import (  # noqa: E402
    LIBRARY_SEMANTIC_TARGET_PROTOCOL,
    REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,
    selected_library_semantic_prerequisite_targets,
)
from scripts.corrected_target_identity import (  # noqa: E402
    APPROVED_CORRECTED_TARGET_MATCH,
    current_approved_corrected_target_metadata,
    source_requires_approved_corrected_target,
)


LEDGER_RELATIVE = Path("audit") / "library_semantic_review.json"
PROMPT_VERSION = REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION
TARGET_PROTOCOL = LIBRARY_SEMANTIC_TARGET_PROTOCOL
VALID_VERDICTS = frozenset(
    {"matches", APPROVED_CORRECTED_TARGET_MATCH, "mismatch", "uncertain"}
)


class LibraryReviewReissueError(ValueError):
    """Raised when a library-review reissue cannot be checked mechanically."""


def _load_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise LibraryReviewReissueError(f"could not read {label}: {exc}") from exc
    if not isinstance(payload, dict):
        raise LibraryReviewReissueError(f"{label} must be a JSON object")
    return payload


def _decisions(path: Path, *, paper: str) -> dict[str, dict[str, Any]]:
    payload = _load_object(path, label="decision file")
    try:
        return review_queue.normalized_decisions(
            payload,
            paper=paper,
            valid_verdicts=VALID_VERDICTS,
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise LibraryReviewReissueError(str(exc)) from exc


def decision_template(
    source_map: Mapping[str, Any],
    semantic_targets: Mapping[str, Mapping[str, Any]],
    paper_prerequisite_targets: Mapping[str, Mapping[str, Any]],
    library_targets: Mapping[str, Mapping[str, Any]],
    *,
    paper: str,
) -> dict[str, Any]:
    """Return a dependency-routed, deliberately non-evidentiary work queue.

    Lean owns the complete paper/library dependency closure.  Typed source
    routes seed candidate source items at its roots, and those candidates are
    propagated only along Lean-emitted dependency edges.  This narrows what a
    reviewer must inspect without inferring a verdict from names or locations.
    """

    try:
        routes = EvidenceRouteSet.from_source_map(
            source_map
        )
    except ObligationRouteError as exc:
        raise LibraryReviewReissueError(
            "invalid typed source route surface: " + str(exc)
        ) from exc
    try:
        selected_targets = selected_library_semantic_prerequisite_targets(
            source_map,
            library_targets,
        )
    except ValueError as exc:
        raise LibraryReviewReissueError(str(exc)) from exc
    expected = set(selected_targets)
    result_by_spec = routes.result_route_by_specification()
    missing_specs = sorted(set(result_by_spec) - set(semantic_targets))
    if missing_specs:
        raise LibraryReviewReissueError(
            "staged Lean cache lacks typed result Specs: "
            + ", ".join(missing_specs[:4])
        )

    raw_explicit_sources = source_map.get(
        "library_semantic_prerequisite_sources", {}
    )
    if not isinstance(raw_explicit_sources, Mapping) or not all(
        isinstance(declaration, str)
        and declaration.strip()
        and isinstance(source_item, str)
        and source_item.strip()
        for declaration, source_item in raw_explicit_sources.items()
    ):
        raise LibraryReviewReissueError(
            "library_semantic_prerequisite_sources must map nonempty Lean "
            "declaration names to nonempty source-item ids"
        )
    explicit_sources = {
        str(declaration).strip(): str(source_item).strip()
        for declaration, source_item in raw_explicit_sources.items()
    }
    unknown_explicit_declarations = sorted(set(explicit_sources) - expected)
    if unknown_explicit_declarations:
        raise LibraryReviewReissueError(
            "library_semantic_prerequisite_sources names absent Lean-selected "
            "material declarations: " + ", ".join(unknown_explicit_declarations)
        )
    raw_source_items = source_map.get("items")
    source_items = raw_source_items if isinstance(raw_source_items, Mapping) else {}
    unknown_explicit_source_items = sorted(
        set(explicit_sources.values()) - set(source_items)
    )
    if unknown_explicit_source_items:
        raise LibraryReviewReissueError(
            "library_semantic_prerequisite_sources names absent source items: "
            + ", ".join(unknown_explicit_source_items)
        )

    if source_map.get("semantic_route_schema") == 2:
        # The explicit typed map is the sole source-semantic frontier. The
        # Lean graph still retains every recursive reusable dependency for
        # proof, axiom, and import checks, but a proof helper with no source
        # statement must not acquire a made-up LLM comparison row.
        return {
            "schema": 1,
            "paper": paper,
            "comment": (
                "Non-evidence review work queue. Each row is one explicitly "
                "source-mapped reusable semantic root from the Lean-owned "
                "dependency graph. Recursive proof-only reusable dependencies "
                "remain graph-checked support and are not source-review rows."
            ),
            "unrouted_declarations": [],
            "items": {
                name: {
                    "source_item": explicit_sources[name],
                    "candidate_source_items": [explicit_sources[name]],
                    "judgment": "",
                    "reason": "",
                }
                for name in sorted(expected)
            },
        }

    owners: dict[str, set[str]] = defaultdict(set)
    pending_library: deque[tuple[str, str]] = deque()

    def library_owner(raw: object) -> str:
        name = str(raw or "").strip()
        # Current graph edges already name the Lean-selected review owner.
        # Re-normalizing them through a Python declaration table creates a
        # second, potentially stale semantic owner authority.
        return name

    def seed_library(raw: object, source_item: str) -> None:
        name = library_owner(raw)
        if not name:
            return
        if name not in expected:
            raise LibraryReviewReissueError(
                "staged library surface omits Lean-routed declaration: " + name
            )
        # Lean owns whether this declaration is material and all recursive
        # dependencies.  A source map may nevertheless select the one source
        # model/result that semantically introduces a reused library concept;
        # a downstream theorem conclusion is often only a structural route.
        pending_library.append((name, explicit_sources.get(name, source_item)))

    paper_owners: dict[str, set[str]] = defaultdict(set)
    pending_paper: deque[tuple[str, str]] = deque()

    for specification, route in result_by_spec.items():
        target = semantic_targets.get(specification)
        if not isinstance(target, Mapping):
            continue
        for name in target.get("library_declarations", ()):
            seed_library(name, route.source_item_id)
        for raw_name in target.get("prerequisite_declarations", ()):
            name = str(raw_name or "").strip()
            if name:
                pending_paper.append((name, route.source_item_id))

    for route in routes.routes:
        for declaration in route.semantic_declarations:
            if declaration in expected:
                seed_library(declaration, route.source_item_id)
            elif declaration:
                pending_paper.append((declaration, route.source_item_id))

    while pending_paper:
        declaration, source_item = pending_paper.popleft()
        if source_item in paper_owners[declaration]:
            continue
        paper_owners[declaration].add(source_item)
        target = paper_prerequisite_targets.get(declaration)
        if not isinstance(target, Mapping):
            continue
        for name in target.get("direct_library_declarations", ()):
            seed_library(name, source_item)
        for raw_child in target.get("direct_paper_declarations", ()):
            child = str(raw_child or "").strip()
            if child in paper_prerequisite_targets:
                pending_paper.append((child, source_item))

    while pending_library:
        declaration, source_item = pending_library.popleft()
        if source_item in owners[declaration]:
            continue
        owners[declaration].add(source_item)
        target = library_targets.get(declaration)
        if not isinstance(target, Mapping):
            continue
        for child in target.get("direct_library_declarations", ()):
            seed_library(child, source_item)

    items: dict[str, Any] = {}
    for name in sorted(expected):
        candidates = sorted(owners.get(name, ()))
        items[name] = {
            "source_item": candidates[0] if len(candidates) == 1 else "",
            "candidate_source_items": candidates,
            "judgment": "",
            "reason": "",
        }
    return {
        "schema": 1,
        "paper": paper,
        "comment": (
            "Non-evidence review work queue. Candidate source items follow only "
            "typed source routes and Lean-produced dependency edges, except that "
            "a source map may select one explicit canonical source connection for "
            "a material reusable declaration. The reviewer "
            "must inspect exact source bytes, the full Lean display, and exact "
            "bounded declaration code before filling every judgment and reason."
        ),
        "unrouted_declarations": sorted(expected - set(owners)),
        "items": items,
    }


def _template_output_path(paper_dir: Path, raw_path: Path) -> Path:
    try:
        return review_queue.template_output_path(
            paper_dir, raw_path, repository_root=ROOT
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise LibraryReviewReissueError(str(exc)) from exc


def _content_addressed_queue_path(
    paper_dir: Path, payload: Mapping[str, Any]
) -> Path:
    try:
        return review_queue.content_addressed_queue_path(
            paper_dir,
            payload,
            filename_prefix="library_semantic_reissue_decisions_",
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise LibraryReviewReissueError(str(exc)) from exc


def _merged_ledger(
    existing: Mapping[str, Any], decisions: Mapping[str, Mapping[str, Any]]
) -> dict[str, Any]:
    raw_existing = existing.get("items")
    existing_items = raw_existing if isinstance(raw_existing, Mapping) else {}
    merged: dict[str, Any] = {
        str(name): dict(row)
        for name, row in existing_items.items()
        if str(name).strip() and isinstance(row, Mapping)
    }
    for name, decision in decisions.items():
        prior = existing_items.get(name)
        row = dict(prior) if isinstance(prior, Mapping) else {}
        for field in (
            "source_item",
            "source_location",
            "source_anchor_evidence",
            "semantic_context_requirements",
            "library_source_path",
            "library_line_start",
            "library_line_end",
            "label",
        ):
            if field in decision:
                row[field] = decision[field]
        # An explicit direct anchor is a selected replacement for a prior
        # source-map bundle, not supplemental metadata on that broader route.
        if "source_anchor_evidence" in decision and "source_item" not in decision:
            row.pop("source_item", None)
        row["library_declaration"] = name
        merged[name] = row
    return merged


def _unchanged_semantic_judgment(
    prior: object, entry: Mapping[str, Any]
) -> dict[str, str] | None:
    """Return reusable reviewer metadata for one exact semantic identity.

    Navigation coordinates and bounded declaration bytes may be refreshed
    mechanically. Reviewer authority is reusable only when the byte-pinned
    paper source bundle and Lean-produced semantic target are identical.
    """

    return review_queue.reusable_semantic_judgment(
        prior,
        entry,
        target_protocol_field="library_semantic_target_protocol",
        target_protocol=TARGET_PROTOCOL,
        prior_code_sha256_field="library_definition_sha256",
        current_code_sha256_field="current_named_library_definition_sha256",
        prior_target_sha256_field="library_semantic_target_sha256",
        current_target_sha256_field="library_semantic_target_sha256",
    )


def _review_support(review_graph: Any, roots: set[str]) -> tuple[dict, dict]:
    """Transport the same Lean-owned context used for paper prerequisites."""

    return review_queue.review_support_from_targets(
        review_graph.target_material(), root_declarations=roots
    )


def _enrich_decision_template(
    payload: Mapping[str, Any],
    *,
    paper_dir: Path,
    source_map: Mapping[str, Any],
    entries: list[dict[str, Any]],
    review_graph: Any,
) -> dict[str, Any]:
    support, names_by_root = _review_support(review_graph, set(payload["items"]))
    return review_queue.enrich_queue(
        payload,
        paper_dir=paper_dir,
        source_map=source_map,
        material_by_name={str(entry["lean_name"]): entry for entry in entries},
        semantic_target_field="library_semantic_target",
        semantic_target_sha256_field="library_semantic_target_sha256",
        declaration_source_field="library_definition",
        declaration_source_sha256_field="library_definition_sha256",
        supporting_declarations=support,
        supporting_declaration_names_by_item=names_by_root,
    )


def current_changed_decision_template_and_path(
    paper_dir: Path,
    *,
    review_graph: Any,
) -> tuple[dict[str, Any], Path] | None:
    """Return the exact changed library queue and content-addressed path."""

    source_map = review_graph.context.statement_map
    semantic_targets = review_graph.semantic_targets
    paper_targets = review_graph.paper_prerequisite_targets
    library_targets = review_graph.library_semantic_targets
    payload = decision_template(
        source_map,
        semantic_targets,
        paper_targets,
        library_targets,
        paper=paper_dir.name,
    )
    current_path = paper_dir / LEDGER_RELATIVE
    current = (
        _load_object(current_path, label="current library ledger")
        if current_path.is_file()
        else {}
    )
    raw_existing = current.get("items")
    existing_items = raw_existing if isinstance(raw_existing, Mapping) else {}
    provisional_items: dict[str, Any] = {}
    for name, item in payload["items"].items():
        prior = existing_items.get(name)
        row = dict(prior) if isinstance(prior, Mapping) else dict(item)
        row["candidate_source_items"] = item.get("candidate_source_items", [])
        provisional_items[name] = row
    provisional = {
        "schema": 1,
        "paper": paper_dir.name,
        "prompt_version": PROMPT_VERSION,
        "target_protocol": TARGET_PROTOCOL,
        "items": provisional_items,
    }
    entries = list(
        review_graph.project_library_prerequisites(
            paper_dir,
            ledger=provisional,
        )
    )
    payload, entries = review_queue.changed_only_template_surface(
        payload,
        entries,
        existing_items,
        reusable_judgment=_unchanged_semantic_judgment,
    )
    if not payload["items"]:
        return None
    try:
        payload = _enrich_decision_template(
            payload,
            paper_dir=paper_dir,
            source_map=source_map,
            entries=entries,
            review_graph=review_graph,
        )
    except review_queue.SemanticReviewDecisionQueueError as exc:
        raise LibraryReviewReissueError(str(exc)) from exc
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
    current = _load_object(current_path, label="current library ledger")
    entries = review_graph.project_library_prerequisites(
        paper_dir,
        ledger=current,
    )
    if any(entry.get("semantic_current") is not True for entry in entries):
        return True
    # Semantic reuse may authorize an approved-context metadata rebind. The
    # terminal surface still needs the writer's current exact source bundle.
    refreshed = reissue(paper_dir, {}, validator="", review_graph=review_graph)
    return current.get("items") != refreshed.get("items")


def reissue(
    paper_dir: Path,
    decisions: Mapping[str, Mapping[str, Any]],
    *,
    validator: str,
    review_graph: Any,
    allow_retired_decisions: bool = False,
) -> dict[str, Any]:
    if decisions and not validator.strip():
        raise LibraryReviewReissueError("--validator must be nonempty")
    source_map = review_graph.context.statement_map
    try:
        specs = list(
            EvidenceRouteSet.from_source_map(
                source_map
            ).result_specifications()
        )
    except ObligationRouteError as exc:
        raise LibraryReviewReissueError(
            "invalid typed source route surface: " + str(exc)
        ) from exc
    if list(review_graph.specifications) != specs:
        raise LibraryReviewReissueError(
            "current v11 review transaction does not match the selected Spec surface"
        )
    current_path = paper_dir / LEDGER_RELATIVE
    current = (
        _load_object(current_path, label="current library ledger")
        if current_path.is_file()
        else {}
    )
    raw_existing = current.get("items")
    existing_items = raw_existing if isinstance(raw_existing, Mapping) else {}
    merged_decisions = _merged_ledger(current, decisions)
    template = decision_template(
        source_map,
        review_graph.semantic_targets,
        review_graph.paper_prerequisite_targets,
        review_graph.library_semantic_targets,
        paper=paper_dir.name,
    )
    provisional_items: dict[str, Any] = {}
    for name, item in template["items"].items():
        if name in decisions:
            row = dict(merged_decisions[name])
        else:
            prior = existing_items.get(name)
            row = dict(prior) if isinstance(prior, Mapping) else dict(item)
        row["candidate_source_items"] = item.get("candidate_source_items", [])
        provisional_items[name] = row
    entries = list(
        review_graph.project_library_prerequisites(
            paper_dir,
            ledger={
                "schema": 1,
                "paper": paper_dir.name,
                "prompt_version": PROMPT_VERSION,
                "target_protocol": TARGET_PROTOCOL,
                "items": provisional_items,
            },
        )
    )
    material_names = {str(entry.get("lean_name") or "").strip() for entry in entries}
    by_name = {str(entry.get("lean_name") or "").strip(): entry for entry in entries}
    bindings = review_queue.unique_reusable_judgment_bindings(
        by_name,
        existing_items,
        reusable_judgment=_unchanged_semantic_judgment,
    )
    missing = sorted(material_names - set(decisions) - set(bindings))
    extra = sorted(set(decisions) - material_names)
    if missing or (extra and not allow_retired_decisions):
        parts: list[str] = []
        if missing:
            parts.append(
                "missing decisions for new or semantically changed declarations: "
                + ", ".join(missing)
            )
        if extra:
            parts.append("decisions outside the material surface: " + ", ".join(extra))
        raise LibraryReviewReissueError("library decision coverage is not exact: " + "; ".join(parts))
    if extra:
        # See the paper-local analogue: a current typed route can explicitly
        # retire a former helper row without invalidating independently
        # reviewed rows whose byte-pinned source and Lean targets are unchanged.
        decisions = {name: decision for name, decision in decisions.items() if name in material_names}

    records: dict[str, Any] = {}
    current_support: tuple[dict, dict] | None = None
    for name in sorted(material_names):
        entry = by_name[name]
        decision = decisions.get(name)
        if not str(entry.get("library_definition") or "").strip():
            raise LibraryReviewReissueError(
                f"{name}: exact bounded library declaration is unavailable: "
                + str(entry.get("library_definition_error") or "")
            )
        if not str(entry.get("library_semantic_target") or "").strip():
            raise LibraryReviewReissueError(
                f"{name}: Lean semantic target is unavailable: "
                + str(entry.get("library_semantic_target_error") or "")
            )
        if not str(entry.get("verbatim_source_input") or "").strip():
            raise LibraryReviewReissueError(
                f"{name}: exact paper source connection is unavailable: "
                + str(entry.get("source_connection_error") or "")
            )
        if decision is not None:
            reviewer = {
                "judgment": str(decision["judgment"]),
                "reason": str(decision["reason"]),
                "validator": validator.strip(),
                "validator_type": "llm_as_judge",
                "validated_at": datetime.now(timezone.utc)
                .replace(microsecond=0)
                .isoformat(),
            }
            raw = provisional_items.get(name)
            if not isinstance(raw, Mapping):
                raise LibraryReviewReissueError(
                    f"{name}: current library review template has no source-routed entry"
                )
        else:
            prior_name, reviewer = bindings[name]
            raw = existing_items[prior_name]
        if decision is not None:
            try:
                if current_support is None:
                    current_support = _review_support(review_graph, set(decisions))
                support, names_by_root = current_support
                support_digest = review_queue.selected_supporting_declarations_sha256(
                    support, names_by_root[name]
                ) or ""
                review_queue.validate_current_identity(
                    name,
                    decision,
                    {**entry, "semantic_supporting_declarations_sha256": support_digest},
                    semantic_target_sha256_field="library_semantic_target_sha256",
                    declaration_source_sha256_field="library_definition_sha256",
                )
            except review_queue.SemanticReviewDecisionQueueError as exc:
                raise LibraryReviewReissueError(str(exc)) from exc
            source_item = str(entry.get("source_item") or "").strip()
            source_items = source_map.get("items")
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
                raise LibraryReviewReissueError(
                    f"{name}: corrected source route requires a "
                    "`matches_approved_corrected_target` judgment"
                )
            if (
                not requires_corrected_target
                and decision["judgment"] == APPROVED_CORRECTED_TARGET_MATCH
            ):
                raise LibraryReviewReissueError(
                    f"{name}: approved-corrected-target judgment has no corrected source route"
                )
            if requires_corrected_target:
                try:
                    corrected_metadata = current_approved_corrected_target_metadata(
                        source_record,
                        decision.get("_reviewed_approved_corrected_target"),
                    )
                except ValueError as exc:
                    raise LibraryReviewReissueError(f"{name}: {exc}") from exc
            else:
                corrected_metadata = {}
        else:
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
        label = str(entry.get("label") or "").strip()
        if label:
            record["label"] = label
        record.update(
            {
                "library_declaration": name,
                "library_source_path": entry["library_source_path"],
                "library_line_start": entry["library_line_start"],
                "library_line_end": entry["library_line_end"],
                "library_definition_sha256": entry["library_definition_sha256"],
                "library_semantic_target_sha256": entry[
                    "library_semantic_target_sha256"
                ],
                "elaborated_signature_sha256": entry[
                    "elaborated_signature_sha256"
                ],
                "library_semantic_target_protocol": TARGET_PROTOCOL,
                "source_input_bundle_sha256": entry["source_input_bundle_sha256"],
                "source_anchor_bundle_sha256": entry[
                    "source_anchor_bundle_sha256"
                ],
                **corrected_metadata,
                **reviewer,
            }
        )
        records[name] = record
    return {
        "schema": 1,
        "paper": paper_dir.name,
        "prompt_version": PROMPT_VERSION,
        "target_protocol": TARGET_PROTOCOL,
        "comment": (
            "Each verdict compares the byte-pinned paper-source bundle with Lean's "
            "current semantic target and exact bounded declaration code. These "
            "prerequisites are not additional paper-claim rows."
        ),
        "items": records,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--decisions", type=Path)
    mode.add_argument(
        "--emit-template",
        type=Path,
        help=(
            "write a blank non-evidence work queue from the current v11 review "
            "transaction; candidate source routes are structural navigation only"
        ),
    )
    mode.add_argument(
        "--refresh-current",
        action="store_true",
        help=(
            "refresh only derived routing and declaration-location metadata; "
            "refuse unless every exact source-to-library judgment is reusable"
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
            "with --emit-template, include only declarations whose exact source-bundle "
            "or Lean semantic identity cannot reuse the current ledger judgment"
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
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    paper_dir = args.root.resolve() / "papers" / args.paper
    if not args.v11_review_graph:
        raise LibraryReviewReissueError(
            "current semantic-review writing requires --v11-review-graph"
        )
    review_graph = load_current_v11_review_graph_projection(
        args.root.resolve(), paper_dir
    )
    if review_graph is None:
        raise LibraryReviewReissueError(
            "no exact-current v11 review graph; prepare the unified graph first"
        )
    if args.emit_template is not None:
        if args.write or args.validator.strip():
            raise LibraryReviewReissueError(
                "--emit-template cannot be combined with --write or --validator"
            )
        source_map = review_graph.context.statement_map
        semantic_targets = review_graph.semantic_targets
        paper_targets = review_graph.paper_prerequisite_targets
        library_targets = review_graph.library_semantic_targets
        payload = decision_template(
            source_map,
            semantic_targets,
            paper_targets,
            library_targets,
            paper=args.paper,
        )
        existing_items: Mapping[str, Any] = {}
        provisional_items = payload["items"]
        if args.changed_only:
            current_path = paper_dir / LEDGER_RELATIVE
            current = (
                _load_object(current_path, label="current library ledger")
                if current_path.is_file()
                else {}
            )
            raw_existing = current.get("items")
            existing_items = raw_existing if isinstance(raw_existing, Mapping) else {}
            provisional_items = {}
            for name, item in payload["items"].items():
                prior = existing_items.get(name)
                row = dict(prior) if isinstance(prior, Mapping) else dict(item)
                row["candidate_source_items"] = item.get("candidate_source_items", [])
                provisional_items[name] = row
        provisional = {
            "schema": 1,
            "paper": args.paper,
            "prompt_version": PROMPT_VERSION,
            "target_protocol": TARGET_PROTOCOL,
            "items": provisional_items,
        }
        entries = list(
            review_graph.project_library_prerequisites(
                paper_dir,
                ledger=provisional,
            )
        )
        if args.changed_only:
            payload, entries = review_queue.changed_only_template_surface(
                payload,
                entries,
                existing_items,
                reusable_judgment=_unchanged_semantic_judgment,
            )
            if not payload["items"]:
                print(
                    f"{args.paper}: no new or semantically changed library "
                    "declarations need reviewer decisions"
                )
                return 0
        try:
            payload = _enrich_decision_template(
                payload,
                paper_dir=paper_dir,
                source_map=source_map,
                entries=entries,
                review_graph=review_graph,
            )
        except review_queue.SemanticReviewDecisionQueueError as exc:
            raise LibraryReviewReissueError(str(exc)) from exc
        path = _template_output_path(paper_dir, args.emit_template)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        print(
            f"{args.paper}: wrote non-evidence library decision template {path} "
            f"({len(payload['items'])} rows; "
            f"{len(payload['unrouted_declarations'])} unrouted)"
        )
        return 0
    if args.refresh_current:
        if args.validator.strip() or args.changed_only:
            raise LibraryReviewReissueError(
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
        raise LibraryReviewReissueError("--decisions requires --validator")
    if args.changed_only:
        raise LibraryReviewReissueError("--changed-only is valid only with --emit-template")
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
        print(f"{args.paper}: validated {len(decisions)} library decisions; rerun with --write")
        return 0
    path = paper_dir / LEDGER_RELATIVE
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        f"{args.paper}: wrote {path} "
        f"({len(payload['items'])} active library decisions)"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except LibraryReviewReissueError as exc:
        print(f"library semantic reissue refused: {exc}", file=sys.stderr)
        raise SystemExit(1)
