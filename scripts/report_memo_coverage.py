#!/usr/bin/env python3
"""Document-only coverage checks for source-clarification explanations.

The assessment binds reader prose to one externally supplied, already-current
semantic-review identity.  It does not inspect Lean, issue review verdicts, or
grant graph authority.  It enumerates existing source records and permits an
explicit, explained non-material disposition for representation conventions
and historical items.  The template deliberately cannot pass until its
inventory and semantic-review identity are reviewed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path, PurePosixPath
from typing import Mapping
from urllib.parse import unquote, urlsplit

from scripts.final_validation_report_sections import (
    ResultTableRow,
    section_four_result_table,
)
from scripts.source_coverage_scope import (
    THEOREM_REALIZATION_SOURCE_KINDS,
    _current_canonical_text_source,
    source_coverage_mode_from_map,
    source_index_byte_pinned_anchor_item_ids,
    source_named_presentation_in_coverage_scope,
    source_presentation_aliases,
    source_prose_definition_replaced_named_presentation_spans,
)
from scripts.source_named_result_index import (
    NamedResultPresentation,
    SOURCE_PRESENTATION_RECONCILIATION_FIELD,
    named_result_presentations_sha256,
    reconcile_named_result_presentations,
    reviewed_source_presentation_inventory,
)

ROOT = Path(__file__).resolve().parents[1]
COVERAGE_PATH = Path("docs/REPORT_MEMO_COVERAGE.json")
REPORT_PATH = Path("FINAL_VALIDATION_REPORT.md")
# A metadata-only line contributes no reader text, including its newline.
# Stop at the first closing delimiter so an inline comment cannot consume
# intervening prose while searching for a later comment-only line.
_COMMENTS = re.compile(
    r"^[ \t]*<!--(?:(?!-->).)*-->[ \t]*(?:\r?\n|$)|<!--.*?-->",
    re.DOTALL | re.MULTILINE,
)
_TECHNICAL_SECTION = re.compile(r"^##\s+(?:1[2-9]|[2-9]\d)\.\s", re.MULTILINE)
_LINK = re.compile(r"\]\(\s*(?:<([^>]+)>|([^\s)]+))(?:\s+\"[^\"]*\")?\s*\)")
_DRAFT_LABEL = re.compile(
    r"\bCodex(?:[- ]authored)?[ \t]+[^\n.]{0,70}\b(?:draft|for review|addition)\b", re.IGNORECASE
)
_VISIBLE_GENERATOR = re.compile(
    r"(?:>{2,}[^\n]*generat|(?:BEGIN|END|START OF) GENERATED)", re.IGNORECASE
)
_PRIVATE_PROVENANCE = re.compile(
    r"repository (?:user|owner) (?:has (?:also )?)?approved|"
    r"(?:docs|audit)/[^\s)\]]*(?:APPROV|AUTHORITY|WORKING|HANDOFF)[^\s)\]]*",
    re.IGNORECASE,
)
_PRIVATE_MEMO_NAME = re.compile(
    r"(?:^|[/_.-])(?:approval|approved|authority|working|handoff|draft|formalization_plan)(?:[/_.-]|$)",
    re.IGNORECASE,
)
_APPROVAL_LABEL = re.compile(
    r"\b(?:author|formalizer|owner|maintainer|user)[ -]approved\b|"
    r"\b(?:author|formalizer|owner|maintainer|user)\s+(?:has\s+)?approved\b|"
    r"\bapproved\s+(?:(?:additional|corrected|clarified|formalized)\s+)?"
    r"(?:assumptions?|targets?|clarifications?|scope|readings?|additions?)\b|"
    r"\bapproval[- ](?:pinned|bound)\s+(?:corrected\s+)?targets?\b",
    re.IGNORECASE,
)
_ASSUMPTIONS_SECTION = re.compile(
    r"^##\s+6\.\s+Additional Assumptions Beyond Paper\s*\n(.*?)(?=^##\s|\Z)",
    re.MULTILINE | re.DOTALL,
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_SOURCE_INVENTORY_SCHEMA = 1
_RESULT_TABLE_SCHEMA = 1
_PRINTED_LABEL_BASES = frozenset(
    {"source_text_heading", "reviewed_rendered_source"}
)
_NUMBERING_KINDS = frozenset({"numbered", "unnumbered"})
_NONRESULT_SOURCE_STATUSES = frozenset(
    {"quarantined_source_defect", "support_only"}
)
_NONRESULT_INVENTORY_ROLES = frozenset(
    {"quarantined_source_defect", "proof_support"}
)
_NONRESULT_SCOPE_DISPOSITIONS = frozenset({"user_approved_scope_exclusion"})
_RESULT_KIND_LABELS = {
    "claim": "Claim",
    "corollary": "Corollary",
    "example": "Example",
    "lemma": "Lemma",
    "proposition": "Proposition",
    "runtime_claim": "Runtime Claim",
    "theorem": "Theorem",
}


def _presentation_kind_matches_source_kind(
    presentation_kind: str, source_kind: str
) -> bool:
    """Recognize a reviewed generic claim by its source-visible result kind."""

    return presentation_kind == source_kind or (
        presentation_kind == "claim"
        and source_kind in THEOREM_REALIZATION_SOURCE_KINDS
    )


def _source_item_is_nonresult_support(item: object) -> bool:
    if not isinstance(item, Mapping):
        return False
    return bool(
        str(item.get("inventory_role") or "").strip().lower()
        in _NONRESULT_INVENTORY_ROLES
        or str(item.get("source_status") or "").strip().lower()
        in _NONRESULT_SOURCE_STATUSES
        or str(item.get("scope_disposition") or "").strip().lower()
        in _NONRESULT_SCOPE_DISPOSITIONS
    )


def _selected_semantic_source_owner_ids(
    raw_items: Mapping[str, object],
) -> set[str]:
    """Return typed named-result owners selected by the semantic surface.

    Source discovery supplies presentation and printed-label evidence.  It
    cannot remove an already selected semantic-contract owner when OCR or
    extraction mangles that owner's visible heading.
    """

    return {
        str(item_id)
        for item_id, item in raw_items.items()
        if isinstance(item_id, str)
        and isinstance(item, Mapping)
        and str(item.get("source_kind") or "").strip().lower()
        in THEOREM_REALIZATION_SOURCE_KINDS
        and isinstance(item.get("semantic_contract"), Mapping)
        and item.get("source_presentation_alias") is None
        and not _source_item_is_nonresult_support(item)
    }


def _source_item_presentation_spans(
    item: object, *, source_path: str
) -> tuple[tuple[int, int], ...]:
    if not isinstance(item, Mapping):
        return ()
    spans: list[tuple[int, int]] = []
    anchors = item.get("source_anchor_evidence")
    if not isinstance(anchors, list):
        return ()
    expected_path = PurePosixPath(source_path).as_posix()
    for anchor in anchors:
        if not isinstance(anchor, Mapping):
            continue
        anchor_path = PurePosixPath(str(anchor.get("path") or "")).as_posix()
        line_start = anchor.get("line_start")
        line_end = anchor.get("line_end")
        if (
            anchor_path == expected_path
            and isinstance(line_start, int)
            and not isinstance(line_start, bool)
            and isinstance(line_end, int)
            and not isinstance(line_end, bool)
            and 1 <= line_start <= line_end
        ):
            spans.append((line_start, line_end))
    return tuple(spans)


def _canonical_source_item_for_presentation(
    presentation: NamedResultPresentation,
    canonical_ids: list[str],
    raw_items: Mapping[str, object],
) -> tuple[str, str]:
    """Choose the map carrier while retaining the source-visible result kind."""

    candidates = [
        item_id
        for item_id in canonical_ids
        if isinstance(raw_items.get(item_id), Mapping)
    ]
    if not candidates:
        raise ValueError(
            "selected named presentation has no canonical source item: "
            f"{presentation.kind} {presentation.label}"
        )

    def source_kind(item_id: str) -> str:
        item = raw_items[item_id]
        assert isinstance(item, Mapping)
        return str(item.get("source_kind") or "").strip().lower()

    exact = [item_id for item_id in candidates if source_kind(item_id) == presentation.kind]
    visibly_typed_claim = [
        item_id
        for item_id in candidates
        if presentation.kind == "claim"
        and source_kind(item_id) in THEOREM_REALIZATION_SOURCE_KINDS
    ]
    generic_claim_carriers = [
        item_id for item_id in candidates if source_kind(item_id) == "claim"
    ]
    claim_bearing = [
        item_id
        for item_id in candidates
        if isinstance(raw_items[item_id], Mapping)
        and raw_items[item_id].get("claim_bearing") is True
    ]
    selected_semantic_owners = _selected_semantic_source_owner_ids(raw_items)

    def semantic_first(items: list[str]) -> list[str]:
        selected = [item_id for item_id in items if item_id in selected_semantic_owners]
        return selected or items

    selected = semantic_first(
        exact
        or visibly_typed_claim
        or generic_claim_carriers
        or claim_bearing
        or candidates
    )[0]
    selected_kind = source_kind(selected)
    result_kind = (
        selected_kind
        if presentation.kind == "claim"
        and selected_kind in THEOREM_REALIZATION_SOURCE_KINDS
        else presentation.kind
    )
    return selected, result_kind


def _local_links(text: str) -> set[str]:
    links = set()
    for match in _LINK.finditer(text):
        target = urlsplit(match.group(1) or match.group(2))
        if not target.scheme and not target.netloc:
            links.add(PurePosixPath(unquote(target.path)).as_posix())
    return links


def _has_approval_label(text: str) -> bool:
    # Evidence identifiers and approval-voting terminology are not prose
    # endorsements. Comments do not appear in the rendered documents.
    return bool(_APPROVAL_LABEL.search(_COMMENTS.sub("", text)))


def _object(path: Path, *, optional: bool = False) -> dict:
    if optional and not path.exists():
        return {}

    def unique_fields(pairs: list[tuple[str, object]]) -> dict:
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON field: {key}")
            result[key] = value
        return result

    try:
        data = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_fields)
    except (OSError, ValueError) as exc:
        raise ValueError(f"{path.name}: {exc}") from exc
    if not isinstance(data, dict):
        raise ValueError(f"{path.name}: expected a JSON object")
    return data


def _canonical_sha256(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value, ensure_ascii=True, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
    ).hexdigest()


def _source_inventory_receipt(map_payload: Mapping[str, object]) -> tuple[str, str]:
    """Return the current artifact and named-presentation receipt identities."""

    source_sha256 = str(map_payload.get("source_artifact_sha256") or "").strip().lower()
    review = map_payload.get("source_named_result_inventory_review")
    if not isinstance(review, Mapping) or review.get("complete") is not True:
        raise ValueError(
            "paper_statement_map.json has no complete typed named-result inventory receipt"
        )
    discovered_sha256 = str(review.get("discovered_named_result_sha256") or "").strip().lower()
    if not _SHA256_RE.fullmatch(source_sha256) or not _SHA256_RE.fullmatch(
        discovered_sha256
    ):
        raise ValueError(
            "paper_statement_map.json has no current source and named-result inventory digests"
        )
    if str(review.get("source_artifact_sha256") or "").strip().lower() != source_sha256:
        raise ValueError(
            "paper_statement_map.json named-result inventory does not pin the current source artifact"
        )
    return source_sha256, discovered_sha256


def _presentation_record(
    presentation: NamedResultPresentation, *, source_item_id: str
) -> dict[str, object]:
    return {
        "kind": presentation.kind,
        "line_end": presentation.line_end,
        "line_start": presentation.line_start,
        "presentation": presentation.presentation,
        "presentation_sha256": named_result_presentations_sha256([presentation]),
        "source_item_id": source_item_id,
        "source_label": presentation.label,
    }


def _current_source_result_inventory(
    folder: Path, map_payload: Mapping[str, object]
) -> dict[str, object] | None:
    """Build the selected theorem-like presentation inventory from source bytes.

    ``None`` means the canonical source bytes are intentionally unavailable.
    Callers may then validate already-frozen portable metadata against the map's
    typed source receipt, but may not synthesize a result set from map prose.
    """

    current = _current_canonical_text_source(
        folder, map_payload, repository_root=ROOT
    )
    if current is None:
        return None
    source_text, source_path, source_format = current
    source_sha256, discovered_sha256 = _source_inventory_receipt(map_payload)
    mode, mode_error = source_coverage_mode_from_map(map_payload)
    if mode_error:
        raise ValueError(mode_error)
    review = map_payload.get("source_named_result_inventory_review")
    assert isinstance(review, Mapping)
    try:
        presentation_inventory = reviewed_source_presentation_inventory(
            source_text,
            source_path=source_path,
            source_format=source_format,
            environment_kinds=review.get("environment_kinds"),
            heading_kinds=review.get("heading_kinds"),
            candidate_dispositions=(
                review.get("candidate_presentations")
                if "candidate_presentations" in review
                else None
            ),
        )
    except (TypeError, ValueError) as exc:
        raise ValueError(f"cannot read the current typed named-result inventory: {exc}") from exc
    classified_presentations = list(presentation_inventory.classified)
    replaced_definition_spans = source_prose_definition_replaced_named_presentation_spans(
        folder,
        map_payload,
        classified_presentations,
        repository_root=ROOT,
    )
    receipt_presentations = [
        presentation
        for presentation in classified_presentations
        if source_named_presentation_in_coverage_scope(presentation.kind, mode)
        and not (
            presentation.kind == "definition"
            and (presentation.line_start, presentation.line_end)
            in replaced_definition_spans
        )
    ]
    if named_result_presentations_sha256(receipt_presentations) != discovered_sha256:
        raise ValueError(
            "paper_statement_map.json named-result receipt is stale for the current source"
        )
    presentations = [
        presentation
        for presentation in classified_presentations
        if presentation.kind in THEOREM_REALIZATION_SOURCE_KINDS
        and source_named_presentation_in_coverage_scope(presentation.kind, mode)
    ]
    raw_items = map_payload.get("items")
    if not isinstance(raw_items, Mapping):
        raise ValueError("paper_statement_map.json: items is not an object")
    selected_item_ids = source_index_byte_pinned_anchor_item_ids(
        folder, map_payload, mode, repository_root=ROOT
    )
    strict_items = {
        item_id: {
            "source_anchor_evidence": raw_items[item_id].get("source_anchor_evidence"),
            **(
                {
                    SOURCE_PRESENTATION_RECONCILIATION_FIELD: raw_items[item_id].get(
                        SOURCE_PRESENTATION_RECONCILIATION_FIELD
                    )
                }
                if SOURCE_PRESENTATION_RECONCILIATION_FIELD in raw_items[item_id]
                else {}
            ),
        }
        for item_id in selected_item_ids
        if isinstance(raw_items.get(item_id), Mapping)
    }
    reconciliations = reconcile_named_result_presentations(
        presentations,
        strict_items,
        source_text=source_text,
        source_path=source_path,
    )
    aliases, alias_errors = source_presentation_aliases(raw_items)
    if alias_errors:
        raise ValueError("; ".join(alias_errors))
    grouped: dict[
        str, list[tuple[NamedResultPresentation, str, tuple[str, ...]]]
    ] = {}
    grouped_kinds: dict[str, str] = {}
    for reconciliation in reconciliations:
        if not reconciliation.matches:
            raise ValueError(
                "selected named presentation has no byte-pinned source item: "
                f"{reconciliation.presentation.kind} {reconciliation.presentation.label}"
            )
        item_ids = tuple(
            match.item_id
            for match in reconciliation.matches
            if not _source_item_is_nonresult_support(
                raw_items.get(match.item_id)
            )
        )
        if not item_ids:
            # A quarantined false restatement or attributed proof-support item
            # remains covered by its owning evidence lane; neither becomes a
            # selected result-table conclusion merely because it is printed as
            # a theorem.
            continue
        canonical_ids = sorted({aliases.get(item_id, item_id) for item_id in item_ids})
        logical_id, logical_kind = _canonical_source_item_for_presentation(
            reconciliation.presentation,
            canonical_ids,
            raw_items,
        )
        if not isinstance(raw_items.get(logical_id), Mapping):
            raise ValueError(f"selected named result has no canonical source item: {logical_id}")
        if (
            str(raw_items[logical_id].get("source_kind") or "").strip().lower()
            not in THEOREM_REALIZATION_SOURCE_KINDS
        ):
            # A reviewed generic ``claim`` presentation can record a labelled
            # source assumption or definition.  It stays in ordinary source
            # coverage, but does not become a result-table conclusion.
            continue
        representative = next(
            (item_id for item_id in item_ids if aliases.get(item_id) == logical_id),
            logical_id,
        )
        grouped.setdefault(logical_id, []).append(
            (reconciliation.presentation, representative, item_ids)
        )
        grouped_kinds[logical_id] = logical_kind
    results: dict[str, object] = {}
    for canonical, entries in sorted(grouped.items()):
        kinds = {
            grouped_kinds[canonical]
            for _presentation, _item_id, _ids in entries
        }
        if len(kinds) != 1 or any(
            not _presentation_kind_matches_source_kind(
                presentation.kind, grouped_kinds[canonical]
            )
            for presentation, _item_id, _ids in entries
        ):
            raise ValueError(
                f"selected named result `{canonical}` has inconsistent presentation kinds"
            )
        records = sorted(
            (
                _presentation_record(presentation, source_item_id=item_id)
                for presentation, item_id, _ids in entries
            ),
            key=lambda row: (
                row["line_start"], row["line_end"], row["source_item_id"]
            ),
        )
        results[canonical] = {
            "kind": next(iter(kinds)),
            "presentations": records,
            "source_item_ids": sorted(
                {canonical, *(item_id for _p, _representative, ids in entries for item_id in ids)}
            ),
        }
    # When a proof restatement aliases one clause owner of a multi-clause
    # printed theorem, reconciliation can initially form a second result whose
    # canonical owner is already carried by the main printed result.  Merge the
    # repeated presentation into that one logical result.
    for result_id in sorted(tuple(results)):
        if result_id not in results:
            continue
        containers = [
            candidate_id
            for candidate_id, candidate in results.items()
            if candidate_id != result_id
            and isinstance(candidate, Mapping)
            and result_id in candidate.get("source_item_ids", [])
        ]
        if len(containers) != 1:
            continue
        target = results[containers[0]]
        duplicate = results.pop(result_id)
        assert isinstance(target, dict) and isinstance(duplicate, Mapping)
        target_presentations = target.get("presentations")
        duplicate_presentations = duplicate.get("presentations")
        target_item_ids = target.get("source_item_ids")
        duplicate_item_ids = duplicate.get("source_item_ids")
        assert isinstance(target_presentations, list)
        assert isinstance(duplicate_presentations, list)
        assert isinstance(target_item_ids, list)
        assert isinstance(duplicate_item_ids, list)
        target["presentations"] = sorted(
            [*target_presentations, *duplicate_presentations],
            key=lambda row: (
                row["line_start"], row["line_end"], row["source_item_id"]
            ),
        )
        target["source_item_ids"] = sorted(
            set(target_item_ids) | set(duplicate_item_ids)
        )
    semantic_owner_ids = _selected_semantic_source_owner_ids(raw_items)
    represented_owner_ids = {
        item_id
        for result in results.values()
        if isinstance(result, Mapping)
        for item_id in result.get("source_item_ids", [])
        if isinstance(item_id, str)
    }
    # A selected clause owner can have an anchor narrower than the printed
    # theorem presentation, so presentation reconciliation may not return it.
    # Attach it to the unique overlapping printed result when one exists.
    for owner in sorted(semantic_owner_ids - represented_owner_ids):
        owner_spans = _source_item_presentation_spans(
            raw_items[owner], source_path=source_path
        )
        overlapping_results: list[str] = []
        for result_id, result in results.items():
            if not isinstance(result, Mapping):
                continue
            result_kind = str(result.get("kind") or "").strip().lower()
            owner_item = raw_items[owner]
            assert isinstance(owner_item, Mapping)
            owner_kind = str(owner_item.get("source_kind") or "").strip().lower()
            if not _presentation_kind_matches_source_kind(result_kind, owner_kind):
                continue
            presentations_for_result = result.get("presentations")
            if not isinstance(presentations_for_result, list):
                continue
            if any(
                isinstance(presentation, Mapping)
                and isinstance(presentation.get("line_start"), int)
                and isinstance(presentation.get("line_end"), int)
                and any(
                    not (
                        anchor_end < presentation["line_start"]
                        or presentation["line_end"] < anchor_start
                    )
                    for anchor_start, anchor_end in owner_spans
                )
                for presentation in presentations_for_result
            ):
                overlapping_results.append(result_id)
        if len(overlapping_results) == 1:
            result = results[overlapping_results[0]]
            assert isinstance(result, dict)
            source_item_ids = result.get("source_item_ids")
            assert isinstance(source_item_ids, list)
            source_item_ids.extend(
                [
                    owner,
                    *(
                        alias
                        for alias, canonical in aliases.items()
                        if canonical == owner
                    ),
                ]
            )
            result["source_item_ids"] = sorted(set(source_item_ids))
            represented_owner_ids.add(owner)
    for owner in sorted(semantic_owner_ids - represented_owner_ids):
        item = raw_items[owner]
        assert isinstance(item, Mapping)
        kind = str(item.get("source_kind") or "").strip().lower()
        results[owner] = {
            "kind": kind,
            "presentations": [],
            "source_item_ids": sorted(
                {
                    owner,
                    *(
                        alias
                        for alias, canonical in aliases.items()
                        if canonical == owner
                    ),
                }
            ),
        }
    return {
        "schema": _SOURCE_INVENTORY_SCHEMA,
        "source_artifact_sha256": source_sha256,
        "discovered_named_result_sha256": discovered_sha256,
        "source_format": source_format,
        "results": results,
    }


def _empty_source_result_inventory() -> dict[str, object]:
    return {
        "schema": _SOURCE_INVENTORY_SCHEMA,
        "source_artifact_sha256": "",
        "discovered_named_result_sha256": "",
        "source_format": "none",
        "results": {},
    }


def _source_result_inventory_for_template(folder: Path) -> dict[str, object]:
    map_payload = _object(folder / "audit/paper_statement_map.json", optional=True)
    if not map_payload:
        return _empty_source_result_inventory()
    current = _current_source_result_inventory(folder, map_payload)
    if current is None:
        raise ValueError(
            "cannot create result-table coverage without the current source artifact; "
            "a source-absent checkout may validate an existing schema-2 portable inventory"
        )
    return current


def reader_report_text(text: str) -> str:
    """Keep the reader assessment; omit source-only comments and later ledgers."""
    text = _COMMENTS.sub("", text)
    match = _TECHNICAL_SECTION.search(text)
    if match:
        text = text[:match.start()]
    return "\n".join(line.rstrip() for line in text.strip().splitlines()) + "\n"


def report_content_sha256(text: str) -> str:
    return hashlib.sha256(reader_report_text(text).encode("utf-8")).hexdigest()


def _automatic_printed_label(
    source_inventory: Mapping[str, object], result: Mapping[str, object]
) -> tuple[str, str, str]:
    """Return a source-visible text label when no rendered-number review is needed."""

    if source_inventory.get("source_format") == "tex":
        return "", "needs_review", "numbered"
    presentations = result.get("presentations")
    if not isinstance(presentations, list) or not presentations:
        return "", "needs_review", "numbered"
    canonical = presentations[0]
    if not isinstance(canonical, Mapping):
        return "", "needs_review", "numbered"
    source_label = str(canonical.get("source_label") or "").strip()
    kind = str(result.get("kind") or "").strip()
    if not source_label or source_label.startswith("@") or kind not in _RESULT_KIND_LABELS:
        return "", "needs_review", "unnumbered"
    result_kind = _RESULT_KIND_LABELS[kind]
    if source_label.lower().startswith(result_kind.lower()):
        return source_label, "source_text_heading", "numbered"
    if not re.fullmatch(
        r"(?:[A-Za-z]\.)?\d+(?:\.\d+)*(?:\([A-Za-z0-9]+\))*",
        source_label,
    ):
        return "", "needs_review", "unnumbered"
    return (
        f"{result_kind} {source_label}",
        "source_text_heading",
        "numbered",
    )


def _result_table_template(folder: Path, report: str) -> dict[str, object]:
    source_inventory = _source_result_inventory_for_template(folder)
    table_rows, _table_errors = section_four_result_table(report)
    source_results = source_inventory.get("results")
    assert isinstance(source_results, Mapping)
    mappings: dict[str, object] = {}
    for result_id, raw_result in sorted(source_results.items()):
        assert isinstance(raw_result, Mapping)
        printed_label, label_basis, numbering = _automatic_printed_label(
            source_inventory, raw_result
        )
        mappings[str(result_id)] = {
            "numbering": numbering,
            "printed_label": printed_label,
            "printed_label_basis": label_basis,
            "row_mappings": [],
        }
    return {
        "schema": _RESULT_TABLE_SCHEMA,
        "complete": False,
        "source_inventory": source_inventory,
        "source_inventory_sha256": _canonical_sha256(source_inventory),
        "results": mappings,
        "rows": {
            row.sha256: {"explanation_keys": [], "supplemental_reason": ""}
            for row in table_rows
        },
    }


def memo_coverage_requirements(folder: Path) -> dict[str, str]:
    """Enumerate records for assessment without deciding their materiality."""
    fidelity = _object(folder / "audit/source_proof_fidelity.json", optional=True)
    result: dict[str, str] = {}
    for field, prefix in (("defects", "defect"), ("model_conventions", "convention")):
        rows = fidelity.get(field, [])
        if not isinstance(rows, list):
            raise ValueError(f"source_proof_fidelity.json: {field} is not a list")
        for row in rows:
            if not isinstance(row, dict) or not isinstance(row.get("id"), str) or not row["id"].strip():
                raise ValueError(f"source_proof_fidelity.json: {field} contains a record without an id")
            key = f"{prefix}/{row['id'].strip()}"
            if key in result:
                raise ValueError(f"source_proof_fidelity.json: duplicate {key}")
            result[key] = str(row.get("source_claim") or row.get("formal_meaning") or row.get("classification") or key)
    source_map = _object(folder / "audit/paper_statement_map.json", optional=True)
    source_items = source_map.get("items", {})
    if not isinstance(source_items, dict):
        raise ValueError("paper_statement_map.json: items is not an object")
    for key, row in sorted(source_items.items()):
        if not isinstance(row, dict):
            raise ValueError(f"paper_statement_map.json: source item {key} is not an object")
        if row.get("corrected_target") is not None:
            result[f"source/{key}/corrected_target"] = str(row.get("source_item") or key)
        if row.get("accepted_additional_assumptions") is not None:
            result[f"source/{key}/additional_assumptions"] = str(row.get("source_item") or key)
    return result


def coverage_template(folder: Path) -> dict:
    report = (folder / REPORT_PATH).read_text(encoding="utf-8")
    return {
        "schema": 2,
        "paper": folder.name,
        "report_sha256": report_content_sha256(report),
        "source_items_sha256": coverage_source_sha256(folder),
        "all_selected_semantic_review_sha256": "",
        "report_inventory_complete": False,
        "items": {
            key: {"disposition": "needs_review", "source_reading": label}
            for key, label in memo_coverage_requirements(folder).items()
        },
        "result_table": _result_table_template(folder, report),
    }


def coverage_source_sha256(folder: Path) -> str:
    """Bind the assessed source records without binding display-only summaries."""
    fidelity = _object(folder / "audit/source_proof_fidelity.json", optional=True)
    source_map = _object(folder / "audit/paper_statement_map.json", optional=True)
    items = source_map.get("items", {})
    projection = {
        "defects": fidelity.get("defects", []),
        "model_conventions": [
            {key: value for key, value in row.items() if key != "report_summary"}
            for row in fidelity.get("model_conventions", [])
            if isinstance(row, dict)
        ],
        "source_records": {
            key: {
                field: row[field]
                for field in ("corrected_target", "accepted_additional_assumptions")
                if field in row
            }
            for key, row in items.items()
            if isinstance(row, dict) and any(
                field in row for field in ("corrected_target", "accepted_additional_assumptions")
            )
        },
    }
    return hashlib.sha256(
        json.dumps(projection, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def _memo_text(path: Path) -> str:
    if path.suffix.lower() == ".md":
        return _COMMENTS.sub("", path.read_text(encoding="utf-8"))
    try:
        return subprocess.run(
            ["pdftotext", str(path), "-"], check=True, capture_output=True,
            text=True, timeout=15,
        ).stdout
    except (OSError, subprocess.SubprocessError) as exc:
        raise ValueError(f"cannot read PDF memo with pdftotext: {path.name}: {exc}") from exc


def _memo_digest(text: str) -> str:
    normalized = "\n".join(line.rstrip() for line in text.strip().splitlines())
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def memo_content_sha256(path: Path) -> str:
    """Bind the explanation actually reviewed, excluding invisible comments."""
    return _memo_digest(_memo_text(path))


def _heading_anchor(heading: str) -> str:
    """Return the ordinary GitHub-style fragment for a Markdown heading."""

    plain = re.sub(
        r"\[([^\]]+)\]\(\s*(?:<[^>]+>|[^)\s]+)(?:\s+\"[^\"]*\")?\s*\)",
        r"\1",
        heading,
    )
    # GFM removes a doubled ASCII dash as punctuation rather than retaining a
    # separator between the adjacent visible tokens (for example, 3.4--3.5).
    plain = plain.replace("--", "")
    plain = re.sub(r"<[^>]*>", "", plain)
    plain = re.sub(r"[`*_~]", "", plain).strip().lower()
    plain = re.sub(r"[^\w\s-]", "", plain)
    return re.sub(r"[\s-]+", "-", plain).strip("-")


def _local_link_targets(text: str) -> set[str]:
    targets: set[str] = set()
    for match in _LINK.finditer(text):
        target = urlsplit(match.group(1) or match.group(2))
        if target.scheme or target.netloc:
            continue
        path = PurePosixPath(unquote(target.path)).as_posix()
        while path.startswith("./"):
            path = path[2:]
        fragment = unquote(target.fragment).strip()
        targets.add(path + (f"#{fragment}" if fragment else ""))
    return targets


def _contains_report_label(cell: str, label: str) -> bool:
    return bool(
        label
        and re.search(r"(?<![\w])" + re.escape(label) + r"(?![\w])", cell)
    )


def _portable_source_inventory_errors(
    folder: Path,
    source_inventory: object,
    source_inventory_sha256: object,
) -> tuple[list[str], dict[str, object], Mapping[str, object]]:
    """Validate current private or source-absent portable result metadata."""

    errors: list[str] = []
    if not isinstance(source_inventory, dict):
        return ["result-table source_inventory is not an object"], {}, {}
    expected_fields = {
        "schema",
        "source_artifact_sha256",
        "discovered_named_result_sha256",
        "source_format",
        "results",
    }
    if set(source_inventory) != expected_fields or source_inventory.get("schema") != 1:
        errors.append("result-table source_inventory has unexpected or missing fields")
    if source_inventory.get("source_format") not in {"none", "tex", "text"}:
        errors.append("result-table source_inventory has no supported source format")
    if source_inventory_sha256 != _canonical_sha256(source_inventory):
        errors.append("result-table source inventory digest is stale or invalid")
    raw_results = source_inventory.get("results")
    if not isinstance(raw_results, dict):
        return errors + ["result-table source_inventory.results is not an object"], {}, {}
    map_payload = _object(folder / "audit/paper_statement_map.json", optional=True)
    if not map_payload:
        if source_inventory != _empty_source_result_inventory():
            errors.append("result-table source inventory has no current source map binding")
        return errors, raw_results, {}
    try:
        source_sha256, discovered_sha256 = _source_inventory_receipt(map_payload)
    except ValueError as exc:
        errors.append(str(exc))
        source_sha256, discovered_sha256 = "", ""
    if source_inventory.get("source_artifact_sha256") != source_sha256:
        errors.append("result-table source inventory is stale for the current source artifact")
    if source_inventory.get("discovered_named_result_sha256") != discovered_sha256:
        errors.append("result-table source inventory is stale for the current named-result receipt")
    try:
        current = _current_source_result_inventory(folder, map_payload)
    except ValueError as exc:
        errors.append(str(exc))
        current = None
    declared_source = str(map_payload.get("source_artifact_path") or "").strip()
    declared_candidates = (
        (folder / declared_source, ROOT / declared_source) if declared_source else ()
    )
    if current is None and any(path.exists() for path in declared_candidates):
        errors.append("result-table source inventory cannot verify the present source artifact")
    elif current is not None and source_inventory != current:
        errors.append("result-table source inventory is stale for the current selected named results")
    raw_items = map_payload.get("items")
    if not isinstance(raw_items, Mapping):
        return errors + ["paper_statement_map.json: items is not an object"], raw_results, {}
    aliases, alias_errors = source_presentation_aliases(raw_items)
    errors.extend(alias_errors)
    selected_semantic_owners = _selected_semantic_source_owner_ids(raw_items)
    semantic_owner_result_counts = {
        owner: 0 for owner in selected_semantic_owners
    }
    seen_presentations: set[str] = set()
    for result_id, raw_result in sorted(raw_results.items()):
        prefix = f"result-table source result `{result_id}`"
        if not isinstance(result_id, str) or not result_id.strip() or not isinstance(
            raw_result, dict
        ):
            errors.append(prefix + " is not a named result object")
            continue
        if set(raw_result) != {"kind", "presentations", "source_item_ids"}:
            errors.append(prefix + " has unexpected or missing fields")
        kind = str(raw_result.get("kind") or "").strip()
        if kind not in THEOREM_REALIZATION_SOURCE_KINDS:
            errors.append(prefix + " has no supported named-result kind")
        canonical_item = raw_items.get(result_id)
        if not isinstance(canonical_item, Mapping):
            errors.append(prefix + " has no current canonical source item")
        elif canonical_item.get("source_presentation_alias") is not None:
            errors.append(prefix + " uses a presentation alias as its canonical item")
        source_item_ids = raw_result.get("source_item_ids")
        if (
            not isinstance(source_item_ids, list)
            or not source_item_ids
            or any(not isinstance(item_id, str) or not item_id for item_id in source_item_ids)
            or len(source_item_ids) != len(set(source_item_ids))
            or result_id not in source_item_ids
        ):
            errors.append(prefix + " has invalid source_item_ids")
            source_item_ids = []
        for item_id in source_item_ids:
            item = raw_items.get(item_id)
            if not isinstance(item, Mapping):
                errors.append(prefix + f" has no current source item `{item_id}`")
            elif (
                item_id in aliases
                and aliases.get(item_id) != result_id
                and aliases.get(item_id) not in source_item_ids
            ):
                errors.append(prefix + f" has a foreign presentation alias `{item_id}`")
        expected_aliases = {
            alias
            for alias, canonical in aliases.items()
            if canonical in source_item_ids
        }
        if expected_aliases - set(source_item_ids):
            errors.append(prefix + " omits a current repeated source presentation")
        for owner in selected_semantic_owners.intersection(source_item_ids):
            semantic_owner_result_counts[owner] += 1
        presentations = raw_result.get("presentations")
        if not isinstance(presentations, list):
            errors.append(prefix + " has no source presentations")
            continue
        if not presentations:
            if result_id not in selected_semantic_owners:
                errors.append(prefix + " has no source presentations")
            continue
        presentation_item_ids: set[str] = set()
        presentation_spans: list[tuple[int, int]] = []
        for index, presentation in enumerate(presentations):
            label = f"{prefix} presentation {index}"
            if not isinstance(presentation, dict) or set(presentation) != {
                "kind",
                "line_end",
                "line_start",
                "presentation",
                "presentation_sha256",
                "source_item_id",
                "source_label",
            }:
                errors.append(label + " has unexpected or missing fields")
                continue
            line_start = presentation.get("line_start")
            line_end = presentation.get("line_end")
            if (
                not isinstance(line_start, int)
                or isinstance(line_start, bool)
                or not isinstance(line_end, int)
                or isinstance(line_end, bool)
                or line_start < 1
                or line_end < line_start
            ):
                errors.append(label + " has invalid presentation coordinates")
                continue
            try:
                typed = NamedResultPresentation(
                    kind=str(presentation.get("kind") or ""),
                    label=str(presentation.get("source_label") or ""),
                    line_start=line_start,
                    line_end=line_end,
                    presentation=str(presentation.get("presentation") or ""),
                )
            except (TypeError, ValueError):
                errors.append(label + " has invalid presentation coordinates")
                continue
            digest = str(presentation.get("presentation_sha256") or "")
            if digest != named_result_presentations_sha256([typed]):
                errors.append(label + " has an invalid presentation digest")
            if digest in seen_presentations:
                errors.append(label + " duplicates another source presentation")
            seen_presentations.add(digest)
            presentation_spans.append((line_start, line_end))
            if not _presentation_kind_matches_source_kind(typed.kind, kind):
                errors.append(label + " does not preserve the result kind")
            presentation_item_id = presentation.get("source_item_id")
            if presentation_item_id not in source_item_ids:
                errors.append(label + " has no matching source item")
            elif isinstance(presentation_item_id, str):
                presentation_item_ids.add(presentation_item_id)
        if not any(
            item_id == result_id or aliases.get(item_id) == result_id
            for item_id in presentation_item_ids
        ):
            errors.append(prefix + " source presentations omit their canonical or alias item")
        missing_alias_presentations = {
            alias
            for alias in expected_aliases.intersection(source_item_ids)
            if alias not in presentation_item_ids
            and not any(
                not (anchor_end < line_start or line_end < anchor_start)
                for anchor_start, anchor_end in _source_item_presentation_spans(
                    raw_items.get(alias), source_path=declared_source
                )
                for line_start, line_end in presentation_spans
            )
        }
        if missing_alias_presentations:
            errors.append(
                prefix
                + " omits repeated source presentation records for "
                + ", ".join(f"`{item_id}`" for item_id in sorted(missing_alias_presentations))
            )
    for owner, count in sorted(semantic_owner_result_counts.items()):
        if count != 1:
            errors.append(
                f"selected semantic source owner `{owner}` occurs in {count} result-table source results"
            )
    return errors, raw_results, raw_items


def _required_result_explanation_keys(
    raw_items: Mapping[str, object],
    source_item_ids: object,
    coverage_items: Mapping[str, object],
) -> set[str]:
    result: set[str] = set()
    if not isinstance(source_item_ids, list):
        return result
    for item_id in source_item_ids:
        item = raw_items.get(item_id)
        if not isinstance(item, Mapping):
            continue
        for field, prefix in (
            ("source_defect_ids", "defect"),
            ("model_convention_ids", "convention"),
        ):
            identifiers = item.get(field)
            if isinstance(identifiers, list):
                for identifier in identifiers:
                    key = (
                        f"{prefix}/{identifier.strip()}"
                        if isinstance(identifier, str) and identifier.strip()
                        else ""
                    )
                    coverage = coverage_items.get(key)
                    if key and (
                        not isinstance(coverage, Mapping)
                        or coverage.get("report_home", 4) == 4
                    ):
                        result.add(key)
        for field, suffix in (
            ("corrected_target", "corrected_target"),
            ("accepted_additional_assumptions", "additional_assumptions"),
        ):
            if item.get(field) is None:
                continue
            key = f"source/{item_id}/{suffix}"
            coverage = coverage_items.get(key)
            if (
                not isinstance(coverage, Mapping)
                or coverage.get("report_home", 4) == 4
            ):
                result.add(key)
    return result


def _result_table_errors(
    folder: Path,
    report: str,
    assessment: Mapping[str, object],
    coverage_items: Mapping[str, object],
) -> tuple[str, ...]:
    result_table = assessment.get("result_table")
    if not isinstance(result_table, dict):
        return ("REPORT_MEMO_COVERAGE.json: result_table is not an object",)
    errors: list[str] = []
    if set(result_table) != {
        "schema",
        "complete",
        "source_inventory",
        "source_inventory_sha256",
        "results",
        "rows",
    } or result_table.get("schema") != _RESULT_TABLE_SCHEMA:
        errors.append("result_table has unexpected or missing assessment fields")
    if result_table.get("complete") is not True:
        errors.append("result-table inventory has not been reviewed to completion")
    table_rows, table_errors = section_four_result_table(report)
    errors.extend(table_errors)
    rows_by_digest = {row.sha256: row for row in table_rows}
    inventory_errors, source_results, raw_items = _portable_source_inventory_errors(
        folder,
        result_table.get("source_inventory"),
        result_table.get("source_inventory_sha256"),
    )
    errors.extend(inventory_errors)
    mappings = result_table.get("results")
    if not isinstance(mappings, dict):
        return tuple(errors + ["result_table.results is not an object"])
    missing_results = sorted(set(source_results) - set(mappings))
    unknown_results = sorted(set(mappings) - set(source_results))
    errors.extend(
        f"selected named result has no Section 4 mapping: {result_id}"
        for result_id in missing_results
    )
    errors.extend(
        f"Section 4 mapping names an unknown selected result: {result_id}"
        for result_id in unknown_results
    )
    mapped_rows: dict[str, set[str]] = {}
    required_by_result: dict[str, set[str]] = {}
    for result_id, mapping in sorted(mappings.items()):
        prefix = f"result_table.results.{result_id}"
        if not isinstance(mapping, dict):
            errors.append(prefix + " is not an object")
            continue
        allowed = {
            "numbering",
            "printed_label",
            "printed_label_basis",
            "row_mappings",
            "grouping_reason",
            "split_reason",
        }
        required_fields = allowed - {"grouping_reason", "split_reason"}
        if not required_fields.issubset(mapping) or set(mapping) - allowed:
            errors.append(prefix + " has unexpected or missing fields")
        source_result = source_results.get(result_id)
        if not isinstance(source_result, Mapping):
            continue
        printed_label = str(mapping.get("printed_label") or "").strip()
        basis = str(mapping.get("printed_label_basis") or "").strip()
        numbering = str(mapping.get("numbering") or "").strip()
        kind = str(source_result.get("kind") or "").strip()
        kind_label = _RESULT_KIND_LABELS.get(kind, "")
        if (
            not printed_label
            or not kind_label
            or (
                basis == "source_text_heading"
                and not re.match(
                    re.escape(kind_label) + r"\b",
                    printed_label,
                    re.IGNORECASE,
                )
            )
        ):
            errors.append(prefix + " has no valid human-facing printed label")
        if basis not in _PRINTED_LABEL_BASES:
            errors.append(prefix + " has no reviewed printed-label basis")
        if numbering not in _NUMBERING_KINDS:
            errors.append(prefix + " has no valid numbered/unnumbered disposition")
        source_inventory = result_table.get("source_inventory")
        if (
            basis == "source_text_heading"
            and isinstance(source_inventory, Mapping)
        ):
            expected_label, _basis, expected_numbering = _automatic_printed_label(
                source_inventory, source_result
            )
            if not expected_label or printed_label != expected_label or numbering != expected_numbering:
                errors.append(prefix + " printed label does not match the visible source heading")
        elif (
            basis == "reviewed_rendered_source"
            and not isinstance(mapping.get("printed_label"), str)
        ):
            errors.append(prefix + " rendered-source label review is incomplete")
        raw_row_mappings = mapping.get("row_mappings")
        if (
            not isinstance(raw_row_mappings, list)
            or not raw_row_mappings
            or any(
                not isinstance(row_mapping, dict)
                or set(row_mapping) != {"report_label", "row_sha256"}
                for row_mapping in raw_row_mappings
            )
        ):
            errors.append(prefix + " must map to one or more distinct Section 4 rows")
            raw_row_mappings = []
        row_ids = [
            str(row_mapping.get("row_sha256") or "")
            for row_mapping in raw_row_mappings
        ]
        if len(row_ids) != len(set(row_ids)):
            errors.append(prefix + " repeats a Section 4 row mapping")
        if len(raw_row_mappings) > 1 and not str(mapping.get("split_reason") or "").strip():
            errors.append(prefix + " maps one result across rows without a split_reason")
        for row_mapping in raw_row_mappings:
            row_id = str(row_mapping.get("row_sha256") or "")
            report_label = str(row_mapping.get("report_label") or "").strip()
            if report_label != printed_label and not str(
                mapping.get("grouping_reason") or ""
            ).strip():
                errors.append(prefix + " uses a grouped/subpart report label without a grouping_reason")
            row = rows_by_digest.get(row_id)
            if row is None:
                errors.append(prefix + f" maps to an unknown or stale Section 4 row: {row_id}")
                continue
            if not _contains_report_label(row.result, report_label):
                errors.append(prefix + " report_label does not occur in its Section 4 result cell")
            mapped_rows.setdefault(row_id, set()).add(result_id)
        required_by_result[result_id] = _required_result_explanation_keys(
            raw_items,
            source_result.get("source_item_ids"),
            coverage_items,
        )
    row_assessments = result_table.get("rows")
    if not isinstance(row_assessments, dict):
        return tuple(errors + ["result_table.rows is not an object"])
    for row_id in sorted(set(rows_by_digest) - set(row_assessments)):
        errors.append(f"Section 4 row has no coverage assessment: {row_id}")
    for row_id in sorted(set(row_assessments) - set(rows_by_digest)):
        errors.append(f"result-table assessment names an unknown or stale row: {row_id}")
    explained_by_result: dict[str, set[str]] = {
        result_id: set() for result_id in mappings
    }
    for row_id, row_assessment in sorted(row_assessments.items()):
        prefix = f"result_table.rows.{row_id}"
        if not isinstance(row_assessment, dict):
            errors.append(prefix + " is not an object")
            continue
        allowed = {"explanation_keys", "supplemental_reason"}
        if "explanation_keys" not in row_assessment or set(row_assessment) - allowed:
            errors.append(prefix + " has unexpected or missing fields")
        explanation_keys = row_assessment.get("explanation_keys")
        if (
            not isinstance(explanation_keys, list)
            or any(not isinstance(key, str) or not key for key in explanation_keys)
            or len(explanation_keys) != len(set(explanation_keys))
        ):
            errors.append(prefix + " has invalid explanation_keys")
            explanation_keys = []
        if row_id not in mapped_rows and not str(
            row_assessment.get("supplemental_reason") or ""
        ).strip():
            errors.append(prefix + " is not mapped to a result and has no supplemental_reason")
        row = rows_by_digest.get(row_id)
        row_links = (
            _local_link_targets(row.result) | _local_link_targets(row.comparison)
            if row is not None
            else set()
        )
        for key in explanation_keys:
            coverage_item = coverage_items.get(key)
            if not isinstance(coverage_item, Mapping) or coverage_item.get("disposition") != "memo":
                errors.append(prefix + f" references a non-memo coverage item: {key}")
                continue
            memo = str(coverage_item.get("memo") or "").removeprefix("./")
            anchor = str(coverage_item.get("memo_anchor") or "").strip()
            heading = str(coverage_item.get("memo_heading") or "").strip()
            if not memo or not anchor or not heading or _heading_anchor(heading) != anchor:
                errors.append(prefix + f" has no exact reviewed memo target for {key}")
                continue
            target = f"{memo}#{anchor}"
            if target not in row_links:
                errors.append(prefix + f" does not link its exact memo target for {key}: {target}")
            for result_id in mapped_rows.get(row_id, set()):
                explained_by_result.setdefault(result_id, set()).add(key)
    for result_id, required_keys in sorted(required_by_result.items()):
        required_memos = {
            key
            for key in required_keys
            if isinstance(coverage_items.get(key), Mapping)
            and coverage_items[key].get("disposition") == "memo"
        }
        for key in sorted(required_memos - explained_by_result.get(result_id, set())):
            errors.append(
                f"selected named result `{result_id}` has no exact Section 4 memo mapping for {key}"
            )
    return tuple(dict.fromkeys(errors))


def report_memo_coverage_errors(
    folder: Path,
    *,
    expected_all_selected_semantic_review_sha256: str | None = None,
) -> tuple[str, ...]:
    """Check explicit coverage, current reader text, and resolvable public notes.

    A standalone call checks the document and source bindings recorded in the
    assessment.  Only a caller that supplies the current all-selected semantic
    identity verifies that the assessment still describes the current reviewed
    source-to-Lean targets.  The digest is a comparison input, not evidence.
    """
    errors: list[str] = []
    try:
        report = (folder / REPORT_PATH).read_text(encoding="utf-8")
        assessment = _object(folder / COVERAGE_PATH)
        required = memo_coverage_requirements(folder)
        source_digest = coverage_source_sha256(folder)
    except (OSError, ValueError) as exc:
        return (str(exc),)
    if type(assessment.get("schema")) is not int or assessment.get("schema") != 2 or assessment.get("paper") != folder.name:
        errors.append("REPORT_MEMO_COVERAGE.json: expected schema 2 and the current paper id")
    if set(assessment) != {
        "schema", "paper", "report_sha256", "source_items_sha256",
        "all_selected_semantic_review_sha256", "report_inventory_complete",
        "items", "result_table",
    }:
        errors.append("REPORT_MEMO_COVERAGE.json: unexpected or missing assessment fields")
    recorded_semantic_sha256 = str(
        assessment.get("all_selected_semantic_review_sha256") or ""
    ).strip().lower()
    if not _SHA256_RE.fullmatch(recorded_semantic_sha256):
        errors.append(
            "report clarification inventory has no all-selected semantic-review basis"
        )
    if expected_all_selected_semantic_review_sha256 is not None:
        expected_semantic_sha256 = str(
            expected_all_selected_semantic_review_sha256 or ""
        ).strip().lower()
        if not _SHA256_RE.fullmatch(expected_semantic_sha256):
            errors.append(
                "current all-selected semantic-review basis was not supplied by the terminal closeout"
            )
        elif recorded_semantic_sha256 != expected_semantic_sha256:
            errors.append(
                "report clarification inventory is stale for the current all-selected semantic review"
            )
    if assessment.get("report_inventory_complete") is not True:
        errors.append("report clarification inventory has not been reviewed to completion")
    if assessment.get("report_sha256") != report_content_sha256(report):
        errors.append("report clarification inventory is stale for the current reader-facing report")
    if assessment.get("source_items_sha256") != source_digest:
        errors.append("report clarification inventory is stale for the current source records")
    items = assessment.get("items")
    if not isinstance(items, dict):
        return tuple(errors + ["REPORT_MEMO_COVERAGE.json: items is not an object"])
    errors.extend(_result_table_errors(folder, report, assessment, items))
    for key in sorted(set(required) - set(items)):
        errors.append(f"source clarification has no coverage assessment: {key}")
    visible_report = reader_report_text(report)
    links = _local_links(visible_report)
    rendered_report = _COMMENTS.sub("", report)
    if _DRAFT_LABEL.search(rendered_report) or _VISIBLE_GENERATOR.search(rendered_report):
        errors.append("reader-facing report contains a draft label or visible generated boundary")
    if _has_approval_label(rendered_report):
        errors.append("reader-facing report uses an approval label instead of stating the formalized scope")
    assumptions = _ASSUMPTIONS_SECTION.search(visible_report)
    assessed_memos = {
        item.get("memo") for item in items.values()
        if isinstance(item, dict) and item.get("disposition") == "memo"
        and isinstance(item.get("memo"), str)
    }
    if assumptions and assessed_memos:
        body = assumptions.group(1).strip()
        if body and not re.fullmatch(r"None\.?", body, re.IGNORECASE):
            if not (_local_links(body) & assessed_memos):
                errors.append("Section 6 discusses assumptions without linking an assessed clarification memo")
    memo_cache: dict[str, str] = {}
    for key, item in sorted(items.items()):
        if key not in required and not (key.startswith("report/") and len(key) > 7):
            errors.append(f"unknown source clarification in coverage assessment: {key}")
        if not isinstance(item, dict):
            errors.append(f"coverage assessment is not an object: {key}")
            continue
        disposition = item.get("disposition")
        allowed_fields = (
            {"disposition", "reason"} if disposition == "not_material"
            else {
                "disposition", "memo", "memo_sha256", "memo_heading",
                "memo_anchor", "source_reading", "report_home",
            }
        )
        if set(item) - allowed_fields:
            errors.append(f"unexpected coverage item fields: {key}")
        if disposition == "not_material":
            if not isinstance(item.get("reason"), str) or not item["reason"].strip():
                errors.append(f"non-material assessment needs a mathematical reason: {key}")
            continue
        if disposition != "memo":
            errors.append(f"source clarification needs a reviewed memo or non-material disposition: {key}")
            continue
        report_home = item.get("report_home", 4)
        if type(report_home) is not int or not 1 <= report_home <= 11:
            errors.append(
                f"memo coverage item has no valid reader-facing report_home section: {key}"
            )
            report_home = 4
        relative = item.get("memo")
        if not isinstance(relative, str):
            errors.append(f"memo path is missing: {key}")
            continue
        path = PurePosixPath(relative)
        if (
            path.is_absolute() or path.as_posix() != relative or ".." in path.parts
            or path.parts[:1] != ("docs",) or path.suffix.lower() not in {".md", ".pdf"}
        ):
            errors.append(f"memo must be a paper-local readable document under docs/: {key}: {relative}")
            continue
        if _PRIVATE_MEMO_NAME.search(relative):
            errors.append(f"memo target is an internal approval or working document: {key}: {relative}")
            continue
        target = folder / relative
        try:
            target.resolve().relative_to(folder.resolve())
            target.resolve().relative_to((folder / "docs").resolve())
        except (OSError, RuntimeError, ValueError):
            errors.append(f"memo escapes the paper docs directory: {relative}")
            continue
        if relative not in links:
            errors.append(f"report does not link the clarification memo: {key}: {relative}")
        if relative not in memo_cache:
            try:
                text = _memo_text(target)
            except (OSError, ValueError) as exc:
                errors.append(f"missing or unreadable clarification memo: {relative}: {exc}")
                memo_cache[relative] = ""
                continue
            memo_cache[relative] = text
            if not text.strip():
                errors.append(f"clarification memo has no readable text: {relative}")
            if _DRAFT_LABEL.search(text) or _VISIBLE_GENERATOR.search(text):
                errors.append(f"clarification memo contains a draft label or visible generated boundary: {relative}")
            if _PRIVATE_PROVENANCE.search(text):
                errors.append(f"clarification memo exposes internal approval or working records: {relative}")
            if _has_approval_label(text):
                errors.append(f"clarification memo uses an approval label instead of stating the formalized scope: {relative}")
        expected_memo_digest = _memo_digest(memo_cache[relative])
        if item.get("memo_sha256") != expected_memo_digest:
            errors.append(f"clarification memo changed since its coverage assessment: {key}: {relative}")
        heading = item.get("memo_heading")
        if heading is not None and (
            not isinstance(heading, str) or not heading.strip()
            or not re.search(r"^#{1,6}\s+" + re.escape(heading) + r"\s*$", memo_cache.get(relative, ""), re.MULTILINE)
        ):
            errors.append(f"clarification memo heading does not resolve: {key}: {heading}")
        anchor = item.get("memo_anchor")
        if anchor is not None and (
            not isinstance(anchor, str)
            or not anchor.strip()
            or not isinstance(heading, str)
            or _heading_anchor(heading) != anchor.strip()
        ):
            errors.append(f"clarification memo anchor does not resolve: {key}: {anchor}")
        if report_home != 4:
            section = re.search(
                rf"^##\s+{report_home}\.\s+[^\n]+\n(.*?)(?=^##\s+\d+\.\s|\Z)",
                visible_report,
                re.MULTILINE | re.DOTALL,
            )
            if path.suffix.lower() == ".pdf":
                target_link = relative
            elif (
                not isinstance(heading, str)
                or not heading.strip()
                or not isinstance(anchor, str)
                or not anchor.strip()
                or _heading_anchor(heading) != anchor.strip()
            ):
                errors.append(
                    f"coverage item with Section {report_home} report_home needs an exact memo heading and anchor: {key}"
                )
                continue
            else:
                target_link = f"{relative}#{anchor.strip()}"
            if section is None or target_link not in _local_link_targets(
                section.group(1)
            ):
                errors.append(
                    f"coverage item is not linked from its reviewed Section {report_home} report_home: {key}: {target_link}"
                )
    return tuple(dict.fromkeys(errors))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--write-template", action="store_true")
    args = parser.parse_args()
    folder = ROOT / "papers" / args.paper
    if not folder.is_dir() or folder.parent != ROOT / "papers":
        parser.error("--paper must name an existing paper folder")
    if args.write_template:
        target = folder / COVERAGE_PATH
        if target.exists():
            parser.error("coverage assessment already exists; preserve its reviewed dispositions")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(coverage_template(folder), indent=2) + "\n", encoding="utf-8")
        print(f"wrote non-accepting coverage template: {target}")
        return 0
    errors = report_memo_coverage_errors(folder)
    for error in errors:
        print(error)
    if not errors:
        print(
            "report document/source coverage is structurally current; this "
            "standalone command did not verify the recorded semantic basis: "
            f"{args.paper}"
        )
    return int(bool(errors))


if __name__ == "__main__":
    raise SystemExit(main())
