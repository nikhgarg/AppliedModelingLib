"""Source-only inventory projection for intake and semantic-review planning.

The projection owns no dashboard, Lean, review ledger, or acceptance behavior.
It converts an explicitly supplied statement-map payload into normalized source
records.  Callers remain responsible for structural validation and for freezing
any source text files before using the result inside a transaction.
"""

from __future__ import annotations

import copy
import re
from pathlib import Path
from typing import Any, Mapping

from scripts.source_artifact_companion import semantic_review_source_identity
from scripts.source_review_input import normalize_statement, statement_digest


SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
MODEL_CONVENTION_IDS_FIELD = "model_convention_ids"
SOURCE_DEFINITION_PARTITION_FIELD = "source_definition_partition"


def _valid_digest(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if SHA256_RE.fullmatch(text) else ""


def _string_list(value: object) -> list[str]:
    if isinstance(value, (list, tuple, set)):
        values = value
    elif value is None:
        values = []
    else:
        values = [value]
    return [str(item).strip() for item in values if str(item).strip()]


def _safe_relative_source(folder: Path, raw_path: object) -> Path | None:
    text = str(raw_path or "").strip()
    if not text:
        return None
    candidate = (folder / text).resolve()
    try:
        candidate.relative_to(folder.resolve())
    except ValueError:
        return None
    return candidate


def inventory_from_source_map(
    folder: Path, payload: Mapping[str, Any]
) -> dict[str, dict[str, Any]]:
    """Build the normalized source inventory from one supplied map payload."""

    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        return {}
    map_artifact_path, map_artifact_sha256 = semantic_review_source_identity(payload)
    map_artifact_sha256 = _valid_digest(map_artifact_sha256)
    map_anchor_required = payload.get("source_anchor_evidence_required") is True
    text_cache: dict[Path, list[str]] = {}
    inventory: dict[str, dict[str, Any]] = {}
    for raw_key, raw_item in raw_items.items():
        key = str(raw_key or "").strip()
        if not key or not isinstance(raw_item, Mapping):
            continue
        direct = str(raw_item.get("statement") or "").strip()
        source_location = str(raw_item.get("source_location") or "").strip()
        statement = ""
        if direct:
            statement = normalize_statement(direct)
        else:
            source_path = _safe_relative_source(
                folder, raw_item.get("source_text_file") or "source.txt"
            )
            try:
                start = int(str(raw_item.get("start_line")))
                end = int(str(raw_item.get("end_line")))
            except (TypeError, ValueError):
                continue
            if source_path is None or start <= 0 or end < start:
                continue
            try:
                lines = text_cache[source_path]
            except KeyError:
                try:
                    lines = source_path.read_text(encoding="utf-8").splitlines()
                except OSError:
                    continue
                text_cache[source_path] = lines
            if start > len(lines):
                continue
            statement = normalize_statement(
                "\n".join(lines[start - 1 : min(end, len(lines))])
            )
            if not source_location:
                source_location = f"{source_path.name}:{start}-{end}"
        if not statement:
            continue
        inventory[key] = {
            "title": str(raw_item.get("title") or "").strip(),
            "statement": statement,
            "aliases": _string_list(raw_item.get("aliases")),
            "source": "audit/paper_statement_map.json",
            "coverage_status": str(raw_item.get("coverage_status") or "").strip().lower(),
            "protocol_role": str(raw_item.get("protocol_role") or "").strip().lower(),
            "corrected_target": raw_item.get("corrected_target"),
            "source_kind": str(raw_item.get("source_kind") or "").strip().lower(),
            "claim_bearing": raw_item.get("claim_bearing"),
            "source_scope_classification": str(
                raw_item.get("source_scope_classification") or ""
            ).strip().lower(),
            "user_approved_scope_exclusion": raw_item.get(
                "user_approved_scope_exclusion"
            ),
            "scope_reason": str(raw_item.get("scope_reason") or "").strip(),
            "source_evidence": str(raw_item.get("source_evidence") or "").strip(),
            "source_artifact_path": str(
                raw_item.get("source_artifact_path") or map_artifact_path
            ).strip(),
            "source_artifact_sha256": _valid_digest(
                raw_item.get("source_artifact_sha256") or map_artifact_sha256
            ),
            "canonical_source_artifact_path": map_artifact_path,
            "canonical_source_artifact_sha256": map_artifact_sha256,
            "source_anchor_evidence_required": (
                raw_item.get("source_anchor_evidence_required") is True
                or map_anchor_required
            ),
            "source_anchor_evidence": raw_item.get("source_anchor_evidence"),
            "source_defect_ids": _string_list(raw_item.get("source_defect_ids")),
            "support_lean_declarations": _string_list(
                raw_item.get("support_lean_declarations")
            ),
            "spec_lean_declarations": _string_list(
                raw_item.get("spec_lean_declarations")
            ),
            "semantic_contract": raw_item.get("semantic_contract"),
            "lean_declarations": _string_list(raw_item.get("lean_declarations")),
            "proof_lean_declarations": _string_list(
                raw_item.get("proof_lean_declarations")
            ),
            "source_location": source_location,
            "source_url": str(
                raw_item.get("source_url") or payload.get("source_url") or ""
            ).strip(),
            "source_note": str(raw_item.get("source_note") or "").strip(),
            "source_status": str(raw_item.get("source_status") or "").strip(),
            "statement_sha256": statement_digest(statement),
        }
        if MODEL_CONVENTION_IDS_FIELD in raw_item:
            inventory[key][MODEL_CONVENTION_IDS_FIELD] = copy.deepcopy(
                raw_item.get(MODEL_CONVENTION_IDS_FIELD)
            )
        for field in (
            SOURCE_DEFINITION_PARTITION_FIELD,
            "source_presentation_alias",
            "semantic_context_requirements",
        ):
            if field in raw_item:
                inventory[key][field] = copy.deepcopy(raw_item.get(field))
    return inventory
