"""Validate structural formalization regularities for configured assumptions.

This is intentionally a narrow, non-source-credit lane.  A paper may need a
Lean representation regularity (for example, a measurable carrier or a
probability-measure instance) in order to state a source model faithfully.
Such a regularity is source-located and audited, but it is *not* a source
theorem, a source-contract association, or evidence for a paper conclusion.

The matching relation is structural.  In particular, it does not select an
entry from a judgment key, Lean declaration spelling, binder name, or source
map item label.  Those fields may remain in a ledger as reviewer navigation
text, but changing them cannot choose a different raw obligation.
"""

from __future__ import annotations

import copy
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping


CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE = (
    "audit/configured_assumption_formalization_regularities.json"
)
CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_SCHEMA = 1
CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_ARTIFACT_KIND = (
    "configured_assumption_formalization_regularities"
)
CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_STATUS = "current"
CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_STATUS_FIELD = (
    "configured_assumption_formalization_regularities_file"
)
_EXACT_INPUT_UNSET = object()
CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_ID_FIELD = (
    "configured_assumption_formalization_regularity_id"
)
CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_SHA256_FIELD = (
    "configured_assumption_formalization_regularity_sha256"
)
CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_CONTEXT_SHA256_FIELD = (
    "configured_assumption_formalization_regularity_context_sha256"
)
FORMALIZATION_REGULARITY_CLASSIFICATION = "approved_formalization_regularity"
CANONICAL_TYPE_DIGEST_SCHEMA = "sha256-utf8-source-record-canonical-type-v1"
CONTEXT_SCHEMA = 1
_SHA256_RE = re.compile(r"[0-9a-f]{64}")

_DIRECT_SOURCE_ASSOCIATION_FIELDS = (
    "source_contract_association",
    "semantic_contract_source_association",
    "source_statement_association",
    "recursive_field_explicit_parent_route",
)
_FORBIDDEN_RESPONSE_FIELDS = frozenset(
    {
        "source_contract_association",
        "semantic_contract_source_association",
        "source_statement_association",
        "recursive_field_explicit_parent_route",
        "semantic_association_sha256",
        "source_contract_association_sha256",
        "source_item_identities",
        "source_semantic_sha256",
        "source_semantic_sha256_by_key",
        "source_map_item_sha256",
        "source_map_item_sha256_by_key",
        "source_map_item_keys_sha256",
        "source_map_item_keys",
        "source_item_semantic_sha256",
        "source_item_semantic_sha256_by_key",
        "model_convention_ids",
        "model_convention_sha256_by_id",
        "governing_defect_ids",
        "governing_source_defect_ids",
        "corrected_target_sha256_by_source_item",
        "corrected_target_sha256_by_source_semantic_sha256",
        "corrected_target_sha256",
        "source_key",
        "paper_statement_key",
        "source_target_disposition",
        "source_target_disposition_sha256",
        "source_target_match_verdict",
    }
)


def _canonical_payload(value: object) -> object:
    """Return a deterministic JSON-compatible representation.

    Lists deliberately retain their order.  Binder sequence is positional and
    source anchors are explicit evidence, so treating either as an unordered
    set would make a different regularity look current.
    """

    if isinstance(value, Mapping):
        return {
            str(key): _canonical_payload(item)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        }
    if isinstance(value, tuple):
        return [_canonical_payload(item) for item in value]
    if isinstance(value, list):
        return [_canonical_payload(item) for item in value]
    return value


def canonical_digest(value: object) -> str:
    encoded = json.dumps(
        _canonical_payload(value),
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _sha256_text(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _canonical_type(type_text: object) -> str:
    """Use the conservative source-record type normalization locally.

    Keeping this small avoids importing the source-record generator into the
    runtime validator.  It is intentionally an equality normalizer, not a
    parser or theorem prover.
    """

    text = " ".join(str(type_text or "").split())
    for source, target in (
        ("<->", "↔"),
        ("->", "→"),
        ("/\\", "∧"),
        ("\\/", "∨"),
        ("<=", "≤"),
        (">=", "≥"),
        ("!=", "≠"),
    ):
        text = text.replace(source, target)
    text = re.sub(r"\s*([(){}\[\],:.])\s*", r"\1", text)
    text = re.sub(r"\s*(→|↔|∧|∨|=|≠|≤|≥|<|>)\s*", r"\1", text)
    while text.startswith("(") and text.endswith(")"):
        text = text[1:-1].strip()
    return text


def _regularity_anchor_identity(anchor: Mapping[str, object]) -> dict[str, object]:
    """Return the name-free source coordinate that can affect regularity credit."""

    return {
        "anchor_path": str(anchor.get("anchor_path") or "").strip(),
        "line_start": anchor.get("line_start"),
        "line_end": anchor.get("line_end"),
        "quoted_text_sha256": _sha256_text(anchor.get("quoted_text_sha256")),
    }


def configured_assumption_formalization_regularity_entry_payload(
    entry: Mapping[str, object],
) -> dict[str, object]:
    """Project one ledger entry to the semantically pinned regularity content.

    The ledger can retain labels useful to a reviewer, but they must not make
    an already-reviewed structural regularity stale.  In particular this
    projection excludes entry ids, judgment keys, declaration/binder spellings,
    source-item labels, source-location display text, and explanatory prose.
    The source coordinates and quoted source bytes remain pinned separately.
    """

    declaration = entry.get("reviewed_declaration")
    position = entry.get("structural_input_position")
    scope = entry.get("scope_constraints")
    raw_reuse = entry.get("raw_item_reuse_eligibility")
    anchors = entry.get("source_anchors")
    anchor_identities = (
        sorted(
            (
                _regularity_anchor_identity(anchor)
                for anchor in anchors
                if isinstance(anchor, Mapping)
            ),
            key=lambda anchor: (
                str(anchor["anchor_path"]),
                str(anchor["line_start"]),
                str(anchor["line_end"]),
                str(anchor["quoted_text_sha256"]),
            ),
        )
        if isinstance(anchors, list)
        else []
    )
    expected_scope_fields = (
        "is_source_contract",
        "can_supply_direct_source_result_credit",
        "can_close_unrelated_boundary_inputs",
        "applies_only_to_exact_declaration_signature_and_binder_position",
        "name_matching_permitted",
    )
    return {
        "schema": CONTEXT_SCHEMA,
        "raw_item_section": str(entry.get("raw_item_section") or "").strip(),
        "raw_item_kind": str(entry.get("raw_item_kind") or "").strip(),
        "raw_item_reuse_eligibility": {
            "eligible": raw_reuse.get("eligible") if isinstance(raw_reuse, Mapping) else None,
            "blockers": sorted(
                {
                    str(blocker).strip()
                    for blocker in raw_reuse.get("blockers") or []
                    if str(blocker).strip()
                }
            )
            if isinstance(raw_reuse, Mapping)
            else [],
        },
        "source_record_current_group_descriptor_sha256": _sha256_text(
            entry.get("source_record_current_group_descriptor_sha256")
        ),
        "reviewed_declaration": {
            "declaration_sha256": _sha256_text(
                declaration.get("declaration_sha256")
            )
            if isinstance(declaration, Mapping)
            else "",
            "elaborated_signature_sha256": _sha256_text(
                declaration.get("elaborated_signature_sha256")
            )
            if isinstance(declaration, Mapping)
            else "",
        },
        "structural_input_position": {
            "binder_sequence_sha256": _sha256_text(
                position.get("binder_sequence_sha256")
            )
            if isinstance(position, Mapping)
            else "",
            "binder_position_zero_based": (
                position.get("binder_position_zero_based")
                if isinstance(position, Mapping)
                else None
            ),
            "binder_info": str(position.get("binder_info") or "").strip()
            if isinstance(position, Mapping)
            else "",
            "expanded_input_type": _canonical_type(
                position.get("expanded_input_type")
            )
            if isinstance(position, Mapping)
            else "",
        },
        "canonical_type": _canonical_type(entry.get("canonical_type")),
        "canonical_type_digest_schema": str(
            entry.get("canonical_type_digest_schema") or ""
        ).strip(),
        "canonical_type_sha256": _sha256_text(entry.get("canonical_type_sha256")),
        "source_anchors": anchor_identities,
        "scope_constraints": {
            field: scope.get(field) if isinstance(scope, Mapping) else None
            for field in expected_scope_fields
        },
    }


def configured_assumption_formalization_regularity_entry_sha256(
    entry: Mapping[str, object],
) -> str:
    """Return the name-free digest a regularity response must echo."""

    return canonical_digest(
        configured_assumption_formalization_regularity_entry_payload(entry)
    )


def _matching_delimiter(text: str, start: int) -> int:
    pairs = {"(": ")", "[": "]", "{": "}"}
    opening = text[start]
    closing = pairs.get(opening)
    if closing is None:
        return -1
    depth = 0
    for index in range(start, len(text)):
        char = text[index]
        if char == opening:
            depth += 1
        elif char == closing:
            depth -= 1
            if depth == 0:
                return index
    return -1


def _top_level_colon_index(text: str) -> int:
    depth = 0
    opens = "([{"
    closes = ")] }".replace(" ", "")
    for index, char in enumerate(text):
        if char in opens:
            depth += 1
        elif char in closes:
            depth -= 1
        elif char == ":" and depth == 0:
            return index
    return -1


def binder_sequence_from_declaration(declaration: object) -> list[dict[str, object]] | None:
    """Extract only top-level Lean binders from a generated declaration.

    The declaration spelling itself is never returned or used.  We stop at a
    top-level result-type colon or ``:=`` and hash the ordered binder kinds and
    canonical types.  An unsupported or malformed declaration has no usable
    sequence and therefore cannot receive regularity credit.
    """

    text = str(declaration or "")
    if not text.strip():
        return None
    body_index = text.find(":=")
    header = text if body_index < 0 else text[:body_index]
    sequence: list[dict[str, object]] = []
    index = 0
    top_level_colon_seen = False
    while index < len(header):
        char = header[index]
        if char == ":" and index + 1 < len(header) and header[index + 1] == "=":
            break
        if char == ":":
            # A colon outside a binder starts the declaration result type.
            top_level_colon_seen = True
            break
        if top_level_colon_seen:
            break
        if char not in "([{":
            index += 1
            continue
        end = _matching_delimiter(header, index)
        if end < 0:
            return None
        content = header[index + 1 : end].strip()
        colon = _top_level_colon_index(content)
        raw_type = content[colon + 1 :].strip() if colon >= 0 else content
        canonical = _canonical_type(raw_type)
        if not canonical:
            return None
        binder_info = {
            "(": "explicit",
            "[": "instanceImplicit",
            "{": "implicit",
        }[char]
        sequence.append(
            {
                "position": len(sequence),
                "binder_info": binder_info,
                "type": canonical,
            }
        )
        index = end + 1
    return sequence or None


def binder_sequence_sha256(sequence: list[dict[str, object]] | None) -> str:
    return canonical_digest(sequence) if sequence else ""


def _single_signature_sha256(item: Mapping[str, object]) -> str:
    raw = item.get("reviewed_elaborated_signature_identities")
    candidates: set[str] = set()
    if isinstance(raw, list):
        for value in raw:
            if isinstance(value, Mapping):
                digest = _sha256_text(value.get("elaborated_signature_sha256"))
                if digest:
                    candidates.add(digest)
    singular = item.get("reviewed_elaborated_signature_identity")
    if isinstance(singular, Mapping):
        digest = _sha256_text(singular.get("elaborated_signature_sha256"))
        if digest:
            candidates.add(digest)
    return next(iter(candidates)) if len(candidates) == 1 else ""


def _declaration_sha256(item: Mapping[str, object]) -> str:
    identity = item.get("reviewed_declaration_identity")
    return _sha256_text(identity.get("declaration_sha256")) if isinstance(identity, Mapping) else ""


def _declaration_text(item: Mapping[str, object]) -> str:
    values = {
        str(item.get(field) or "").strip()
        for field in ("effective_lean_source_declaration", "lean_source_declaration")
        if str(item.get(field) or "").strip()
    }
    return next(iter(values)) if len(values) == 1 else ""


def _raw_item_reuse_eligibility(item: Mapping[str, object]) -> Mapping[str, object] | None:
    value = item.get("source_record_item_reuse_eligibility")
    if not isinstance(value, Mapping):
        return None
    if value.get("eligible") is not False:
        return None
    blockers = value.get("blockers")
    if not isinstance(blockers, list) or "no source-content semantic identity" not in {
        str(blocker).strip() for blocker in blockers
    }:
        return None
    return value


def _has_direct_source_association(item: Mapping[str, object]) -> bool:
    return any(item.get(field) not in (None, {}, [], "") for field in _DIRECT_SOURCE_ASSOCIATION_FIELDS)


def _raw_structural_facts(
    item: Mapping[str, object],
    *,
    section: str,
    current_group_descriptor_sha256: str,
) -> tuple[dict[str, object] | None, str]:
    if section != "boundary_input_items":
        return None, "regularity may only target a boundary_input_items member"
    if str(item.get("kind") or "").strip() != "semantic_unknown_nondata_premise":
        return None, "regularity target is not semantic_unknown_nondata_premise"
    if str(item.get("result_relation") or "").strip():
        return None, "regularity target has a nonempty result_relation"
    if _has_direct_source_association(item):
        return None, "regularity target carries a direct source-contract or parent-route association"
    reuse = _raw_item_reuse_eligibility(item)
    if reuse is None:
        return None, "regularity target is not an aggregate-only no-source-identity input"
    declaration_sha = _declaration_sha256(item)
    signature_sha = _single_signature_sha256(item)
    sequence = binder_sequence_from_declaration(_declaration_text(item))
    sequence_sha = binder_sequence_sha256(sequence)
    canonical_type = _canonical_type(item.get("expanded_input_type"))
    if not declaration_sha or not signature_sha or not sequence_sha or not canonical_type:
        return None, "regularity target lacks a unique declaration/signature/binder/type structural identity"
    if not _sha256_text(current_group_descriptor_sha256):
        return None, "regularity target lacks a current generated group descriptor"
    return {
        "raw_item_kind": "semantic_unknown_nondata_premise",
        "result_relation": "",
        "declaration_sha256": declaration_sha,
        "elaborated_signature_sha256": signature_sha,
        "binder_sequence": sequence,
        "binder_sequence_sha256": sequence_sha,
        "canonical_type": canonical_type,
        "canonical_type_sha256": hashlib.sha256(
            canonical_type.encode("utf-8")
        ).hexdigest(),
        "current_group_descriptor_sha256": current_group_descriptor_sha256,
        "raw_item_reuse_eligibility": copy.deepcopy(dict(reuse)),
    }, ""


def _configured_row_structures(raw_audit: Mapping[str, object]) -> set[tuple[str, str]]:
    """Return generated configured-row structural signatures.

    The v10 raw payload still records configured rows by a presentation key.
    We use that only to read the generator's selected set, then discard it and
    match raw inputs by signature/binder-sequence structure.  No ledger entry
    contains or is selected through a row name.
    """

    selected = {
        str(value).strip()
        for value in raw_audit.get("semantic_model_configured_assumption_rows") or []
        if str(value).strip()
    }
    structures: set[tuple[str, str]] = set()
    rows = raw_audit.get("rows_with_semantic_inputs")
    if not selected or not isinstance(rows, list):
        return structures
    for row in rows:
        if not isinstance(row, Mapping) or str(row.get("row") or "").strip() not in selected:
            continue
        signature = _single_signature_sha256(row)
        sequence = binder_sequence_from_declaration(
            row.get("effective_lean_source_declaration") or row.get("lean_source_declaration")
        )
        sequence_sha = binder_sequence_sha256(sequence)
        if signature and sequence_sha:
            structures.add((signature, sequence_sha))
    return structures


def _source_anchor_errors(entry: Mapping[str, object], paper_dir: Path) -> tuple[list[dict[str, object]], list[str]]:
    anchors = entry.get("source_anchors")
    errors: list[str] = []
    verified: list[dict[str, object]] = []
    if not isinstance(anchors, list) or not anchors:
        return [], ["regularity entry needs a nonempty source_anchors list"]
    source_path = paper_dir / "source.txt"
    try:
        source_text = source_path.read_text(encoding="utf-8")
    except OSError:
        return [], ["paper source.txt is missing or unreadable"]
    # Match the canonical source-anchor convention: form-feed page markers are
    # source content, not line separators, and a final newline adds no fake
    # empty source line.
    lines = source_text.split("\n")
    if source_text.endswith("\n"):
        lines.pop()
    seen: set[tuple[int, int, str]] = set()
    for index, raw_anchor in enumerate(anchors):
        prefix = f"source_anchors[{index}]"
        if not isinstance(raw_anchor, Mapping):
            errors.append(f"{prefix} is not an object")
            continue
        path = str(raw_anchor.get("anchor_path") or "").strip()
        start = raw_anchor.get("line_start")
        end = raw_anchor.get("line_end")
        digest = _sha256_text(raw_anchor.get("quoted_text_sha256"))
        if path != "source.txt":
            errors.append(f"{prefix}.anchor_path must be source.txt")
            continue
        if not isinstance(start, int) or not isinstance(end, int) or start < 1 or end < start or end > len(lines):
            errors.append(f"{prefix}.line_start/line_end is outside source.txt")
            continue
        if not digest:
            errors.append(f"{prefix}.quoted_text_sha256 must be a SHA-256 digest")
            continue
        quote = "\n".join(lines[start - 1 : end])
        if hashlib.sha256(quote.encode("utf-8")).hexdigest() != digest:
            errors.append(f"{prefix}.quoted_text_sha256 does not match current source.txt lines")
            continue
        location = f"source.txt:{start}-{end}"
        if str(raw_anchor.get("source_location") or "").strip() != location:
            errors.append(f"{prefix}.source_location must equal {location}")
            continue
        coordinate = (start, end, digest)
        if coordinate in seen:
            errors.append(f"{prefix} duplicates a source anchor")
            continue
        seen.add(coordinate)
        # Deliberately omit source_item. It is navigation-only and cannot
        # influence which regularity or source condition is accepted.
        verified.append(
            {
                "anchor_path": path,
                "line_start": start,
                "line_end": end,
                "source_location": location,
                "quoted_text_sha256": digest,
            }
        )
    return verified, errors


def _entry_static_errors(
    entry: Mapping[str, object],
    *,
    paper_dir: Path,
) -> tuple[dict[str, object] | None, list[str]]:
    errors: list[str] = []
    entry_id = str(entry.get("entry_id") or "").strip()
    if not entry_id:
        errors.append("entry_id is required")
    if str(entry.get("raw_item_section") or "").strip() != "boundary_input_items":
        errors.append("raw_item_section must be boundary_input_items")
    if str(entry.get("raw_item_kind") or "").strip() != "semantic_unknown_nondata_premise":
        errors.append("raw_item_kind must be semantic_unknown_nondata_premise")
    scope = entry.get("scope_constraints")
    expected_scope = {
        "is_source_contract": False,
        "can_supply_direct_source_result_credit": False,
        "can_close_unrelated_boundary_inputs": False,
        "applies_only_to_exact_declaration_signature_and_binder_position": True,
        "name_matching_permitted": False,
    }
    if not isinstance(scope, Mapping):
        errors.append("scope_constraints must be an object")
    else:
        for field, expected in expected_scope.items():
            if scope.get(field) is not expected:
                errors.append(f"scope_constraints.{field} must be {str(expected).lower()}")
    if not str(entry.get("meaning") or "").strip():
        errors.append("meaning is required")
    if not str(entry.get("why_needed") or "").strip():
        errors.append("why_needed is required")
    declaration = entry.get("reviewed_declaration")
    if not isinstance(declaration, Mapping):
        errors.append("reviewed_declaration must be an object")
        declaration_sha = ""
        signature_sha = ""
    else:
        declaration_sha = _sha256_text(declaration.get("declaration_sha256"))
        signature_sha = _sha256_text(declaration.get("elaborated_signature_sha256"))
        if not declaration_sha:
            errors.append("reviewed_declaration.declaration_sha256 must be a SHA-256 digest")
        if not signature_sha:
            errors.append("reviewed_declaration.elaborated_signature_sha256 must be a SHA-256 digest")
    position = entry.get("structural_input_position")
    if not isinstance(position, Mapping):
        errors.append("structural_input_position must be an object")
        position_index = -1
        sequence_sha = ""
        position_type = ""
    else:
        position_index = position.get("binder_position_zero_based")
        sequence_sha = _sha256_text(position.get("binder_sequence_sha256"))
        position_type = _canonical_type(position.get("expanded_input_type"))
        if not isinstance(position_index, int) or position_index < 0:
            errors.append("structural_input_position.binder_position_zero_based must be a nonnegative integer")
        if str(position.get("binder_info") or "").strip() != "instanceImplicit":
            errors.append("structural_input_position.binder_info must be instanceImplicit")
        if not sequence_sha:
            errors.append("structural_input_position.binder_sequence_sha256 must be a SHA-256 digest")
        if not position_type:
            errors.append("structural_input_position.expanded_input_type is required")
    canonical_type = _canonical_type(entry.get("canonical_type"))
    type_sha = _sha256_text(entry.get("canonical_type_sha256"))
    if str(entry.get("canonical_type_digest_schema") or "").strip() != CANONICAL_TYPE_DIGEST_SCHEMA:
        errors.append("canonical_type_digest_schema is unsupported")
    if not canonical_type:
        errors.append("canonical_type is required")
    elif type_sha != hashlib.sha256(canonical_type.encode("utf-8")).hexdigest():
        errors.append("canonical_type_sha256 does not match canonical_type")
    if canonical_type and position_type and canonical_type != position_type:
        errors.append("canonical_type must equal structural_input_position.expanded_input_type")
    group_sha = _sha256_text(entry.get("source_record_current_group_descriptor_sha256"))
    if not group_sha:
        errors.append("source_record_current_group_descriptor_sha256 must be a SHA-256 digest")
    raw_reuse = entry.get("raw_item_reuse_eligibility")
    if not isinstance(raw_reuse, Mapping) or raw_reuse.get("eligible") is not False:
        errors.append("raw_item_reuse_eligibility must explicitly remain aggregate-only")
    verified_anchors, anchor_errors = _source_anchor_errors(entry, paper_dir)
    errors.extend(anchor_errors)
    if errors:
        return None, errors
    return {
        "entry_id": entry_id,
        "entry_sha256": configured_assumption_formalization_regularity_entry_sha256(
            entry
        ),
        "declaration_sha256": declaration_sha,
        "elaborated_signature_sha256": signature_sha,
        "binder_sequence_sha256": sequence_sha,
        "binder_position_zero_based": position_index,
        "canonical_type": canonical_type,
        "canonical_type_sha256": type_sha,
        "source_record_current_group_descriptor_sha256": group_sha,
        "raw_item_reuse_eligibility": copy.deepcopy(dict(raw_reuse)),
        "source_locations": frozenset(
            str(anchor["source_location"]) for anchor in verified_anchors
        ),
        "verified_source_anchors": verified_anchors,
        "complete_entry": copy.deepcopy(dict(entry)),
    }, []


def _current_group_descriptors(raw_audit: Mapping[str, object]) -> tuple[dict[int, str], list[str]]:
    """Obtain generated group descriptors without key-based matching.

    The differential helper's descriptor intentionally normalizes presentation
    fields.  Import it lazily: that module imports target-disposition helpers
    during startup, while this validator is only needed at runtime.
    """

    try:
        try:
            from scripts.source_record_obligation_groups import raw_source_record_obligation_groups
        except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
            from source_record_obligation_groups import raw_source_record_obligation_groups
        groups, group_errors = raw_source_record_obligation_groups(raw_audit)
    except Exception as exc:  # noqa: BLE001 - fail closed at an audit boundary.
        return {}, [f"could not reconstruct current raw-group descriptors: {exc}"]
    if group_errors:
        return {}, [
            "current raw audit has malformed response groups: "
            + ", ".join(sorted(str(key) for key in group_errors)[:5])
        ]
    by_item_id: dict[int, str] = {}
    errors: list[str] = []
    for group in groups.values():
        if not isinstance(group, Mapping):
            errors.append("current raw audit has a malformed response group")
            continue
        digest = _sha256_text(group.get("descriptor_sha256"))
        members = group.get("raw_members")
        if not digest or not isinstance(members, list):
            errors.append("current raw audit group lacks a descriptor digest or members")
            continue
        for member in members:
            if not isinstance(member, tuple) or len(member) != 2 or not isinstance(member[1], Mapping):
                errors.append("current raw audit group has a malformed member")
                continue
            prior = by_item_id.setdefault(id(member[1]), digest)
            if prior != digest:
                errors.append("one raw item belongs to incompatible current response groups")
    return by_item_id, errors


@dataclass(frozen=True)
class ResolvedConfiguredAssumptionFormalizationRegularity:
    """One exact structural raw input bound to one regularity ledger entry."""

    entry_id: str
    entry_sha256: str
    context_sha256: str
    source_locations: frozenset[str]
    structural_identity_sha256: str
    declaration_sha256: str
    elaborated_signature_sha256: str
    binder_sequence_sha256: str
    binder_position_zero_based: int
    canonical_type: str
    canonical_type_sha256: str
    current_group_descriptor_sha256: str


@dataclass(frozen=True)
class ConfiguredAssumptionFormalizationRegularityContext:
    """Authenticated regularity matches for one current raw source-record audit."""

    raw_audit_sha256: str
    matches_by_structural_identity: Mapping[str, ResolvedConfiguredAssumptionFormalizationRegularity]


def _raw_structural_identity(facts: Mapping[str, object], *, position: int) -> str:
    return canonical_digest(
        {
            "schema": CONTEXT_SCHEMA,
            "raw_item_kind": facts["raw_item_kind"],
            "result_relation": facts["result_relation"],
            "declaration_sha256": facts["declaration_sha256"],
            "elaborated_signature_sha256": facts["elaborated_signature_sha256"],
            "binder_sequence_sha256": facts["binder_sequence_sha256"],
            "binder_position_zero_based": position,
            "canonical_type_sha256": facts["canonical_type_sha256"],
            "current_group_descriptor_sha256": facts["current_group_descriptor_sha256"],
        }
    )


def _entry_matches_raw(
    entry: Mapping[str, object], facts: Mapping[str, object]
) -> tuple[str, str]:
    position = entry["binder_position_zero_based"]
    assert isinstance(position, int)
    sequence = facts.get("binder_sequence")
    if not isinstance(sequence, list) or position >= len(sequence):
        return "", "regularity binder position is absent from the current declaration"
    binder = sequence[position]
    if not isinstance(binder, Mapping) or binder.get("binder_info") != "instanceImplicit":
        return "", "regularity target is not an instance-implicit binder"
    comparisons = (
        ("declaration_sha256", facts.get("declaration_sha256")),
        ("elaborated_signature_sha256", facts.get("elaborated_signature_sha256")),
        ("binder_sequence_sha256", facts.get("binder_sequence_sha256")),
        ("canonical_type", facts.get("canonical_type")),
        ("canonical_type_sha256", facts.get("canonical_type_sha256")),
        (
            "source_record_current_group_descriptor_sha256",
            facts.get("current_group_descriptor_sha256"),
        ),
    )
    for field, actual in comparisons:
        if entry.get(field) != actual:
            return "", f"regularity {field} does not match the current structural input"
    if _canonical_type(binder.get("type")) != str(entry.get("canonical_type") or ""):
        return "", "regularity binder type does not match the current structural input"
    if canonical_digest(entry.get("raw_item_reuse_eligibility")) != canonical_digest(
        facts.get("raw_item_reuse_eligibility")
    ):
        return "", "regularity aggregate-only reuse eligibility does not match the current raw input"
    return _raw_structural_identity(facts, position=position), ""


def _entry_base_matches_raw(entry: Mapping[str, object], facts: Mapping[str, object]) -> bool:
    """Compare the name-independent input shape before its group receipt."""

    position = entry.get("binder_position_zero_based")
    sequence = facts.get("binder_sequence")
    if not isinstance(position, int) or not isinstance(sequence, list) or position >= len(sequence):
        return False
    binder = sequence[position]
    if not isinstance(binder, Mapping) or binder.get("binder_info") != "instanceImplicit":
        return False
    return (
        entry.get("declaration_sha256") == facts.get("declaration_sha256")
        and entry.get("elaborated_signature_sha256") == facts.get("elaborated_signature_sha256")
        and entry.get("binder_sequence_sha256") == facts.get("binder_sequence_sha256")
        and entry.get("canonical_type") == facts.get("canonical_type")
        and entry.get("canonical_type_sha256") == facts.get("canonical_type_sha256")
        and _canonical_type(binder.get("type")) == entry.get("canonical_type")
        and canonical_digest(entry.get("raw_item_reuse_eligibility"))
        == canonical_digest(facts.get("raw_item_reuse_eligibility"))
    )


def _ledger_path_error(status_payload: Mapping[str, object] | None) -> str:
    """Require an explicit top-level status declaration for this exceptional lane."""

    if not isinstance(status_payload, Mapping):
        return "status.json is missing or invalid for configured-assumption regularities"
    configured = status_payload.get(CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_STATUS_FIELD)
    if str(configured or "").strip() != CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE:
        return (
            "status.json."
            + CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_STATUS_FIELD
            + " must equal `"
            + CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE
            + "`"
        )
    return ""


def load_configured_assumption_formalization_regularity_context(
    paper_dir: Path | None,
    raw_audit: Mapping[str, object] | None,
    *,
    status_payload: Mapping[str, object] | None,
    ledger_bytes_override: bytes | None | object = _EXACT_INPUT_UNSET,
    source_artifact_sha256_override: str | None | object = _EXACT_INPUT_UNSET,
) -> tuple[ConfiguredAssumptionFormalizationRegularityContext | None, str]:
    """Load and structurally bind the paper-local regularity ledger.

    ``(None, "")`` means the paper does not opt into this lane.  A malformed
    opt-in ledger returns an explanatory error, but does not itself make an
    unrelated ordinary source-record response stale.
    """

    if paper_dir is None or not isinstance(raw_audit, Mapping):
        return None, "configured-assumption regularity context needs a paper directory and current raw audit"
    ledger_path = paper_dir / CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE
    configured = (
        status_payload.get(CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_STATUS_FIELD)
        if isinstance(status_payload, Mapping)
        else None
    )
    ledger_present = (
        ledger_path.exists()
        if ledger_bytes_override is _EXACT_INPUT_UNSET
        else isinstance(ledger_bytes_override, bytes)
    )
    if not ledger_present and not str(configured or "").strip():
        return None, ""
    if error := _ledger_path_error(status_payload):
        return None, error
    try:
        if ledger_bytes_override is _EXACT_INPUT_UNSET:
            ledger = json.loads(ledger_path.read_bytes())
        elif isinstance(ledger_bytes_override, bytes):
            ledger = json.loads(ledger_bytes_override)
        else:
            raise OSError("exact ledger snapshot is missing")
    except (OSError, json.JSONDecodeError, UnicodeDecodeError) as exc:
        return None, f"configured-assumption regularity ledger is missing or invalid: {exc}"
    if not isinstance(ledger, Mapping):
        return None, "configured-assumption regularity ledger must be an object"
    if ledger.get("schema") != CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_SCHEMA:
        return None, "configured-assumption regularity ledger has an unsupported schema"
    if str(ledger.get("artifact_kind") or "").strip() != CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_ARTIFACT_KIND:
        return None, "configured-assumption regularity ledger has the wrong artifact_kind"
    if str(ledger.get("status") or "").strip() != CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_STATUS:
        return None, "configured-assumption regularity ledger must have status current"
    if str(ledger.get("paper") or "").strip() != paper_dir.name:
        return None, "configured-assumption regularity ledger paper does not match its paper directory"
    receipt = ledger.get("raw_receipt")
    if not isinstance(receipt, Mapping):
        return None, "configured-assumption regularity ledger has no raw_receipt object"
    raw_audit_sha = _sha256_text(raw_audit.get("source_record_audit_sha256"))
    if not raw_audit_sha or _sha256_text(receipt.get("source_record_audit_sha256")) != raw_audit_sha:
        return None, "configured-assumption regularity ledger does not match the current raw source-record receipt"
    fingerprint = raw_audit.get("source_record_input_fingerprint")
    # Older raw-fingerprint schemas carried the policy version inside the
    # fingerprint.  Current raw receipts bind it at the receipt top level,
    # so prefer the fingerprint when present and otherwise use that canonical
    # receipt field.  A configured-regularity ledger still has to match one
    # exact current policy in either representation.
    policy = (
        str(fingerprint.get("source_record_policy_version") or "").strip()
        if isinstance(fingerprint, Mapping)
        else ""
    ) or str(raw_audit.get("source_record_policy_version") or "").strip()
    if not policy or str(receipt.get("source_record_policy_version") or "").strip() != policy:
        return None, "configured-assumption regularity ledger does not match the current raw source-record policy"
    if source_artifact_sha256_override is _EXACT_INPUT_UNSET:
        source_path = paper_dir / "source.txt"
        try:
            source_sha = hashlib.sha256(source_path.read_bytes()).hexdigest()
        except OSError:
            return None, "configured-assumption regularity source.txt is missing or unreadable"
    elif isinstance(source_artifact_sha256_override, str) and re.fullmatch(
        r"[0-9a-f]{64}", source_artifact_sha256_override
    ):
        source_sha = source_artifact_sha256_override
    else:
        return None, "configured-assumption regularity source.txt exact snapshot is missing or unreadable"
    if _sha256_text(receipt.get("source_artifact_sha256")) != source_sha:
        return None, "configured-assumption regularity ledger does not match current source.txt bytes"
    entries = ledger.get("entries")
    if not isinstance(entries, list) or not entries:
        return None, "configured-assumption regularity ledger needs a nonempty entries list"
    configured_structures = _configured_row_structures(raw_audit)
    if not configured_structures:
        return None, "current raw audit has no structurally readable configured-assumption rows"
    group_descriptors, group_errors = _current_group_descriptors(raw_audit)
    if group_errors:
        return None, "; ".join(group_errors)
    raw_items = raw_audit.get("boundary_input_items")
    if not isinstance(raw_items, list):
        return None, "current raw audit has no boundary_input_items list"
    raw_candidates: list[tuple[Mapping[str, object], dict[str, object]]] = []
    for raw_item in raw_items:
        if not isinstance(raw_item, Mapping):
            continue
        facts, _ = _raw_structural_facts(
            raw_item,
            section="boundary_input_items",
            current_group_descriptor_sha256=group_descriptors.get(id(raw_item), ""),
        )
        if facts is None:
            continue
        signature = str(facts["elaborated_signature_sha256"])
        sequence_sha = str(facts["binder_sequence_sha256"])
        if (signature, sequence_sha) not in configured_structures:
            continue
        raw_candidates.append((raw_item, facts))
    resolved: dict[str, ResolvedConfiguredAssumptionFormalizationRegularity] = {}
    used_structural_ids: set[str] = set()
    entry_ids: set[str] = set()
    for index, raw_entry in enumerate(entries):
        if not isinstance(raw_entry, Mapping):
            return None, f"entries[{index}] is not an object"
        entry, errors = _entry_static_errors(raw_entry, paper_dir=paper_dir)
        if errors or entry is None:
            return None, f"entries[{index}] is invalid: " + "; ".join(errors)
        entry_id = str(entry["entry_id"])
        if entry_id in entry_ids:
            return None, f"entries contains duplicate entry_id `{entry_id}`"
        entry_ids.add(entry_id)
        base_matches: list[tuple[Mapping[str, object], dict[str, object]]] = []
        matches: list[tuple[Mapping[str, object], dict[str, object], str]] = []
        mismatch_reasons: list[str] = []
        for raw_item, facts in raw_candidates:
            if _entry_base_matches_raw(entry, facts):
                base_matches.append((raw_item, facts))
            structural_identity, mismatch = _entry_matches_raw(entry, facts)
            if structural_identity:
                matches.append((raw_item, facts, structural_identity))
            elif mismatch:
                mismatch_reasons.append(mismatch)
        if len(base_matches) != 1:
            return None, (
                f"regularity `{entry_id}` has {len(base_matches)} inputs with the same "
                "declaration/signature/binder/type shape; a group receipt cannot "
                "disambiguate presentation-identical inputs"
            )
        if len(matches) != 1:
            if not matches and mismatch_reasons:
                detail = sorted(set(mismatch_reasons))[0]
                return None, f"regularity `{entry_id}` has no exact current structural input: {detail}"
            return None, f"regularity `{entry_id}` has {len(matches)} matching current structural inputs"
        _raw_item, facts, structural_identity = matches[0]
        if structural_identity in used_structural_ids:
            return None, "multiple regularity entries target one current structural input"
        used_structural_ids.add(structural_identity)
        context_sha = canonical_digest(
            {
                "schema": CONTEXT_SCHEMA,
                "regularity_entry_sha256": entry["entry_sha256"],
                "raw_receipt": {
                    "source_record_audit_sha256": raw_audit_sha,
                    "source_record_policy_version": policy,
                    "source_artifact_sha256": source_sha,
                },
                "current_group_descriptor_sha256": facts[
                    "current_group_descriptor_sha256"
                ],
                "structural_identity_sha256": structural_identity,
                "verified_source_anchors": entry["verified_source_anchors"],
            }
        )
        resolved[structural_identity] = ResolvedConfiguredAssumptionFormalizationRegularity(
            entry_id=entry_id,
            entry_sha256=str(entry["entry_sha256"]),
            context_sha256=context_sha,
            source_locations=entry["source_locations"],
            structural_identity_sha256=structural_identity,
            declaration_sha256=str(entry["declaration_sha256"]),
            elaborated_signature_sha256=str(entry["elaborated_signature_sha256"]),
            binder_sequence_sha256=str(entry["binder_sequence_sha256"]),
            binder_position_zero_based=int(entry["binder_position_zero_based"]),
            canonical_type=str(entry["canonical_type"]),
            canonical_type_sha256=str(entry["canonical_type_sha256"]),
            current_group_descriptor_sha256=str(
                entry["source_record_current_group_descriptor_sha256"]
            ),
        )
    return ConfiguredAssumptionFormalizationRegularityContext(
        raw_audit_sha256=raw_audit_sha,
        matches_by_structural_identity=resolved,
    ), ""


def response_claims_configured_assumption_formalization_regularity(
    response: Mapping[str, object]
) -> bool:
    return (
        str(response.get("classification") or "").strip()
        == FORMALIZATION_REGULARITY_CLASSIFICATION
        or any(
        field in response
        for field in (
            CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_ID_FIELD,
            CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_SHA256_FIELD,
            CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_CONTEXT_SHA256_FIELD,
        )
        )
    )


def _raw_member_matches_regularities(
    raw_members: object,
    regularity: ResolvedConfiguredAssumptionFormalizationRegularity,
) -> tuple[bool, str]:
    """Confirm an exact ledger regularity occurs in this raw response group.

    Context construction has already checked the exact generated group digest
    against the current raw audit.  Here we only need to ensure that the group
    handed to the response loader contains that one structural input.  The
    context rejects presentation-identical duplicate inputs, so no key or
    declaration spelling is needed to resolve it.
    """

    if not isinstance(raw_members, list):
        return False, "current raw group members are missing"
    matches = 0
    for member in raw_members:
        if not isinstance(member, tuple) or len(member) != 2:
            return False, "current raw group contains a malformed member"
        section, item = member
        if not isinstance(section, str) or not isinstance(item, Mapping):
            return False, "current raw group contains a malformed member"
        if section == "boundary_input_items" and _item_matches_regularity(item, regularity):
            matches += 1
    if matches != 1:
        return False, (
            "current raw group has "
            + str(matches)
            + " matching configured-assumption structural inputs"
        )
    return True, ""


def _item_matches_regularity(
    item: Mapping[str, object],
    regularity: ResolvedConfiguredAssumptionFormalizationRegularity,
) -> bool:
    """Compare an input to a resolved regularity without presentation fields."""

    if (
        str(item.get("kind") or "").strip() != "semantic_unknown_nondata_premise"
        or str(item.get("result_relation") or "").strip()
        or _has_direct_source_association(item)
        or _raw_item_reuse_eligibility(item) is None
        or _declaration_sha256(item) != regularity.declaration_sha256
        or _single_signature_sha256(item) != regularity.elaborated_signature_sha256
    ):
        return False
    sequence = binder_sequence_from_declaration(_declaration_text(item))
    position = regularity.binder_position_zero_based
    if (
        binder_sequence_sha256(sequence) != regularity.binder_sequence_sha256
        or not isinstance(sequence, list)
        or position >= len(sequence)
    ):
        return False
    binder = sequence[position]
    canonical_type = _canonical_type(item.get("expanded_input_type"))
    return (
        isinstance(binder, Mapping)
        and binder.get("binder_info") == "instanceImplicit"
        and canonical_type == regularity.canonical_type
        and hashlib.sha256(canonical_type.encode("utf-8")).hexdigest()
        == regularity.canonical_type_sha256
        and _canonical_type(binder.get("type")) == regularity.canonical_type
    )


def project_configured_assumption_formalization_regularity_pin(
    raw_members: object,
    response: Mapping[str, object],
    *,
    context: ConfiguredAssumptionFormalizationRegularityContext | None,
    reject_existing: bool = False,
) -> tuple[dict[str, object] | None, str]:
    """Inject the current regularity context pin into a claimed response.

    A reviewer confirms the name-free semantic entry digest, but cannot
    serialize or invent the current context pin.  The pin is derived from the
    semantic entry projection, current raw receipt/group, and byte-checked
    source anchors.  A current entry id is normalized only as navigation text.
    """

    if not isinstance(response, Mapping):
        return None, "response is not an object"
    if not response_claims_configured_assumption_formalization_regularity(response):
        return copy.deepcopy(dict(response)), ""
    if context is None:
        return None, "configured-assumption regularity response has no current regularity context"
    supplied_entry_sha = _sha256_text(
        response.get(CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_SHA256_FIELD)
    )
    if not supplied_entry_sha:
        return None, "configured-assumption regularity response needs the exact semantic regularity entry digest"
    candidates = [
        match
        for match in context.matches_by_structural_identity.values()
        if match.entry_sha256 == supplied_entry_sha
    ]
    if len(candidates) != 1:
        return None, "configured-assumption regularity digest does not name one current structural entry"
    match = candidates[0]
    # Confirm the response group actually contains the same exact structural
    # item. We compare this through full candidate facts reconstructed below;
    # raw names and source labels do not participate.
    member_matches, member_error = _raw_member_matches_regularities(raw_members, match)
    if member_error or not member_matches:
        return None, member_error or "regularity entry does not match the current raw group"
    projected = copy.deepcopy(dict(response))
    supplied_context = projected.get(
        CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_CONTEXT_SHA256_FIELD
    )
    if supplied_context is not None:
        if reject_existing:
            return None, "response must not carry a reviewer-supplied configured-assumption regularity context pin"
        if _sha256_text(supplied_context) != match.context_sha256:
            return None, "configured-assumption regularity context pin conflicts with the current raw receipt/entry"
    # ``entry_id`` is reviewer navigation text, not part of matching.  Normalize
    # it after structural selection so a ledger-label rename cannot stale an
    # otherwise current response.
    projected[CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_ID_FIELD] = match.entry_id
    projected[CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_CONTEXT_SHA256_FIELD] = match.context_sha256
    return projected, ""


def configured_assumption_formalization_regularity_response_errors(
    item: Mapping[str, object],
    response: Mapping[str, object],
    *,
    context: ConfiguredAssumptionFormalizationRegularityContext | None,
) -> list[str]:
    """Validate a projected structural-regularity response.

    The current target item alone cannot reconstruct the group descriptor
    without the raw payload.  Consequently this deliberately requires the
    generated context pin injected by the current response loader; a manually
    authored pin is rejected by that loader's ``reject_existing`` mode.
    """

    errors: list[str] = []
    if str(response.get("classification") or "").strip() != FORMALIZATION_REGULARITY_CLASSIFICATION:
        return [
            "configured-assumption regularity must be classified "
            + FORMALIZATION_REGULARITY_CLASSIFICATION
        ]
    if context is None:
        errors.append("configured-assumption regularity has no current authenticated regularity context")
        return errors
    entry_sha = _sha256_text(
        response.get(CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_SHA256_FIELD)
    )
    context_sha = _sha256_text(
        response.get(CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_CONTEXT_SHA256_FIELD)
    )
    matches = [
        match
        for match in context.matches_by_structural_identity.values()
        if match.entry_sha256 == entry_sha
        and match.context_sha256 == context_sha
    ]
    if len(matches) != 1:
        errors.append("configured-assumption regularity digest/context pin is not current")
        return errors
    match = matches[0]
    if not _item_matches_regularity(item, match):
        errors.append(
            "configured-assumption regularity context pin does not match this "
            "structural input"
        )
    location = str(response.get("source_location") or response.get("source_evidence") or "").strip()
    if location not in match.source_locations:
        errors.append("configured-assumption regularity source location must equal one verified ledger source anchor")
    for field in sorted(_FORBIDDEN_RESPONSE_FIELDS):
        if response.get(field) not in (None, "", [], {}):
            errors.append(
                "configured-assumption regularity cannot carry direct-source, model-convention, or corrected-target field `"
                + field
                + "`"
            )
    if _has_direct_source_association(item):
        errors.append("configured-assumption regularity cannot target an item with a direct source association")
    if str(item.get("kind") or "").strip() != "semantic_unknown_nondata_premise":
        errors.append("configured-assumption regularity cannot target a non-structural input")
    if str(item.get("result_relation") or "").strip():
        errors.append("configured-assumption regularity cannot target an input related to a result")
    return errors


def configured_assumption_formalization_regularity_is_direct_source_credit(
    response: Mapping[str, object]
) -> bool:
    """Always false: exposed to make provenance callers state the boundary."""

    del response
    return False
