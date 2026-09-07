#!/usr/bin/env python3
"""Typed, location-neutral input surface for the final holistic source audit.

The final adversarial reread is a semantic review, not an operational build
receipt.  This module keeps two deliberately separate identities:

* the complete source inventory and selected semantic-review material that an
  independent reviewer must actually consider; and
* the complete source-inventory, correction, defect, fidelity, and status
  controls that the closeout transaction must validate.

The final-audit binding includes the source corpus and inventory, not just the
claims selected by intake. Otherwise a mistaken omission, alias, or scope
classification could reuse the very review meant to challenge it. A changed
inventory invalidates that final scope attestation, not the separate unchanged
item judgments or Lean graph. This module projects the already validated v11
source/Lean transaction onto the material that reviewer must have considered:

* the complete content-pinned source corpus and reviewed source inventory;
* every source item and source-claim atom used by a typed source-facing route
  or semantically material prerequisite, together with the complete reviewed
  inventory (including the dispositions of unselected presentations);
* the exact source connection and Lean-owned semantic identity for each Spec,
  paper prerequisite, and reusable-library prerequisite; and
* the Lean-checked Spec-to-proof relation and its axiom boundary.

Declaration names, module paths, source ranges, pretty-printed Lean text,
proof bodies, compiled artifacts, renderer bytes, and closeout scheduling data
are navigation or operational inputs.  They are intentionally absent.  A
pure move or rename can therefore retain a completed holistic audit when Lean
reproduces the same canonical semantic identities, while any source, route,
claim-atom, corrected-target, premise, conclusion, prerequisite, or proof-
contract change produces a different surface.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from collections.abc import Iterable, Mapping
from pathlib import Path
from typing import Any

# Preserve canonical package imports under both `python -m scripts...` and
# direct script entrypoints reached transitively by the public CLI.
if __package__ in {None, ""}:
    repository_root = str(Path(__file__).resolve().parents[1])
    if repository_root not in sys.path:
        sys.path.insert(0, repository_root)

from scripts.lean_review_surface import semantic_review_display_surface_from_inventory
from scripts.formalization_protocol import (
    CLOSEOUT_REPEAT_SCOPE_ALL_SELECTED,
    FormalizationProtocolError,
    closeout_review_policy_assurance_projection,
    closeout_review_policy_material_projection,
    closeout_review_policy_scheduling_projection,
    explicit_closeout_review_policy_from_source_map,
)
from scripts.corrected_target_identity import (
    CORRECTED_TARGET_REVIEW_PROTOCOL,
    corrected_target_review_digest,
)
from scripts.closeout_status_projection import (
    CloseoutStatusProjectionError,
    paper_status_assurance_control_projection,
)
from scripts.obligation_evidence_contracts import (
    TERMINAL_SOURCE_ASSURANCE_V2_CONTRACT,
)
from scripts.obligation_routes import EvidenceRouteSet, ObligationRouteError
from scripts.semantic_prerequisite_projection import (
    LIBRARY_SEMANTIC_REVIEW_SCHEMA,
    LIBRARY_SEMANTIC_TARGET_PROTOCOL,
    PAPER_PREREQUISITE_PROMPT_VERSION,
    PAPER_PREREQUISITE_SCHEMA,
    PAPER_PREREQUISITE_TARGET_PROTOCOL,
    REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,
    selected_library_semantic_prerequisite_targets,
    selected_paper_semantic_prerequisite_targets,
)
from scripts.source_claim_atom_schema import source_claim_atoms_semantic_sha256
from scripts.source_coverage_scope import (
    source_coverage_mode_from_map,
    source_item_coverage_sha256,
    source_prose_definition_presentation_sha256,
)
from scripts.source_proof_fidelity_semantics import (
    source_proof_fidelity_semantic_projection,
)
from scripts.source_review_input import source_semantic_input_bundle
from scripts.source_review_scope import (
    CANDIDATE_PRESENTATION_REGIONS_FIELD,
    PROSE_DEFINITION_PRESENTATION_REGIONS_FIELD,
    SourceReviewScopeError,
    primary_source_region_projection,
    selected_terminal_source_item_ids,
    source_region_partition_projection,
)
from scripts.v11_screening_contract import (
    V11_SCREENING_PROMPT_VERSION,
    V11_SCREENING_SCHEMA,
    validate_v11_screening_container,
)

FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA = 2
FINAL_HOLISTIC_AUDIT_SURFACE_IDENTITY_SCHEMA = (
    "final-holistic-source-and-lean-semantic-surface-v2"
)
POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA = 3
POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_IDENTITY_SCHEMA = (
    "final-holistic-policy-aware-source-and-lean-semantic-surface-v3"
)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
TERMINAL_SOURCE_ASSURANCE_V2_SCHEMA = 2
TERMINAL_SOURCE_ASSURANCE_V2_IDENTITY_SCHEMA = (
    "terminal-source-inventory-and-status-control-assurance-v2"
)
SOURCE_TO_SPEC_PASS_JUDGMENTS = frozenset(
    {"matches", "matches_approved_corrected_target"}
)
APPROVED_CORRECTED_TARGET_MATCH = "matches_approved_corrected_target"


class FinalHolisticAuditSurfaceError(ValueError):
    """The final holistic surface is missing, malformed, or not current."""


def _digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


FINAL_HOLISTIC_AUDIT_REVIEW_IDENTITY_SCHEMA = (
    "final-holistic-source-inventory-and-semantic-review-material-v2"
)
POLICY_AWARE_FINAL_HOLISTIC_AUDIT_REVIEW_IDENTITY_SCHEMA = (
    "final-holistic-policy-aware-review-material-v3"
)


def final_holistic_audit_surface_contract_is_supported(
    surface: Mapping[str, object],
) -> bool:
    """Recognize only the exact historical or policy-aware surface contract."""

    return (
        surface.get("schema"),
        surface.get("identity_schema"),
    ) in {
        (
            FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA,
            FINAL_HOLISTIC_AUDIT_SURFACE_IDENTITY_SCHEMA,
        ),
        (
            POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA,
            POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_IDENTITY_SCHEMA,
        ),
    }


def final_holistic_audit_review_material_projection(
    surface: Mapping[str, object],
) -> dict[str, object]:
    """Return precisely the material read by the terminal semantic reviewer.

    Source-only coverage and classification judgments are part of the final
    review, even when they exclude an item from the Lean comparison rows.
    Machine source assurance cannot substitute for that independent scope
    challenge. Operational scheduling and presentation remain excluded.
    """

    legacy_required = {
        "schema",
        "identity_schema",
        "paper",
        "source_coverage_mode",
        "source_corpus",
        "source_inventory",
        "semantic_review_rows",
        "status_semantics",
        "source_proof_fidelity_semantics",
    }
    policy_required = {
        "schema",
        "identity_schema",
        "paper",
        "source_coverage_mode",
        "source_corpus",
        "source_inventory",
        "status_semantics",
        "source_proof_fidelity_semantics",
        "review_policy_assurance",
        "review_policy_scheduling",
        "source_region_partition",
        "terminal_review",
    }
    if set(surface) == policy_required:
        if (
            surface.get("schema")
            != POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA
            or surface.get("identity_schema")
            != POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_IDENTITY_SCHEMA
        ):
            raise FinalHolisticAuditSurfaceError(
                "policy-aware final holistic surface identity is malformed"
            )
        paper = str(surface.get("paper") or "").strip()
        mode = str(surface.get("source_coverage_mode") or "").strip()
        terminal = surface.get("terminal_review")
        if (
            not paper
            or not mode
            or not isinstance(terminal, Mapping)
            or set(terminal)
            != {
                "review_policy_material",
                "source_regions",
                "source_inventory",
                "semantic_review_rows",
            }
            or not isinstance(terminal.get("semantic_review_rows"), list)
        ):
            raise FinalHolisticAuditSurfaceError(
                "policy-aware terminal semantic-review material is malformed"
            )
        return {
            "schema": POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA,
            "identity_schema": (
                POLICY_AWARE_FINAL_HOLISTIC_AUDIT_REVIEW_IDENTITY_SCHEMA
            ),
            "paper": paper,
            "source_coverage_mode": mode,
            **dict(terminal),
        }
    if set(surface) != legacy_required:
        raise FinalHolisticAuditSurfaceError(
            "final holistic surface fields are malformed"
        )
    if (
        surface.get("schema") != FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA
        or surface.get("identity_schema")
        != FINAL_HOLISTIC_AUDIT_SURFACE_IDENTITY_SCHEMA
    ):
        raise FinalHolisticAuditSurfaceError(
            "final holistic surface identity is malformed"
        )
    paper = str(surface.get("paper") or "").strip()
    mode = str(surface.get("source_coverage_mode") or "").strip()
    rows = surface.get("semantic_review_rows")
    if not paper or not mode or not isinstance(rows, list):
        raise FinalHolisticAuditSurfaceError(
            "final holistic semantic-review material is malformed"
        )
    return {
        "schema": 2,
        "identity_schema": FINAL_HOLISTIC_AUDIT_REVIEW_IDENTITY_SCHEMA,
        "paper": paper,
        "source_coverage_mode": mode,
        "source_corpus": surface["source_corpus"],
        "source_inventory": surface["source_inventory"],
        "semantic_review_rows": rows,
    }


def final_holistic_audit_surface_sha256(surface: Mapping[str, object]) -> str:
    """Return the identity bound to the independent final semantic review.

    This prospective identity binds the source-only omission/scope challenge
    as well as the selected Lean comparisons. Historical credentials retain
    their recorded reviewer identity; changing this producer does not rewrite
    those reports or assert that a new independent review took place.
    """

    return _digest(final_holistic_audit_review_material_projection(surface))


def _sha256(value: object, *, label: str) -> str:
    digest = str(value or "").strip().lower()
    if not SHA256_RE.fullmatch(digest):
        raise FinalHolisticAuditSurfaceError(f"{label} is not a SHA-256 digest")
    return digest


def _load_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise FinalHolisticAuditSurfaceError(
            f"could not read {label}: {exc}"
        ) from exc
    if not isinstance(value, Mapping):
        raise FinalHolisticAuditSurfaceError(f"{label} is not an object")
    return dict(value)


def _load_optional_object(path: Path, *, label: str) -> dict[str, Any] | None:
    if not path.is_file():
        return None
    return _load_object(path, label=label)


def _section_declarations(
    inventory: Mapping[str, Any], section_name: str, field: str
) -> tuple[str, ...]:
    section = inventory.get(section_name)
    rows = section.get("items") if isinstance(section, Mapping) else None
    if not isinstance(rows, list):
        raise FinalHolisticAuditSurfaceError(
            f"Lean graph has malformed {section_name}"
        )
    names: list[str] = []
    for row in rows:
        name = str(row.get(field) or "").strip() if isinstance(row, Mapping) else ""
        if not name or name in names:
            raise FinalHolisticAuditSurfaceError(
                f"Lean graph has a blank or duplicate {section_name} declaration"
            )
        names.append(name)
    return tuple(sorted(names))


def _collect_content_sha256s(value: object) -> set[str]:
    """Collect content hashes without retaining path/extraction coordinates."""

    result: set[str] = set()
    if isinstance(value, Mapping):
        for raw_key, child in value.items():
            key = str(raw_key).strip().lower()
            if key.endswith("sha256") and isinstance(child, str):
                digest = child.strip().lower()
                if SHA256_RE.fullmatch(digest):
                    result.add(digest)
                    continue
            result.update(_collect_content_sha256s(child))
    elif isinstance(value, (list, tuple)):
        for child in value:
            result.update(_collect_content_sha256s(child))
    return result


def _source_corpus_projection(source_map: Mapping[str, Any]) -> dict[str, Any]:
    canonical = _sha256(
        source_map.get("source_artifact_sha256"),
        label="canonical source artifact",
    )
    digests = {canonical}
    for field in (
        "source_archive_sha256",
        "extracted_tex_sha256",
        "source_text_companion",
        "source_archive_surface",
    ):
        if field in source_map:
            digests.update(_collect_content_sha256s(source_map[field]))
    return {
        "canonical_source_sha256": canonical,
        "source_corpus_sha256s": sorted(digests),
    }


def _anchor_quote_sha256(raw: object, *, label: str) -> str:
    if not isinstance(raw, Mapping):
        raise FinalHolisticAuditSurfaceError(f"{label} has no source anchor")
    quote = raw.get("quoted_text")
    recorded = _sha256(raw.get("quoted_text_sha256"), label=f"{label} quote")
    if not isinstance(quote, str) or not quote:
        raise FinalHolisticAuditSurfaceError(f"{label} has no source quote")
    normalized = quote.replace("\r\n", "\n").replace("\r", "\n")
    if hashlib.sha256(normalized.encode("utf-8")).hexdigest() != recorded:
        raise FinalHolisticAuditSurfaceError(f"{label} source quote digest is stale")
    return recorded


def _named_inventory_projection(
    source_map: Mapping[str, Any],
    *,
    candidate_ids: frozenset[str] | None = None,
    prose_presentation_sha256s: frozenset[str] | None = None,
) -> dict[str, Any]:
    review = source_map.get("source_named_result_inventory_review")
    if not isinstance(review, Mapping) or review.get("complete") is not True:
        raise FinalHolisticAuditSurfaceError(
            "source map lacks a complete named-result inventory review"
        )
    source_sha = _sha256(
        review.get("source_artifact_sha256"),
        label="named-result inventory source artifact",
    )
    if source_sha != _sha256(
        source_map.get("source_artifact_sha256"),
        label="canonical source artifact",
    ):
        raise FinalHolisticAuditSurfaceError(
            "named-result inventory is not bound to the canonical source artifact"
        )
    raw_candidates = review.get("candidate_presentations")
    raw_definitions = review.get("prose_definition_presentations")
    if not isinstance(raw_candidates, list) or not isinstance(raw_definitions, list):
        raise FinalHolisticAuditSurfaceError(
            "named-result inventory needs explicit candidate and prose-definition lists"
        )
    candidates: list[dict[str, Any]] = []
    for index, raw in enumerate(raw_candidates):
        if not isinstance(raw, Mapping):
            raise FinalHolisticAuditSurfaceError(
                f"candidate presentation {index} is malformed"
            )
        candidate_id = str(raw.get("id") or "").strip()
        visible_kind = str(raw.get("visible_kind") or "").strip()
        disposition = str(raw.get("scope_disposition") or "").strip()
        if not candidate_id or not visible_kind or not disposition:
            raise FinalHolisticAuditSurfaceError(
                f"candidate presentation {index} is incomplete"
            )
        if candidate_ids is not None and candidate_id not in candidate_ids:
            continue
        candidates.append(
            {
                "visible_kind": visible_kind,
                "scope_disposition": disposition,
                "presentation_label_sha256": _digest(
                    str(raw.get("presentation_label") or "").strip()
                ),
                "semantic_basis_sha256": _digest(
                    str(raw.get("semantic_basis") or "").strip()
                ),
                "discovery_basis": str(raw.get("discovery_basis") or "").strip(),
                "source_quote_sha256": _anchor_quote_sha256(
                    raw.get("source_anchor"), label=f"candidate {candidate_id}"
                ),
            }
        )
    definitions: list[dict[str, Any]] = []
    for index, raw in enumerate(raw_definitions):
        if not isinstance(raw, Mapping):
            raise FinalHolisticAuditSurfaceError(
                f"prose-definition presentation {index} is malformed"
            )
        if (
            prose_presentation_sha256s is not None
            and source_prose_definition_presentation_sha256(raw)
            not in prose_presentation_sha256s
        ):
            continue
        definition = {
            "presentation_kind": str(raw.get("presentation_kind") or "").strip(),
            "defined_entity_kind": str(raw.get("defined_entity_kind") or "").strip(),
            "defined_object": str(raw.get("defined_object") or "").strip(),
            "definitional_clause_sha256": _digest(
                str(raw.get("definitional_clause") or "").strip()
            ),
            "scope_disposition": str(raw.get("scope_disposition") or "").strip(),
            "source_quote_sha256": _anchor_quote_sha256(
                raw.get("source_anchor"),
                label=f"prose-definition presentation {index}",
            ),
        }
        if any(not value for value in definition.values()):
            raise FinalHolisticAuditSurfaceError(
                f"prose-definition presentation {index} is incomplete"
            )
        for field in (
            "canonical_presentation_sha256",
            "repetition_judgment",
            "repetition_judgment_source_sha256",
            "scope_judgment",
            "scope_judgment_source_sha256",
            "user_approved_scope_exclusion",
        ):
            if raw.get(field) is not None:
                definition[field] = raw[field]
        for field in ("scope_reason", "semantic_basis"):
            if raw.get(field) is not None:
                definition[f"{field}_sha256"] = _digest(
                    str(raw.get(field) or "").strip()
                )
        definitions.append(definition)
    return {
        "complete": True,
        "candidate_presentations": sorted(candidates, key=_digest),
        "prose_definition_presentations": sorted(definitions, key=_digest),
    }


def _source_scope_relations_projection(
    source_map: Mapping[str, Any],
    mode: str,
    *,
    required_source_item_ids: frozenset[str] | None = None,
) -> list[dict[str, object]]:
    """Bind every source disposition and its content-addressed relation endpoints.

    Unlike selected Lean comparisons, source-only scope review needs no clean
    extraction bundle. The shared source-semantic projector retains unknown
    annotations while dropping navigation. Alias and subsumption references
    are represented by endpoint content, never by source-map keys.
    """

    from scripts import source_coverage_scope as scope

    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping) or not raw_items or any(
        not isinstance(key, str) or not key or key != key.strip()
        or not isinstance(item, dict)
        for key, item in raw_items.items()
    ):
        raise FinalHolisticAuditSurfaceError("source scope inventory is malformed")
    aliases, errors = scope.source_presentation_aliases(dict(raw_items))
    if errors:
        raise FinalHolisticAuditSurfaceError("; ".join(errors))
    identities: dict[str, str] = {}
    references: dict[str, dict[str, str]] = {}
    for key, item in raw_items.items():
        material = dict(item)
        references[key] = {}
        if key in aliases:
            relation = dict(material[scope.SOURCE_PRESENTATION_ALIAS_FIELD])
            relation.pop("canonical_source_item")
            evidence_field = scope.SOURCE_PRESENTATION_ALIAS_RENUMBERED_EVIDENCE_FIELD
            if evidence_field in relation:
                relation[evidence_field] = scope._source_anchor_semantic_projection(
                    relation[evidence_field]
                )
            material[scope.SOURCE_PRESENTATION_ALIAS_FIELD] = relation
            references[key]["presentation_alias"] = aliases[key]
        if "subsumed_by_source_item" in material:
            target = material.pop("subsumed_by_source_item")
            if not isinstance(target, str) or target not in raw_items or target == key:
                raise FinalHolisticAuditSurfaceError(
                    f"{key}: subsumption target is not another source item"
                )
            references[key]["subsumed_by_selected_result"] = target
        identities[key] = source_item_coverage_sha256(material, mode)
    return sorted(
        (
            {
                "source_item_semantic_sha256": identities[key],
                "relations": {
                    relation: identities[target]
                    for relation, target in references[key].items()
                },
            }
            for key in raw_items
            if required_source_item_ids is None or key in required_source_item_ids
        ),
        key=_digest,
    )


def _source_item_facts(
    source_map: Mapping[str, Any],
    mode: str,
    *,
    required_source_item_ids: Iterable[str],
) -> dict[str, dict[str, Any]]:
    """Project only source records that actually enter semantic review.

    Source-only scope material is bound separately, but a deep-audit-only or
    support-only record is not itself a source-to-Lean target. Requiring its
    PDF-text extraction to be a valid semantic-review
    input would turn transcription noise in an unselected observation into a
    closeout blocker.  The graph instead binds exact source inputs for every
    direct claim and every prerequisite judgment that the final reviewer must
    assess.
    """

    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping) or not raw_items:
        raise FinalHolisticAuditSurfaceError("source map has no item inventory")
    required = {
        str(raw_id).strip()
        for raw_id in required_source_item_ids
        if str(raw_id).strip()
    }
    facts: dict[str, dict[str, Any]] = {}
    for raw_key in sorted(raw_items, key=str):
        key = str(raw_key).strip()
        raw = raw_items[raw_key]
        if not key or key in facts or not isinstance(raw, Mapping):
            raise FinalHolisticAuditSurfaceError(
                "source map has a blank, duplicate, or malformed item"
            )
        if key not in required:
            continue
        _source_text, bundle, error = source_semantic_input_bundle(
            raw, require_context_roles=True
        )
        if error:
            raise FinalHolisticAuditSurfaceError(f"{key}: {error}")
        semantic = source_item_coverage_sha256(dict(raw), mode)
        if not SHA256_RE.fullmatch(semantic):
            raise FinalHolisticAuditSurfaceError(
                f"{key}: source semantic identity is unavailable"
            )
        atoms = ""
        if raw.get("source_claim_atoms") is not None:
            atoms = source_claim_atoms_semantic_sha256(raw.get("source_claim_atoms"))
            if not SHA256_RE.fullmatch(atoms):
                raise FinalHolisticAuditSurfaceError(
                    f"{key}: source claim atoms are malformed"
                )
        raw_defect_ids = raw.get("source_defect_ids")
        if raw_defect_ids is None:
            defect_ids: list[str] = []
        elif not isinstance(raw_defect_ids, list) or any(
            not isinstance(value, str) or not value.strip()
            for value in raw_defect_ids
        ):
            raise FinalHolisticAuditSurfaceError(
                f"{key}: source_defect_ids is not a string list"
            )
        else:
            defect_ids = sorted(value.strip() for value in raw_defect_ids)
            if len(defect_ids) != len(set(defect_ids)):
                raise FinalHolisticAuditSurfaceError(
                    f"{key}: source_defect_ids contains duplicates"
                )
        corrected_digest = ""
        if str(raw.get("coverage_status") or "").strip() == "corrected_source_statement":
            corrected_target = raw.get("corrected_target")
            if (
                not isinstance(corrected_target, Mapping)
                or corrected_target.get("archival_equivalence_claimed") is not False
            ):
                raise FinalHolisticAuditSurfaceError(
                    f"{key}: corrected source item lacks a non-equivalence target"
                )
            corrected_digest = corrected_target_review_digest(corrected_target)
            if _sha256(
                corrected_target.get("corrected_target_review_sha256"),
                label=f"{key} corrected target",
            ) != corrected_digest:
                raise FinalHolisticAuditSurfaceError(
                    f"{key}: corrected target digest is stale"
                )
        facts[key] = {
            "source_item_semantic_sha256": semantic,
            "source_input_bundle_sha256": _sha256(
                bundle, label=f"{key} source input bundle"
            ),
            "source_claim_atoms_sha256": atoms,
            # Defect cross-references are owned by the fidelity validator rather
            # than by source-to-Lean matching, but terminal acceptance must still
            # bind their exact substantive routing.
            "source_defect_ids": defect_ids,
            "corrected_target_review_sha256": corrected_digest,
        }
    missing = sorted(required.difference(facts))
    if missing:
        raise FinalHolisticAuditSurfaceError(
            "typed semantic review names an unknown source item: " + ", ".join(missing)
        )
    return facts


def _ledger_items(
    payload: Mapping[str, Any],
    *,
    paper: str,
    schema: int,
    prompt_version: str,
    target_protocol: str | None,
    label: str,
) -> dict[str, Mapping[str, Any]]:
    if (
        payload.get("schema") != schema
        or payload.get("paper") != paper
        or str(payload.get("prompt_version") or "").strip() != prompt_version
        or (
            target_protocol is not None
            and str(payload.get("target_protocol") or "").strip()
            != target_protocol
        )
    ):
        raise FinalHolisticAuditSurfaceError(f"{label} container is stale")
    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        raise FinalHolisticAuditSurfaceError(f"{label} has no item ledger")
    return {
        str(name): row
        for name, row in raw_items.items()
        if isinstance(name, str) and isinstance(row, Mapping)
    }


def _reviewed_source_item_ids(
    *ledgers: tuple[str, Mapping[str, Mapping[str, Any]]],
) -> set[str]:
    """Return the source records actually used by current semantic review.

    The terminal source-assurance projection deliberately excludes
    deep-audit-only inventory observations, but it must still bind every
    source item that a direct, paper-local, or library semantic judgment
    consumed. Both the full holistic surface and the cheap receipt checker use
    this one data-only selector; neither needs to parse Lean or acquire a Lean
    graph to determine that set.
    """

    source_item_ids: set[str] = set()
    for label, items in ledgers:
        for declaration, row in items.items():
            source_item = str(row.get("source_item") or "").strip()
            if not source_item:
                raise FinalHolisticAuditSurfaceError(
                    f"{declaration}: {label} has no source item"
                )
            source_item_ids.add(source_item)
    return source_item_ids


def _terminal_semantic_declaration_selection(
    *,
    inventory: Mapping[str, Any],
    spec_names: Iterable[str],
    paper_names: Iterable[str],
    library_names: Iterable[str],
    source_spec_items: Mapping[str, Mapping[str, Any]],
    paper_ledger_items: Mapping[str, Mapping[str, Any]],
    library_ledger_items: Mapping[str, Mapping[str, Any]],
    primary_source_item_ids: frozenset[str] | None,
) -> tuple[frozenset[str], frozenset[str], frozenset[str]]:
    """Select main rows and governing typed semantic prerequisites.

    The Lean graph supplies semantic statement/definition edges.  Proof-only
    and erased declarations are deliberately not traversed.  A dependency is
    promoted only when it is also in the typed source-review ledger, so a proof
    helper cannot become paper semantics merely by appearing in the graph.
    """

    specs = frozenset(spec_names)
    papers = frozenset(paper_names)
    libraries = frozenset(library_names)
    if primary_source_item_ids is None:
        return specs, papers, libraries

    def ledger_source_item(
        rows: Mapping[str, Mapping[str, Any]], declaration: str
    ) -> str:
        raw = rows.get(declaration)
        return str(raw.get("source_item") or "").strip() if raw else ""

    selected_specs = {
        name
        for name in specs
        if ledger_source_item(source_spec_items, name) in primary_source_item_ids
    }
    selected_papers = {
        name
        for name in papers
        if ledger_source_item(paper_ledger_items, name) in primary_source_item_ids
    }
    selected_libraries = {
        name
        for name in libraries
        if ledger_source_item(library_ledger_items, name)
        in primary_source_item_ids
    }

    def display_rows(section: str, field: str) -> dict[str, Mapping[str, Any]]:
        raw_section = inventory.get(section)
        raw_rows = (
            raw_section.get("items")
            if isinstance(raw_section, Mapping)
            else None
        )
        if not isinstance(raw_rows, list):
            raise FinalHolisticAuditSurfaceError(
                f"Lean graph has malformed {section}"
            )
        result: dict[str, Mapping[str, Any]] = {}
        for raw in raw_rows:
            name = (
                str(raw.get(field) or "").strip()
                if isinstance(raw, Mapping)
                else ""
            )
            if not name or name in result:
                raise FinalHolisticAuditSurfaceError(
                    f"Lean graph has a blank or duplicate {section} declaration"
                )
            result[name] = raw
        return result

    spec_displays = display_rows("transparent_spec_displays", "specification")
    paper_displays = display_rows("paper_prerequisite_displays", "declaration")
    library_displays = display_rows(
        "library_prerequisite_displays", "declaration"
    )

    def names(raw: object) -> set[str]:
        if not isinstance(raw, list):
            return set()
        return {
            str(value).strip()
            for value in raw
            if isinstance(value, str) and value.strip()
        }

    for spec in tuple(selected_specs):
        display = spec_displays[spec]
        selected_papers.update(
            names(display.get("prerequisite_declarations")) & papers
        )
        selected_libraries.update(
            names(display.get("library_declarations")) & libraries
        )

    changed = True
    while changed:
        before = (len(selected_papers), len(selected_libraries))
        for declaration in tuple(selected_papers):
            display = paper_displays[declaration]
            selected_papers.update(
                names(display.get("direct_paper_declarations")) & papers
            )
            selected_libraries.update(
                names(display.get("direct_library_declarations")) & libraries
            )
        for declaration in tuple(selected_libraries):
            display = library_displays[declaration]
            selected_libraries.update(
                names(display.get("direct_library_declarations")) & libraries
            )
        changed = before != (len(selected_papers), len(selected_libraries))
    return (
        frozenset(selected_specs),
        frozenset(selected_papers),
        frozenset(selected_libraries),
    )


def _prerequisite_rows(
    *,
    names: Iterable[str],
    signatures: Mapping[str, str],
    ledger_items: Mapping[str, Mapping[str, Any]],
    source_facts: Mapping[str, Mapping[str, str]],
    declaration_field: str,
    target_protocol_field: str,
    target_protocol: str,
    role: str,
    selected_names: frozenset[str] | None = None,
) -> list[dict[str, Any]]:
    expected = set(names)
    if set(ledger_items) != expected:
        raise FinalHolisticAuditSurfaceError(
            f"{role} ledger differs from the Lean-selected prerequisite surface"
        )
    rows: list[dict[str, Any]] = []
    for name in sorted(expected):
        raw = ledger_items[name]
        source_item = str(raw.get("source_item") or "").strip()
        source = source_facts.get(source_item)
        signature = signatures.get(name, "")
        judgment = str(raw.get("judgment") or "").strip().lower()
        approved_correction_current = (
            judgment == APPROVED_CORRECTED_TARGET_MATCH
            and source is not None
            and str(raw.get("corrected_target_protocol") or "").strip()
            == CORRECTED_TARGET_REVIEW_PROTOCOL
            and str(raw.get("corrected_target_review_sha256") or "").strip().lower()
            == str(source.get("corrected_target_review_sha256") or "").strip().lower()
            and bool(str(source.get("corrected_target_review_sha256") or "").strip())
        )
        if (
            judgment not in SOURCE_TO_SPEC_PASS_JUDGMENTS
            or (
                judgment == APPROVED_CORRECTED_TARGET_MATCH
                and not approved_correction_current
            )
            or str(raw.get(declaration_field) or "").strip() != name
            or str(raw.get(target_protocol_field) or "").strip()
            != target_protocol
            or _sha256(
                raw.get("elaborated_signature_sha256"),
                label=f"{name} recorded Lean semantic identity",
            )
            != signature
            or source is None
            or _sha256(
                raw.get("source_input_bundle_sha256"),
                label=f"{name} recorded source bundle",
            )
            != source["source_input_bundle_sha256"]
        ):
            raise FinalHolisticAuditSurfaceError(
                f"{name}: {role} source-to-Lean review is not current"
            )
        if selected_names is not None and name not in selected_names:
            continue
        rows.append(
            {
                "role": role,
                **dict(source),
                "lean_semantic_identity_sha256": signature,
            }
        )
    return sorted(rows, key=_digest)


def build_final_holistic_audit_surface(
    *,
    paper: str,
    source_map: Mapping[str, Any],
    graph: Mapping[str, Any],
    status_projection: Mapping[str, Any],
    source_spec_screening: Mapping[str, Any],
    paper_prerequisite_ledger: Mapping[str, Any],
    library_prerequisite_ledger: Mapping[str, Any],
    source_proof_fidelity: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Build one strict semantic surface from the current typed transaction."""

    # These two validators still live with the Lean graph producer.  Load that
    # producer only when this terminal semantic projection is actually built;
    # importing the planner or inspecting a receipt must not acquire it.
    from scripts.lean_signature_manifest import (
        semantic_review_claim_surfaces_from_inventory,
        semantic_signature_sha256s_from_inventory,
    )

    if source_map.get("paper") != paper or graph.get("paper") != paper:
        raise FinalHolisticAuditSurfaceError(
            "source map or Lean graph belongs to a different paper"
        )
    mode, mode_error = source_coverage_mode_from_map(dict(source_map))
    if mode_error:
        raise FinalHolisticAuditSurfaceError(mode_error)
    try:
        review_policy = explicit_closeout_review_policy_from_source_map(source_map)
    except FormalizationProtocolError as exc:
        raise FinalHolisticAuditSurfaceError(str(exc)) from exc
    if review_policy is not None:
        try:
            complete_region_projection = source_region_partition_projection(
                source_map
            )
        except SourceReviewScopeError as exc:
            raise FinalHolisticAuditSurfaceError(str(exc)) from exc
    else:
        complete_region_projection = None
    inventory = graph.get("inventory")
    if not isinstance(inventory, Mapping):
        raise FinalHolisticAuditSurfaceError("Lean graph has no declaration inventory")
    spec_names = _section_declarations(
        inventory, "transparent_spec_displays", "specification"
    )
    all_paper_names = _section_declarations(
        inventory, "paper_prerequisite_displays", "declaration"
    )
    # The Lean graph deliberately carries the complete local dependency
    # closure.  Only the typed source-map boundary is a paper-semantic review
    # row; the remaining declarations stay realization support.  Reuse the
    # same selector used by the prerequisite writer, rather than letting this
    # terminal projection promote implementation dependencies into claims.
    try:
        paper_names = tuple(
            sorted(
                selected_paper_semantic_prerequisite_targets(
                    source_map,
                    {name: {} for name in all_paper_names},
                )
            )
        )
    except ValueError as exc:
        raise FinalHolisticAuditSurfaceError(
            "invalid typed paper-prerequisite review boundary: " + str(exc)
        ) from exc
    all_library_names = _section_declarations(
        inventory, "library_prerequisite_displays", "declaration"
    )
    try:
        library_names = tuple(
            sorted(
                selected_library_semantic_prerequisite_targets(
                    source_map,
                    {name: {} for name in all_library_names},
                )
            )
        )
    except ValueError as exc:
        raise FinalHolisticAuditSurfaceError(
            "invalid reusable-library semantic review boundary: " + str(exc)
        ) from exc
    # The graph retains complete dependency displays, while this terminal
    # semantic surface checks only the explicitly source-routed paper subset.
    # Preserve the graph itself unchanged and pass a projected display section
    # to the shared Lean-owned display validator.
    raw_paper_display = inventory.get("paper_prerequisite_displays")
    raw_paper_rows = (
        raw_paper_display.get("items")
        if isinstance(raw_paper_display, Mapping)
        else None
    )
    if not isinstance(raw_paper_rows, list):
        raise FinalHolisticAuditSurfaceError(
            "Lean graph has malformed paper_prerequisite_displays"
        )
    raw_library_display = inventory.get("library_prerequisite_displays")
    raw_library_rows = (
        raw_library_display.get("items")
        if isinstance(raw_library_display, Mapping)
        else None
    )
    if not isinstance(raw_library_rows, list):
        raise FinalHolisticAuditSurfaceError(
            "Lean graph has malformed library_prerequisite_displays"
        )
    selected_paper_display = {
        "schema": raw_paper_display.get("schema"),
        "items": [
            row
            for row in raw_paper_rows
            if isinstance(row, Mapping)
            and str(row.get("declaration") or "").strip() in set(paper_names)
        ],
    }
    selected_library_display = {
        "schema": raw_library_display.get("schema"),
        "items": [
            row
            for row in raw_library_rows
            if isinstance(row, Mapping)
            and str(row.get("declaration") or "").strip()
            in set(library_names)
        ],
    }
    semantic_display_inventory = dict(inventory)
    semantic_display_inventory["paper_prerequisite_displays"] = (
        selected_paper_display
    )
    semantic_display_inventory["library_prerequisite_displays"] = (
        selected_library_display
    )
    semantic_review_display_surface_from_inventory(
        semantic_display_inventory,
        expected_specifications=spec_names,
        expected_paper_declarations=paper_names,
        expected_library_declarations=library_names,
    )
    all_names = (*spec_names, *paper_names, *library_names)
    raw_signatures = inventory.get("semantic_signatures")
    raw_signature_rows = (
        raw_signatures.get("items") if isinstance(raw_signatures, Mapping) else None
    )
    if not isinstance(raw_signature_rows, list):
        raise FinalHolisticAuditSurfaceError("Lean graph has malformed semantic_signatures")
    semantic_display_inventory["semantic_signatures"] = {
        "schema": raw_signatures.get("schema"),
        "items": [
            row
            for row in raw_signature_rows
            if isinstance(row, Mapping)
            and str(row.get("declaration") or "").strip() in set(all_names)
        ],
        "errors": raw_signatures.get("errors"),
    }
    signatures = semantic_signature_sha256s_from_inventory(
        semantic_display_inventory, expected_declarations=all_names
    )
    claim_surfaces = semantic_review_claim_surfaces_from_inventory(
        inventory, expected_declarations=spec_names
    )
    try:
        routes = EvidenceRouteSet.from_source_map(source_map)
    except ObligationRouteError as exc:
        raise FinalHolisticAuditSurfaceError(
            "source map has invalid typed routes: " + str(exc)
        ) from exc
    by_spec = routes.result_route_by_specification()
    if set(by_spec) != set(spec_names):
        raise FinalHolisticAuditSurfaceError(
            "typed result routes differ from the Lean-selected Spec surface"
        )
    screening_validation = validate_v11_screening_container(
        source_spec_screening, paper=paper
    )
    if not screening_validation.current:
        raise FinalHolisticAuditSurfaceError(
            "source-to-Spec screening is stale: "
            + "; ".join(screening_validation.errors)
        )
    screening_items = _ledger_items(
        source_spec_screening,
        paper=paper,
        schema=V11_SCREENING_SCHEMA,
        prompt_version=V11_SCREENING_PROMPT_VERSION,
        target_protocol=None,
        label="source-to-Spec screening",
    )
    if set(screening_items) != set(spec_names):
        raise FinalHolisticAuditSurfaceError(
            "source-to-Spec screening differs from the Lean-selected Spec surface"
        )

    raw_contracts = inventory.get("semantic_contracts")
    if not isinstance(raw_contracts, list):
        raise FinalHolisticAuditSurfaceError("Lean graph has no semantic contracts")
    contracts: dict[str, Mapping[str, Any]] = {}
    for raw in raw_contracts:
        spec = str(raw.get("specification") or "").strip() if isinstance(raw, Mapping) else ""
        if not spec or spec in contracts:
            raise FinalHolisticAuditSurfaceError(
                "Lean graph has a blank or duplicate semantic contract"
            )
        contracts[spec] = raw
    if set(contracts) != set(spec_names):
        raise FinalHolisticAuditSurfaceError(
            "Lean semantic contracts differ from the selected Spec surface"
        )

    paper_ledger_items = _ledger_items(
        paper_prerequisite_ledger,
        paper=paper,
        schema=PAPER_PREREQUISITE_SCHEMA,
        prompt_version=PAPER_PREREQUISITE_PROMPT_VERSION,
        target_protocol=PAPER_PREREQUISITE_TARGET_PROTOCOL,
        label="paper-prerequisite review",
    )
    library_ledger_items = _ledger_items(
        library_prerequisite_ledger,
        paper=paper,
        schema=LIBRARY_SEMANTIC_REVIEW_SCHEMA,
        prompt_version=REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,
        target_protocol=LIBRARY_SEMANTIC_TARGET_PROTOCOL,
        label="library-prerequisite review",
    )
    required_source_item_ids = _reviewed_source_item_ids(
        ("source-to-Spec screening", screening_items),
        ("paper-prerequisite review", paper_ledger_items),
        ("library-prerequisite review", library_ledger_items),
    )
    source_facts = _source_item_facts(
        source_map,
        mode,
        required_source_item_ids=required_source_item_ids,
    )
    primary_source_item_ids = (
        selected_terminal_source_item_ids(source_map, review_policy)
        if review_policy is not None
        else None
    )
    if review_policy is None:
        selected_specs = frozenset(spec_names)
        selected_paper_names = frozenset(paper_names)
        selected_library_names = frozenset(library_names)
    else:
        try:
            (
                selected_specs,
                selected_paper_names,
                selected_library_names,
            ) = _terminal_semantic_declaration_selection(
                inventory=inventory,
                spec_names=spec_names,
                paper_names=paper_names,
                library_names=library_names,
                source_spec_items=screening_items,
                paper_ledger_items=paper_ledger_items,
                library_ledger_items=library_ledger_items,
                primary_source_item_ids=primary_source_item_ids,
            )
        except SourceReviewScopeError as exc:
            raise FinalHolisticAuditSurfaceError(str(exc)) from exc

    result_rows: list[dict[str, Any]] = []
    for spec in sorted(spec_names):
        route = by_spec[spec]
        raw = screening_items[spec]
        source = source_facts.get(route.source_item_id)
        claim = claim_surfaces[spec]
        contract = contracts[spec]
        if source is None:
            raise FinalHolisticAuditSurfaceError(
                f"{spec}: typed route names an unknown source item"
            )
        if not source["source_claim_atoms_sha256"]:
            raise FinalHolisticAuditSurfaceError(
                f"{route.source_item_id}: result route has no source claim atoms"
            )
        axiom_closure = contract.get("evidence_axiom_closure")
        if not isinstance(axiom_closure, list) or not all(
            isinstance(name, str) and name.strip() for name in axiom_closure
        ):
            raise FinalHolisticAuditSurfaceError(
                f"{spec}: proof contract has malformed axiom closure"
            )
        if (
            str(raw.get("judgment") or "").strip().lower()
            not in SOURCE_TO_SPEC_PASS_JUDGMENTS
            or str(raw.get("semantic_target_declaration") or "").strip() != spec
            or str(raw.get("source_item") or "").strip() != route.source_item_id
            or _sha256(
                raw.get("source_input_bundle_sha256"),
                label=f"{spec} recorded source bundle",
            )
            != source["source_input_bundle_sha256"]
            or _sha256(
                raw.get("review_claim_manifest_sha256"),
                label=f"{spec} recorded Lean claim manifest",
            )
            != signatures[spec]
            or _sha256(
                raw.get("review_claim_atoms_sha256"),
                label=f"{spec} recorded Lean claim atoms",
            )
            != claim.get("claim_atoms_sha256")
            or claim.get("manifest_sha256") != signatures[spec]
            or contract.get("evidence") != route.evidence_declaration
            or contract.get("mode") != route.evidence_mode
            or contract.get("matches") is not True
            or contract.get("evidence_is_unsafe") is not False
            or contract.get("evidence_value_has_sorry") is not False
            or contract.get("evidence_axiom_closure_checked") is not True
        ):
            raise FinalHolisticAuditSurfaceError(
                f"{spec}: source-to-Spec review or proof contract is not current"
            )
        if spec in selected_specs:
            result_rows.append(
                {
                    "role": "source_result",
                    **dict(source),
                    "lean_semantic_identity_sha256": signatures[spec],
                    "lean_claim_atoms_sha256": claim["claim_atoms_sha256"],
                    "source_review_target_sha256": _sha256(
                        raw.get("source_review_target_sha256"),
                        label=f"{spec} source review target",
                    ),
                    "source_match_kind": str(raw.get("judgment") or "")
                    .strip()
                    .lower(),
                    "semantic_review_target_kind": (
                        route.semantic_review_target_kind.value
                    ),
                    "proof_contract": {
                        "mode": route.evidence_mode,
                        "matches": True,
                        "evidence_is_unsafe": False,
                        "evidence_value_has_sorry": False,
                        "evidence_axiom_closure_checked": True,
                        "evidence_axiom_closure": sorted(set(axiom_closure)),
                    },
                }
            )

    prerequisite_rows = _prerequisite_rows(
        names=paper_names,
        signatures=signatures,
        ledger_items=paper_ledger_items,
        source_facts=source_facts,
        declaration_field="paper_declaration",
        target_protocol_field="paper_semantic_target_protocol",
        target_protocol=PAPER_PREREQUISITE_TARGET_PROTOCOL,
        role="paper_prerequisite",
        selected_names=selected_paper_names,
    ) + _prerequisite_rows(
        names=library_names,
        signatures=signatures,
        ledger_items=library_ledger_items,
        source_facts=source_facts,
        declaration_field="library_declaration",
        target_protocol_field="library_semantic_target_protocol",
        target_protocol=LIBRARY_SEMANTIC_TARGET_PROTOCOL,
        role="library_prerequisite",
        selected_names=selected_library_names,
    )

    raw_status = status_projection.get("status")
    if (
        status_projection.get("paper") != paper
        or not isinstance(raw_status, Mapping)
    ):
        raise FinalHolisticAuditSurfaceError(
            "paper status acceptance projection is malformed"
        )
    review_surface = raw_status.get("review_surface")
    if not isinstance(review_surface, Mapping):
        raise FinalHolisticAuditSurfaceError(
            "paper status has no review-surface configuration"
        )
    fidelity_projection = (
        source_proof_fidelity_semantic_projection(source_proof_fidelity)
        if source_proof_fidelity is not None
        else None
    )
    if source_proof_fidelity is not None and fidelity_projection is None:
        raise FinalHolisticAuditSurfaceError(
            "source-proof-fidelity ledger has no valid semantic projection"
        )
    full_inventory = {
        "items": sorted(source_facts.values(), key=_digest),
        "named_result_inventory": _named_inventory_projection(source_map),
        "scope_relations": _source_scope_relations_projection(source_map, mode),
    }
    semantic_rows = sorted([*result_rows, *prerequisite_rows], key=_digest)
    status_semantics = {
        "formalization_status": str(raw_status.get("status") or "").strip(),
        "main_caveat": str(raw_status.get("main_caveat") or "").strip(),
        "assumption_policy": str(
            review_surface.get("assumption_policy") or ""
        ).strip(),
    }
    if review_policy is None:
        return {
        "schema": FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA,
        "identity_schema": FINAL_HOLISTIC_AUDIT_SURFACE_IDENTITY_SCHEMA,
        "paper": paper,
        "source_coverage_mode": mode,
        "source_corpus": _source_corpus_projection(source_map),
        "source_inventory": full_inventory,
        "semantic_review_rows": semantic_rows,
        "status_semantics": status_semantics,
        "source_proof_fidelity_semantics": fidelity_projection,
        }

    assert complete_region_projection is not None
    partition = source_map["source_named_result_inventory_review"][
        "source_region_partition"
    ]
    assert isinstance(partition, Mapping)
    if review_policy.repeat_final_scope == CLOSEOUT_REPEAT_SCOPE_ALL_SELECTED:
        terminal_regions = complete_region_projection
        terminal_inventory = full_inventory
    else:
        terminal_regions = primary_source_region_projection(source_map)
        main_region_ids = {
            str(raw.get("id") or "").strip()
            for raw in partition["regions"]
            if isinstance(raw, Mapping)
            and raw.get("kind") == "main_text"
        }
        candidate_ids = frozenset(
            str(candidate_id)
            for candidate_id, region_id in partition[
                CANDIDATE_PRESENTATION_REGIONS_FIELD
            ].items()
            if str(region_id) in main_region_ids
        )
        prose_digests = frozenset(
            str(presentation_sha256)
            for presentation_sha256, region_id in partition[
                PROSE_DEFINITION_PRESENTATION_REGIONS_FIELD
            ].items()
            if str(region_id) in main_region_ids
        )
        selected_semantic_source_item_ids = {
            str(screening_items[name].get("source_item") or "").strip()
            for name in selected_specs
        } | {
            str(paper_ledger_items[name].get("source_item") or "").strip()
            for name in selected_paper_names
        } | {
            str(library_ledger_items[name].get("source_item") or "").strip()
            for name in selected_library_names
        }
        terminal_scope_source_item_ids = frozenset(
            set(primary_source_item_ids or ())
            | selected_semantic_source_item_ids
        )
        terminal_inventory = {
            "items": sorted(
                (
                    source_facts[source_item]
                    for source_item in selected_semantic_source_item_ids
                ),
                key=_digest,
            ),
            "named_result_inventory": _named_inventory_projection(
                source_map,
                candidate_ids=candidate_ids,
                prose_presentation_sha256s=prose_digests,
            ),
            "scope_relations": _source_scope_relations_projection(
                source_map,
                mode,
                required_source_item_ids=terminal_scope_source_item_ids,
            ),
        }
    return {
        "schema": POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA,
        "identity_schema": (
            POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_IDENTITY_SCHEMA
        ),
        "paper": paper,
        "source_coverage_mode": mode,
        "source_corpus": _source_corpus_projection(source_map),
        "source_inventory": full_inventory,
        "status_semantics": status_semantics,
        "source_proof_fidelity_semantics": fidelity_projection,
        "review_policy_assurance": closeout_review_policy_assurance_projection(
            review_policy
        ),
        "review_policy_scheduling": closeout_review_policy_scheduling_projection(
            review_policy
        ),
        "source_region_partition": complete_region_projection,
        "terminal_review": {
            "review_policy_material": closeout_review_policy_material_projection(
                review_policy
            ),
            "source_regions": terminal_regions,
            "source_inventory": terminal_inventory,
            "semantic_review_rows": semantic_rows,
        },
    }


def final_holistic_source_assurance_projection(
    surface: Mapping[str, object],
) -> dict[str, object]:
    """Select the cheap source/status/fidelity portion of a reviewed surface."""

    legacy_required = {
        "schema",
        "identity_schema",
        "paper",
        "source_coverage_mode",
        "source_corpus",
        "source_inventory",
        "semantic_review_rows",
        "status_semantics",
        "source_proof_fidelity_semantics",
    }
    policy_required = {
        "schema",
        "identity_schema",
        "paper",
        "source_coverage_mode",
        "source_corpus",
        "source_inventory",
        "status_semantics",
        "source_proof_fidelity_semantics",
        "review_policy_assurance",
        "review_policy_scheduling",
        "source_region_partition",
        "terminal_review",
    }
    if set(surface) == policy_required:
        if (
            surface.get("schema")
            != POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA
            or surface.get("identity_schema")
            != POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_IDENTITY_SCHEMA
            or not str(surface.get("paper") or "").strip()
        ):
            raise FinalHolisticAuditSurfaceError(
                "policy-aware final holistic surface identity is malformed"
            )
        projection = {
            "schema": POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA,
            "paper": surface["paper"],
            "source_coverage_mode": surface["source_coverage_mode"],
            "source_corpus": surface["source_corpus"],
            "source_inventory": surface["source_inventory"],
            "status_semantics": surface["status_semantics"],
            "source_proof_fidelity_semantics": surface[
                "source_proof_fidelity_semantics"
            ],
            "review_policy_assurance": surface["review_policy_assurance"],
            "source_region_partition": surface["source_region_partition"],
        }
        final_holistic_source_assurance_projection_sha256(projection)
        return projection
    if set(surface) != legacy_required:
        raise FinalHolisticAuditSurfaceError(
            "final holistic surface fields are malformed"
        )
    if (
        surface.get("schema") != FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA
        or surface.get("identity_schema")
        != FINAL_HOLISTIC_AUDIT_SURFACE_IDENTITY_SCHEMA
        or not str(surface.get("paper") or "").strip()
    ):
        raise FinalHolisticAuditSurfaceError(
            "final holistic surface identity is malformed"
        )
    projection = {
        "schema": 2,
        "paper": surface["paper"],
        "source_coverage_mode": surface["source_coverage_mode"],
        "source_corpus": surface["source_corpus"],
        "source_inventory": surface["source_inventory"],
        "status_semantics": surface["status_semantics"],
        "source_proof_fidelity_semantics": surface[
            "source_proof_fidelity_semantics"
        ],
    }
    final_holistic_source_assurance_projection_sha256(projection)
    return projection


def final_holistic_source_assurance_sha256(
    surface: Mapping[str, object],
) -> str:
    return _digest(final_holistic_source_assurance_projection(surface))


def final_holistic_source_assurance_projection_sha256(
    projection: Mapping[str, object],
) -> str:
    """Hash one exact historical or policy-aware assurance data shape."""

    legacy_required = {
        "schema",
        "paper",
        "source_coverage_mode",
        "source_corpus",
        "source_inventory",
        "status_semantics",
        "source_proof_fidelity_semantics",
    }
    schema = projection.get("schema")
    if schema == POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA:
        required = legacy_required | {
            "review_policy_assurance",
            "source_region_partition",
        }
        inventory = projection.get("source_inventory")
        if (
            set(projection) != required
            or not isinstance(inventory, Mapping)
            or set(inventory)
            != {"items", "named_result_inventory", "scope_relations"}
            or not isinstance(projection.get("review_policy_assurance"), Mapping)
            or not isinstance(projection.get("source_region_partition"), Mapping)
        ):
            raise FinalHolisticAuditSurfaceError(
                "policy-aware source-assurance projection fields are malformed"
            )
        return _digest(dict(projection))
    inventory = projection.get("source_inventory")
    inventory_fields = {"items", "named_result_inventory"}
    if schema == 2:
        inventory_fields.add("scope_relations")
    if (
        set(projection) != legacy_required
        or type(schema) is not int
        or schema not in {1, 2}
        or not isinstance(inventory, Mapping)
        or set(inventory) != inventory_fields
    ):
        raise FinalHolisticAuditSurfaceError(
            "source-assurance projection fields are malformed"
        )
    if schema == 2:
        scope_rows = inventory["scope_relations"]
        if not isinstance(scope_rows, list) or any(
            not isinstance(row, Mapping)
            or set(row) != {"source_item_semantic_sha256", "relations"}
            or not isinstance(row["source_item_semantic_sha256"], str)
            or not SHA256_RE.fullmatch(row["source_item_semantic_sha256"])
            or not isinstance(row["relations"], Mapping)
            or set(row["relations"]) - {
                "presentation_alias", "subsumed_by_selected_result"
            }
            or any(
                not isinstance(value, str) or not SHA256_RE.fullmatch(value)
                for value in row["relations"].values()
            )
            for row in scope_rows
        ):
            raise FinalHolisticAuditSurfaceError(
                "source-assurance scope relations are malformed"
            )
    return _digest(dict(projection))


def final_holistic_source_assurance_v2_projection(
    v1_projection: Mapping[str, object],
) -> dict[str, object]:
    """Upgrade one validated v1 preimage to prose-neutral v2 assurance.

    The exact historical builder and reader above remain the authority for the
    v1 preimage.  V2 changes only its status subprojection: formalization status
    and assumption policy remain controls, while reader prose and repository
    visibility cannot enter the digest.
    """

    final_holistic_source_assurance_projection_sha256(v1_projection)
    v1_schema = v1_projection.get("schema")
    if v1_schema not in {2, POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA}:
        raise FinalHolisticAuditSurfaceError(
            "terminal source-assurance v2 requires a current v1 projection"
        )
    raw_status = v1_projection.get("status_semantics")
    if (
        not isinstance(raw_status, Mapping)
        or set(raw_status)
        != {"formalization_status", "main_caveat", "assumption_policy"}
    ):
        raise FinalHolisticAuditSurfaceError(
            "v1 source-assurance status semantics are malformed"
        )
    try:
        status_control = paper_status_assurance_control_projection(
            paper=str(v1_projection.get("paper") or ""),
            formalization_status=raw_status.get("formalization_status"),
            assumption_policy=raw_status.get("assumption_policy"),
        )
    except CloseoutStatusProjectionError as exc:
        raise FinalHolisticAuditSurfaceError(str(exc)) from exc
    policy_aware = (
        v1_schema == POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA
    )
    return {
        "schema": TERMINAL_SOURCE_ASSURANCE_V2_SCHEMA,
        "identity_schema": TERMINAL_SOURCE_ASSURANCE_V2_IDENTITY_SCHEMA,
        "contract_sha256": TERMINAL_SOURCE_ASSURANCE_V2_CONTRACT.contract_sha256,
        "v1_source_assurance_schema": v1_schema,
        "paper": v1_projection["paper"],
        "source_coverage_mode": v1_projection["source_coverage_mode"],
        "source_corpus": v1_projection["source_corpus"],
        "source_inventory": v1_projection["source_inventory"],
        "status_control": status_control,
        "source_proof_fidelity_semantics": v1_projection[
            "source_proof_fidelity_semantics"
        ],
        "review_policy_assurance": (
            v1_projection["review_policy_assurance"] if policy_aware else None
        ),
        "source_region_partition": (
            v1_projection["source_region_partition"] if policy_aware else None
        ),
    }


def final_holistic_source_assurance_v2_projection_sha256(
    projection: Mapping[str, object],
) -> str:
    """Validate and hash the exact prose-neutral v2 assurance shape."""

    required = {
        "schema",
        "identity_schema",
        "contract_sha256",
        "v1_source_assurance_schema",
        "paper",
        "source_coverage_mode",
        "source_corpus",
        "source_inventory",
        "status_control",
        "source_proof_fidelity_semantics",
        "review_policy_assurance",
        "source_region_partition",
    }
    if (
        set(projection) != required
        or projection.get("schema") != TERMINAL_SOURCE_ASSURANCE_V2_SCHEMA
        or projection.get("identity_schema")
        != TERMINAL_SOURCE_ASSURANCE_V2_IDENTITY_SCHEMA
        or projection.get("contract_sha256")
        != TERMINAL_SOURCE_ASSURANCE_V2_CONTRACT.contract_sha256
    ):
        raise FinalHolisticAuditSurfaceError(
            "terminal source-assurance v2 identity is malformed"
        )
    v1_schema = projection.get("v1_source_assurance_schema")
    policy_aware = (
        v1_schema == POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA
    )
    if v1_schema not in {2, POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA}:
        raise FinalHolisticAuditSurfaceError(
            "terminal source-assurance v2 predecessor schema is malformed"
        )
    review_policy = projection.get("review_policy_assurance")
    region_partition = projection.get("source_region_partition")
    if policy_aware:
        if not isinstance(review_policy, Mapping) or not isinstance(
            region_partition, Mapping
        ):
            raise FinalHolisticAuditSurfaceError(
                "policy-aware terminal source-assurance v2 fields are malformed"
            )
    elif review_policy is not None or region_partition is not None:
        raise FinalHolisticAuditSurfaceError(
            "legacy-surface terminal source-assurance v2 has policy fields"
        )
    status_control = projection.get("status_control")
    if not isinstance(status_control, Mapping):
        raise FinalHolisticAuditSurfaceError(
            "terminal source-assurance v2 status control is malformed"
        )
    try:
        expected_status = paper_status_assurance_control_projection(
            paper=str(projection.get("paper") or ""),
            formalization_status=status_control.get("formalization_status"),
            assumption_policy=status_control.get("assumption_policy"),
        )
    except CloseoutStatusProjectionError as exc:
        raise FinalHolisticAuditSurfaceError(str(exc)) from exc
    if dict(status_control) != expected_status:
        raise FinalHolisticAuditSurfaceError(
            "terminal source-assurance v2 status control fields are malformed"
        )
    # Reuse the exact v1 structural validator for every unchanged semantic
    # field.  The placeholder caveat is never hashed as v2 material.
    structural_v1: dict[str, object] = {
        "schema": v1_schema,
        "paper": projection["paper"],
        "source_coverage_mode": projection["source_coverage_mode"],
        "source_corpus": projection["source_corpus"],
        "source_inventory": projection["source_inventory"],
        "status_semantics": {
            "formalization_status": status_control["formalization_status"],
            "main_caveat": "",
            "assumption_policy": status_control["assumption_policy"],
        },
        "source_proof_fidelity_semantics": projection[
            "source_proof_fidelity_semantics"
        ],
    }
    if policy_aware:
        structural_v1.update(
            review_policy_assurance=review_policy,
            source_region_partition=region_partition,
        )
    final_holistic_source_assurance_projection_sha256(structural_v1)
    return _digest(dict(projection))


def final_holistic_source_assurance_v2_sha256(
    surface: Mapping[str, object],
) -> str:
    """Build and hash v2 assurance from the full reviewed audit surface."""

    return final_holistic_source_assurance_v2_projection_sha256(
        final_holistic_source_assurance_v2_projection(
            final_holistic_source_assurance_projection(surface)
        )
    )


def _historical_source_item_coverage_sha256(item: dict[str, Any]) -> str:
    """Read the frozen schema-6 preimage before the resolved-problem flag.

    Only the newly added *false* diagnostic field is absent from this old
    shape. A true new policy, unknown field, or later schema is not readable
    under it. Every source/correction field remains in the shared projection.
    """

    from scripts import source_coverage_scope as scope

    if (
        scope.SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA != 6
        or scope.SOURCE_STATUS_POLICY_SCHEMA != 1
    ):
        return ""
    policy_fields = {
        "allows_direct_route", "allows_source_component_route",
        "allows_source_model_convention_route", "allows_defect_or_remark_support_route",
        "direct_source_endpoint_required", "is_model_convention",
        "is_quarantined_source_defect", "is_support_only",
        "is_source_declared_open_nonresult", "external_support_only_vocabulary",
    }
    effective = scope.source_item_effective_route_policy(
        item, include_direct_source_status=True
    )
    if (
        set(effective) != policy_fields | {"is_source_resolved_within_paper"}
        or any(type(flag) is not bool for flag in effective.values())
        or effective.get("is_source_resolved_within_paper") is not False
    ):
        return ""
    source_fields, historical_error = (
        scope._historical_source_item_semantic_projection(item)
    )
    if historical_error or source_fields is None:
        return ""
    material: dict[str, object] = {
        "schema": 6,
        "source_item": source_fields,
    }
    policy = scope.source_item_direct_status_policy_projection(item)
    if policy is not None:
        if (
            set(policy) - {
                "schema", "effective_route_policy", "legacy_status_route_policy",
                "direct_source_status_shape",
            }
            or policy.get("schema") != 1
            or "effective_route_policy" not in policy
        ):
            return ""
        policy = dict(policy)
        for field in ("effective_route_policy", "legacy_status_route_policy"):
            if field not in policy:
                continue
            value = policy[field]
            if (
                not isinstance(value, Mapping)
                or set(value) != policy_fields | {"is_source_resolved_within_paper"}
                or any(type(flag) is not bool for flag in value.values())
                or value["is_source_resolved_within_paper"] is not False
            ):
                return ""
            policy[field] = {key: value[key] for key in policy_fields}
        material["direct_source_status_policy"] = policy
    return _digest(material)


def historical_final_holistic_source_assurance_sha256s(
    projection: Mapping[str, object], *, source_map: Mapping[str, Any]
) -> frozenset[str]:
    """Read the baseline schema-1 assurance and its two older observed shapes.

    This is a historical reader, never a fresh issuer. It retains today's
    validated corpus, inventory, source bundles, atoms, defects, status and
    fidelity. The old correction-free row still binds the entire corrected
    target through its source-item digest. Schema 1 did not attest the new
    source-scope relations: these exact historical preimages do not claim it
    did. Every candidate remains schema 1, so no changed schema-2 assurance can
    match by dropping its scope obligations. No engine identity selects a shape.
    """

    from scripts import source_coverage_scope as scope

    final_holistic_source_assurance_projection_sha256(projection)
    if projection.get("schema") not in {1, 2}:
        return frozenset()
    inventory = projection.get("source_inventory")
    items = source_map.get("items")
    if (
        not isinstance(inventory, Mapping)
        or not isinstance(items, Mapping)
        or source_map.get("paper") != projection.get("paper")
    ):
        return frozenset()
    rows = inventory.get("items")
    fields = {
        "source_item_semantic_sha256", "source_input_bundle_sha256",
        "source_claim_atoms_sha256", "source_defect_ids", "corrected_target_review_sha256",
    }
    if not isinstance(rows, list) or any(
        not isinstance(row, Mapping) or set(row) != fields for row in rows
    ):
        return frozenset()
    baseline_inventory = {
        key: value for key, value in inventory.items() if key != "scope_relations"
    }
    baseline = dict(projection, schema=1, source_inventory=baseline_inventory)
    wanted = {row["source_item_semantic_sha256"] for row in rows}
    previous: dict[str, set[str]] = {}
    for item in items.values():
        if not isinstance(item, dict):
            return frozenset()
        current = source_item_coverage_sha256(
            item, str(projection["source_coverage_mode"])
        )
        if current in wanted:
            _historical_item, historical_error = (
                scope._historical_source_item_semantic_projection(item)
            )
            if historical_error:
                raise FinalHolisticAuditSurfaceError(
                    "historical corrected-target locator is malformed: "
                    + historical_error
                )
            previous.setdefault(current, set()).add(
                _historical_source_item_coverage_sha256(item)
            )
    if set(previous) != wanted:
        return frozenset()
    baseline_digest = _digest(baseline)
    if any(len(values) != 1 or "" in values for values in previous.values()):
        return frozenset((baseline_digest,))
    old_rows = [
        dict(row, source_item_semantic_sha256=next(iter(
            previous[row["source_item_semantic_sha256"]]
        )))
        for row in rows
    ]
    old = dict(
        baseline,
        source_inventory=dict(baseline_inventory, items=sorted(old_rows, key=_digest)),
    )
    with_correction_field = _digest(old)
    without_correction = [
        {key: value for key, value in row.items()
         if key != "corrected_target_review_sha256"}
        for row in old_rows
    ]
    old["source_inventory"] = dict(
        baseline_inventory, items=sorted(without_correction, key=_digest)
    )
    return frozenset((baseline_digest, with_correction_field, _digest(old)))


def build_current_final_holistic_source_assurance_projection(
    root: Path,
    *,
    paper: str,
    reviewed_source_item_ids: Iterable[str],
) -> dict[str, object]:
    """Recompute source assurance for the authenticated graph's review inputs.

    The accepting caller selects source records from the validated graph index,
    not mutable issuance worksheets or the current review-prompt version.
    Fresh issuance still validates those worksheets in the full surface builder.
    """

    from scripts.closeout_status_projection import (
        CloseoutStatusProjectionError,
        paper_status_acceptance_projection,
    )

    root = root.resolve()
    audit = root / "papers" / paper / "audit"
    source_map = _load_object(
        audit / "paper_statement_map.json", label="canonical source map"
    )
    if source_map.get("paper") != paper:
        raise FinalHolisticAuditSurfaceError(
            "canonical source map belongs to another paper"
        )
    mode, mode_error = source_coverage_mode_from_map(source_map)
    if mode_error:
        raise FinalHolisticAuditSurfaceError(mode_error)
    source_facts = _source_item_facts(
        source_map,
        mode,
        required_source_item_ids=reviewed_source_item_ids,
    )
    try:
        review_policy = explicit_closeout_review_policy_from_source_map(source_map)
    except FormalizationProtocolError as exc:
        raise FinalHolisticAuditSurfaceError(str(exc)) from exc
    try:
        status_projection = paper_status_acceptance_projection(root, paper)
    except CloseoutStatusProjectionError as exc:
        raise FinalHolisticAuditSurfaceError(str(exc)) from exc
    raw_status = status_projection.get("status")
    review_surface = (
        raw_status.get("review_surface") if isinstance(raw_status, Mapping) else None
    )
    if not isinstance(raw_status, Mapping) or not isinstance(
        review_surface, Mapping
    ):
        raise FinalHolisticAuditSurfaceError(
            "paper status acceptance projection is malformed"
        )
    fidelity = _load_optional_object(
        audit / "source_proof_fidelity.json",
        label="source-proof-fidelity review ledger",
    )
    fidelity_projection = (
        source_proof_fidelity_semantic_projection(fidelity)
        if fidelity is not None
        else None
    )
    if fidelity is not None and fidelity_projection is None:
        raise FinalHolisticAuditSurfaceError(
            "source-proof-fidelity ledger has no valid semantic projection"
        )
    projection: dict[str, object] = {
        "schema": 2,
        "paper": paper,
        "source_coverage_mode": mode,
        "source_corpus": _source_corpus_projection(source_map),
        "source_inventory": {
            "items": sorted(source_facts.values(), key=_digest),
            "named_result_inventory": _named_inventory_projection(source_map),
            "scope_relations": _source_scope_relations_projection(source_map, mode),
        },
        "status_semantics": {
            "formalization_status": str(raw_status.get("status") or "").strip(),
            "main_caveat": str(raw_status.get("main_caveat") or "").strip(),
            "assumption_policy": str(
                review_surface.get("assumption_policy") or ""
            ).strip(),
        },
        "source_proof_fidelity_semantics": fidelity_projection,
    }
    if review_policy is not None:
        try:
            region_projection = source_region_partition_projection(source_map)
        except SourceReviewScopeError as exc:
            raise FinalHolisticAuditSurfaceError(str(exc)) from exc
        projection.update(
            schema=POLICY_AWARE_FINAL_HOLISTIC_AUDIT_SURFACE_SCHEMA,
            review_policy_assurance=closeout_review_policy_assurance_projection(
                review_policy
            ),
            source_region_partition=region_projection,
        )
    final_holistic_source_assurance_projection_sha256(projection)
    return projection


def build_current_final_holistic_source_assurance_v2_projection(
    root: Path,
    *,
    paper: str,
    reviewed_source_item_ids: Iterable[str],
) -> dict[str, object]:
    """Recompute v2 from the exact current v1 source-assurance preimage."""

    return final_holistic_source_assurance_v2_projection(
        build_current_final_holistic_source_assurance_projection(
            root,
            paper=paper,
            reviewed_source_item_ids=reviewed_source_item_ids,
        )
    )


def build_final_holistic_audit_surface_from_repository(
    root: Path,
    *,
    paper: str,
    graph: Mapping[str, Any],
    status_projection: Mapping[str, Any],
) -> dict[str, Any]:
    """Load canonical typed inputs and construct the final audit surface."""

    folder = root.resolve() / "papers" / paper
    audit = folder / "audit"
    return build_final_holistic_audit_surface(
        paper=paper,
        source_map=_load_object(
            audit / "paper_statement_map.json", label="canonical source map"
        ),
        graph=graph,
        status_projection=status_projection,
        source_spec_screening=_load_object(
            audit / "v11_raw_source_spec_screening.json",
            label="source-to-Spec screening",
        ),
        paper_prerequisite_ledger=_load_object(
            audit / "paper_semantic_prerequisites.json",
            label="paper-prerequisite review ledger",
        ),
        library_prerequisite_ledger=_load_object(
            audit / "library_semantic_review.json",
            label="library-prerequisite review ledger",
        ),
        source_proof_fidelity=_load_optional_object(
            audit / "source_proof_fidelity.json",
            label="source-proof-fidelity review ledger",
        ),
    )
