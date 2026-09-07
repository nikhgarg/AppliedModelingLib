#!/usr/bin/env python3
"""Pure pre-graph resolution of evidence identities not yet produced.

A required Lean semantic leaf cannot be named before Lean has elaborated the
declaration. This module plans those exact declaration coordinates without
inventing provisional leaf hashes or invoking a producer. Coordinates are
operational scheduling objects, never evidence or acceptance credentials.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Mapping

try:
    from scripts.obligation_evidence_contracts import (
        LEAN_DECLARATION_CONTRACT,
        RAW_SOURCE_LEAN_MATCH_CONTRACT,
    )
    from scripts.obligation_evidence_graph import (
        LeanSemanticTargetKind,
        ObligationEvidenceLeaf,
        source_lean_judgment_leaf,
    )
    from scripts.obligation_evidence_issuance import (
        EXACT_SEMANTIC_REBIND_ASSURANCE_SHA256,
        ObligationEvidenceIssuance,
        issue_obligation_evidence_attestation,
    )
    from scripts.corrected_target_identity import CORRECTED_TARGET_REVIEW_PROTOCOL
    from scripts.portable_evidence_identity import portable_evidence_sha256
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from obligation_evidence_contracts import (
        LEAN_DECLARATION_CONTRACT,
        RAW_SOURCE_LEAN_MATCH_CONTRACT,
    )
    from obligation_evidence_graph import (
        LeanSemanticTargetKind,
        ObligationEvidenceLeaf,
        source_lean_judgment_leaf,
    )
    from obligation_evidence_issuance import (
        EXACT_SEMANTIC_REBIND_ASSURANCE_SHA256,
        ObligationEvidenceIssuance,
        issue_obligation_evidence_attestation,
    )
    from corrected_target_identity import CORRECTED_TARGET_REVIEW_PROTOCOL
    from portable_evidence_identity import portable_evidence_sha256


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class ObligationResolutionError(ValueError):
    """An obligation coordinate or prior resolution is malformed."""


def _sha256(value: object, field: str) -> str:
    text = str(value or "").strip().lower()
    if not SHA256_RE.fullmatch(text):
        raise ObligationResolutionError(f"{field} is not SHA-256")
    return text


def _nonempty(value: object, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ObligationResolutionError(f"{field} is empty")
    return value.strip()


def _lean_declaration_coordinate(value: object) -> str:
    """Return one opaque declaration name already issued by Lean's graph.

    Lean names are not identifiers in Python's grammar.  In particular,
    private declarations contain numeric name components (for example
    ``_private.Module.0.Module.value``), and quoted Lean identifiers can
    contain syntax that a bounded regular expression will never recognize
    completely.  This module only constructs a non-accepting scheduling
    coordinate; the current Lean graph later proves exact declaration
    membership and identity.  Reject transport-breaking control characters,
    but do not create a second Python authority for Lean name validity.
    """

    declaration = _nonempty(value, "prerequisite declaration")
    if any(character in declaration for character in ("\x00", "\r", "\n")):
        raise ObligationResolutionError(
            "prerequisite declaration contains a transport control character"
        )
    return declaration


@dataclass(frozen=True)
class LeanDeclarationCoordinate:
    """One exact operational request for a not-yet-resolved semantic leaf."""

    declaration: str
    source_item_id: str
    semantic_target_kind: LeanSemanticTargetKind
    expected_source_input_bundle_sha256: str
    expected_display_sha256: str
    expected_declaration_content_sha256: str
    coordinate_sha256: str

    def projection(self) -> dict[str, Any]:
        return {
            "schema": 1,
            "acceptance_credential": False,
            "evidence_object": False,
            "action": "resolve_lean_declaration_identity",
            "declaration": self.declaration,
            "source_item_id": self.source_item_id,
            "semantic_target_kind": self.semantic_target_kind.value,
            "expected_source_input_bundle_sha256": (
                self.expected_source_input_bundle_sha256
            ),
            "expected_display_sha256": self.expected_display_sha256,
            "expected_declaration_content_sha256": (
                self.expected_declaration_content_sha256
            ),
            "coordinate_sha256": self.coordinate_sha256,
        }


@dataclass(frozen=True)
class LeanDeclarationResolution:
    coordinate: LeanDeclarationCoordinate
    action: str
    resolved_leaf_sha256: str | None

    def projection(self) -> dict[str, Any]:
        return {
            "coordinate": self.coordinate.projection(),
            "action": self.action,
            "resolved_leaf_sha256": self.resolved_leaf_sha256,
        }


@dataclass(frozen=True)
class SemanticPrerequisiteResolutionPlan:
    items: tuple[LeanDeclarationResolution, ...]

    @property
    def unresolved(self) -> tuple[LeanDeclarationResolution, ...]:
        return tuple(
            item
            for item in self.items
            if item.action == "materialize_lean_declaration"
        )

    @property
    def resolved(self) -> tuple[LeanDeclarationResolution, ...]:
        return tuple(item for item in self.items if item.action == "reuse_leaf")

    def projection(self) -> dict[str, Any]:
        return {
            "schema": 1,
            "acceptance_credential": False,
            "complete": not self.unresolved,
            "resolved_count": len(self.resolved),
            "unresolved_count": len(self.unresolved),
            "items": [item.projection() for item in self.items],
        }


@dataclass(frozen=True)
class CurrentSourceSemanticMaterial:
    """Current exact source inputs for one typed source-map item."""

    source_input_bundle_sha256: str
    source_atom_leaf_sha256s: tuple[str, ...]

    def projection(self) -> dict[str, Any]:
        return {
            "source_input_bundle_sha256": self.source_input_bundle_sha256,
            "source_atom_leaf_sha256s": list(self.source_atom_leaf_sha256s),
        }


@dataclass(frozen=True)
class LeanSemanticReviewBindingMaterial:
    """Bind one accepted reviewed target to current exact Lean semantics."""

    reviewed_semantic_target_sha256: str
    current_declaration_content_sha256: str
    current_lean_declaration_leaf_sha256: str

    def projection(self) -> dict[str, Any]:
        return {
            "reviewed_semantic_target_sha256": (
                self.reviewed_semantic_target_sha256
            ),
            "current_declaration_content_sha256": (
                self.current_declaration_content_sha256
            ),
            "current_lean_declaration_leaf_sha256": (
                self.current_lean_declaration_leaf_sha256
            ),
        }


@dataclass(frozen=True)
class SemanticPrerequisiteJudgmentResolution:
    """One accepted reuse or exact residual semantic-review task."""

    coordinate: LeanDeclarationCoordinate
    action: str
    reason: str
    judgment_leaf: ObligationEvidenceLeaf | None
    issuance: ObligationEvidenceIssuance | None

    def projection(self) -> dict[str, Any]:
        return {
            "coordinate": self.coordinate.projection(),
            "action": self.action,
            "reason": self.reason,
            "judgment_leaf": (
                self.judgment_leaf.projection()
                if self.judgment_leaf is not None
                else None
            ),
            "issuance": (
                self.issuance.projection() if self.issuance is not None else None
            ),
        }


@dataclass(frozen=True)
class SemanticPrerequisiteJudgmentResolutionPlan:
    items: tuple[SemanticPrerequisiteJudgmentResolution, ...]

    @property
    def reused(self) -> tuple[SemanticPrerequisiteJudgmentResolution, ...]:
        return tuple(
            item for item in self.items if item.action == "reuse_accepted_judgment"
        )

    @property
    def unresolved(self) -> tuple[SemanticPrerequisiteJudgmentResolution, ...]:
        return tuple(
            item for item in self.items if item.action != "reuse_accepted_judgment"
        )

    def projection(self) -> dict[str, Any]:
        return {
            "schema": 1,
            "acceptance_credential": False,
            "complete": not self.unresolved,
            "reused_count": len(self.reused),
            "unresolved_count": len(self.unresolved),
            "items": [item.projection() for item in self.items],
        }


def _coordinate(
    row: Mapping[str, Any],
    *,
    declaration_field: str,
    declaration_content_sha_field: str,
    semantic_target_protocol_field: str,
    semantic_target_sha_field: str,
) -> LeanDeclarationCoordinate:
    declaration = _lean_declaration_coordinate(row.get(declaration_field))
    source_item_id = _nonempty(
        row.get("source_item"), "prerequisite source item"
    )
    judgment = str(row.get("judgment") or "").strip()
    if judgment not in {"matches", "matches_approved_corrected_target"}:
        raise ObligationResolutionError(
            f"semantic prerequisite {declaration} is not an accepted match"
        )
    if judgment == "matches_approved_corrected_target":
        corrected_protocol = str(
            row.get("corrected_target_protocol") or ""
        ).strip()
        corrected_digest = str(
            row.get("corrected_target_review_sha256") or ""
        ).strip().lower()
        if (
            corrected_protocol != CORRECTED_TARGET_REVIEW_PROTOCOL
            or not SHA256_RE.fullmatch(corrected_digest)
        ):
            raise ObligationResolutionError(
                f"semantic prerequisite {declaration} has no current approved "
                "corrected-target identity"
            )
    # Validate the accepted review lane, but keep its renderer/protocol label
    # out of the coordinate identity. Exact displayed and declaration-content
    # hashes carry the material comparison.
    _nonempty(
        row.get(semantic_target_protocol_field),
        "semantic prerequisite target protocol",
    )
    expected_display = _sha256(
        row.get(semantic_target_sha_field),
        "semantic prerequisite displayed target",
    )
    expected_source = _sha256(
        row.get("source_input_bundle_sha256"),
        "semantic prerequisite source bundle",
    )
    expected_content = _sha256(
        row.get(declaration_content_sha_field),
        "semantic prerequisite declaration content",
    )
    material = {
        "schema": 1,
        "action": "resolve_lean_declaration_identity",
        "declaration": declaration,
        "semantic_target_kind": LeanSemanticTargetKind.SEMANTIC_PREREQUISITE.value,
        "expected_source_input_bundle_sha256": expected_source,
        "expected_display_sha256": expected_display,
        "expected_declaration_content_sha256": expected_content,
        "lean_declaration_contract_sha256": (
            LEAN_DECLARATION_CONTRACT.contract_sha256
        ),
    }
    return LeanDeclarationCoordinate(
        declaration=declaration,
        source_item_id=source_item_id,
        semantic_target_kind=LeanSemanticTargetKind.SEMANTIC_PREREQUISITE,
        expected_source_input_bundle_sha256=expected_source,
        expected_display_sha256=expected_display,
        expected_declaration_content_sha256=expected_content,
        coordinate_sha256=portable_evidence_sha256(material),
    )


def _ledger_coordinates(
    ledger: object,
    *,
    declaration_field: str,
    declaration_content_sha_field: str,
    semantic_target_protocol_field: str,
    semantic_target_sha_field: str,
) -> dict[str, LeanDeclarationCoordinate]:
    if not isinstance(ledger, Mapping) or ledger.get("schema") != 1:
        raise ObligationResolutionError(
            "semantic prerequisite ledger schema is unsupported"
        )
    rows = ledger.get("items")
    if not isinstance(rows, Mapping):
        raise ObligationResolutionError(
            "semantic prerequisite ledger has no item map"
        )
    result: dict[str, LeanDeclarationCoordinate] = {}
    for raw_key, raw_row in sorted(rows.items(), key=lambda item: str(item[0])):
        if not isinstance(raw_row, Mapping):
            raise ObligationResolutionError(
                "semantic prerequisite row is not an object"
            )
        coordinate = _coordinate(
            raw_row,
            declaration_field=declaration_field,
            declaration_content_sha_field=declaration_content_sha_field,
            semantic_target_protocol_field=semantic_target_protocol_field,
            semantic_target_sha_field=semantic_target_sha_field,
        )
        if str(raw_key) != coordinate.declaration:
            raise ObligationResolutionError(
                "semantic prerequisite row key disagrees with its declaration"
            )
        if coordinate.declaration in result:
            raise ObligationResolutionError(
                f"semantic prerequisite declaration is duplicated: {coordinate.declaration}"
            )
        result[coordinate.declaration] = coordinate
    return result


def semantic_prerequisite_coordinates(
    *,
    paper_prerequisites: object,
    library_semantic_review: object,
) -> Mapping[str, LeanDeclarationCoordinate]:
    """Return the one shared paper/library semantic-prerequisite inventory."""

    paper = _ledger_coordinates(
        paper_prerequisites,
        declaration_field="paper_declaration",
        declaration_content_sha_field="paper_declaration_sha256",
        semantic_target_protocol_field="paper_semantic_target_protocol",
        semantic_target_sha_field="paper_semantic_target_sha256",
    )
    library = _ledger_coordinates(
        library_semantic_review,
        declaration_field="library_declaration",
        declaration_content_sha_field="library_definition_sha256",
        semantic_target_protocol_field="library_semantic_target_protocol",
        semantic_target_sha_field="library_semantic_target_sha256",
    )
    overlap = sorted(set(paper) & set(library))
    if overlap:
        raise ObligationResolutionError(
            "paper and library prerequisite ledgers duplicate declarations: "
            + ", ".join(overlap)
        )
    return {**paper, **library}


def plan_semantic_prerequisite_resolution(
    *,
    paper_prerequisites: object,
    library_semantic_review: object,
    resolved_leaf_sha256_by_declaration: Mapping[str, object],
) -> SemanticPrerequisiteResolutionPlan:
    """Plan only unresolved declaration identities; never run Lean or review."""

    coordinates = semantic_prerequisite_coordinates(
        paper_prerequisites=paper_prerequisites,
        library_semantic_review=library_semantic_review,
    )
    unexpected = sorted(set(resolved_leaf_sha256_by_declaration) - set(coordinates))
    if unexpected:
        raise ObligationResolutionError(
            "resolved prerequisite map contains unexpected declarations: "
            + ", ".join(unexpected)
        )
    items = []
    for declaration, coordinate in sorted(coordinates.items()):
        raw_leaf = resolved_leaf_sha256_by_declaration.get(declaration)
        if raw_leaf is None:
            items.append(
                LeanDeclarationResolution(
                    coordinate=coordinate,
                    action="materialize_lean_declaration",
                    resolved_leaf_sha256=None,
                )
            )
        else:
            items.append(
                LeanDeclarationResolution(
                    coordinate=coordinate,
                    action="reuse_leaf",
                    resolved_leaf_sha256=_sha256(
                        raw_leaf, "resolved prerequisite leaf"
                    ),
                )
            )
    return SemanticPrerequisiteResolutionPlan(items=tuple(items))


def _current_source_material(
    value: object,
    *,
    source_item_id: str,
) -> CurrentSourceSemanticMaterial:
    if isinstance(value, CurrentSourceSemanticMaterial):
        return value
    if not isinstance(value, Mapping):
        raise ObligationResolutionError(
            f"current source material for {source_item_id} is not an object"
        )
    raw_atoms = value.get("source_atom_leaf_sha256s")
    if not isinstance(raw_atoms, (list, tuple)) or not raw_atoms:
        raise ObligationResolutionError(
            f"current source material for {source_item_id} has no source atoms"
        )
    atoms = tuple(sorted(_sha256(item, "current source atom leaf") for item in raw_atoms))
    if len(set(atoms)) != len(atoms):
        raise ObligationResolutionError(
            f"current source material for {source_item_id} duplicates a source atom"
        )
    return CurrentSourceSemanticMaterial(
        source_input_bundle_sha256=_sha256(
            value.get("source_input_bundle_sha256"),
            "current source input bundle",
        ),
        source_atom_leaf_sha256s=atoms,
    )


def _lean_review_binding_material(
    value: object,
    *,
    declaration: str,
) -> LeanSemanticReviewBindingMaterial:
    if isinstance(value, LeanSemanticReviewBindingMaterial):
        return value
    if not isinstance(value, Mapping):
        raise ObligationResolutionError(
            f"current Lean review material for {declaration} is not an object"
        )
    return LeanSemanticReviewBindingMaterial(
        reviewed_semantic_target_sha256=_sha256(
            value.get("reviewed_semantic_target_sha256"),
            "reviewed semantic target",
        ),
        current_declaration_content_sha256=_sha256(
            value.get("current_declaration_content_sha256"),
            "current declaration content",
        ),
        current_lean_declaration_leaf_sha256=_sha256(
            value.get("current_lean_declaration_leaf_sha256"),
            "current Lean declaration leaf",
        ),
    )


def accepted_review_targets_bound_to_current_lean_leaves(
    *,
    coordinates: Mapping[str, LeanDeclarationCoordinate],
    declaration_content_sha256_by_declaration: Mapping[str, object],
    lean_declaration_leaf_sha256_by_declaration: Mapping[str, object],
) -> Mapping[str, LeanSemanticReviewBindingMaterial]:
    """Pair accepted review targets with current independently checked leaves.

    The accepted display hash identifies exactly what the semantic reviewer
    compared.  Freshness comes from the current declaration bytes and the
    current-artifact-revalidated semantic leaf, not from rerendering that
    presentation.  A review-protocol change remains a separate receipt gate.
    """

    declarations = set(coordinates)
    for label, supplied in (
        ("declaration-content", declaration_content_sha256_by_declaration),
        ("Lean declaration leaf", lean_declaration_leaf_sha256_by_declaration),
    ):
        if set(supplied) != declarations:
            missing = sorted(declarations - set(supplied))
            unexpected = sorted(set(supplied) - declarations)
            detail = []
            if missing:
                detail.append("missing " + ", ".join(missing))
            if unexpected:
                detail.append("unexpected " + ", ".join(unexpected))
            raise ObligationResolutionError(
                f"current {label} inventory differs from prerequisites: "
                + "; ".join(detail)
            )
    return {
        declaration: LeanSemanticReviewBindingMaterial(
            reviewed_semantic_target_sha256=coordinate.expected_display_sha256,
            current_declaration_content_sha256=_sha256(
                declaration_content_sha256_by_declaration[declaration],
                "current declaration content",
            ),
            current_lean_declaration_leaf_sha256=_sha256(
                lean_declaration_leaf_sha256_by_declaration[declaration],
                "current Lean declaration leaf",
            ),
        )
        for declaration, coordinate in sorted(coordinates.items())
    }


def _coordinate_rows(
    ledger: object,
    *,
    declaration_field: str,
    declaration_content_sha_field: str,
    semantic_target_protocol_field: str,
    semantic_target_sha_field: str,
) -> dict[str, tuple[LeanDeclarationCoordinate, Mapping[str, Any]]]:
    coordinates = _ledger_coordinates(
        ledger,
        declaration_field=declaration_field,
        declaration_content_sha_field=declaration_content_sha_field,
        semantic_target_protocol_field=semantic_target_protocol_field,
        semantic_target_sha_field=semantic_target_sha_field,
    )
    assert isinstance(ledger, Mapping)
    rows = ledger["items"]
    assert isinstance(rows, Mapping)
    return {
        declaration: (coordinate, rows[declaration])
        for declaration, coordinate in coordinates.items()
    }


def bind_current_semantic_prerequisite_judgments(
    *,
    paper_prerequisites: object,
    library_semantic_review: object,
    current_source_material_by_item: Mapping[str, object],
    current_lean_material_by_declaration: Mapping[str, object],
    issuance_authority_sha256: str,
) -> SemanticPrerequisiteJudgmentResolutionPlan:
    """Reuse an accepted judgment only after exact current material rebinding.

    This is the bridge for a historical row whose accepted transaction retained
    its exact source bundle, reviewed Lean display, and declaration bytes but
    did not retain a complete per-declaration Lean manifest. The display is the
    immutable review input; its current semantic identity is established by the
    independently reproduced current declaration leaf. Missing current material
    schedules only its deterministic producer. A changed source or declaration
    schedules semantic review for that row alone.
    """

    authority = _sha256(issuance_authority_sha256, "issuance authority")
    paper = _coordinate_rows(
        paper_prerequisites,
        declaration_field="paper_declaration",
        declaration_content_sha_field="paper_declaration_sha256",
        semantic_target_protocol_field="paper_semantic_target_protocol",
        semantic_target_sha_field="paper_semantic_target_sha256",
    )
    library = _coordinate_rows(
        library_semantic_review,
        declaration_field="library_declaration",
        declaration_content_sha_field="library_definition_sha256",
        semantic_target_protocol_field="library_semantic_target_protocol",
        semantic_target_sha_field="library_semantic_target_sha256",
    )
    overlap = sorted(set(paper) & set(library))
    if overlap:
        raise ObligationResolutionError(
            "paper and library prerequisite ledgers duplicate declarations: "
            + ", ".join(overlap)
        )
    rows = {**paper, **library}
    items: list[SemanticPrerequisiteJudgmentResolution] = []
    for declaration, (coordinate, row) in sorted(rows.items()):
        raw_source = current_source_material_by_item.get(coordinate.source_item_id)
        if raw_source is None:
            items.append(
                SemanticPrerequisiteJudgmentResolution(
                    coordinate=coordinate,
                    action="resolve_current_source_material",
                    reason="current exact source bundle and atom leaves are unavailable",
                    judgment_leaf=None,
                    issuance=None,
                )
            )
            continue
        source = _current_source_material(
            raw_source,
            source_item_id=coordinate.source_item_id,
        )
        raw_lean = current_lean_material_by_declaration.get(declaration)
        if raw_lean is None:
            items.append(
                SemanticPrerequisiteJudgmentResolution(
                    coordinate=coordinate,
                    action="materialize_current_review_material",
                    reason=(
                        "current Lean display, declaration content, and semantic leaf "
                        "are unavailable"
                    ),
                    judgment_leaf=None,
                    issuance=None,
                )
            )
            continue
        lean = _lean_review_binding_material(raw_lean, declaration=declaration)
        changed: list[str] = []
        if (
            source.source_input_bundle_sha256
            != coordinate.expected_source_input_bundle_sha256
        ):
            changed.append("source bundle")
        if (
            lean.reviewed_semantic_target_sha256
            != coordinate.expected_display_sha256
        ):
            changed.append("reviewed Lean semantic target")
        if (
            lean.current_declaration_content_sha256
            != coordinate.expected_declaration_content_sha256
        ):
            changed.append("declaration content")
        if changed:
            items.append(
                SemanticPrerequisiteJudgmentResolution(
                    coordinate=coordinate,
                    action="run_semantic_review",
                    reason="accepted comparison changed: " + ", ".join(changed),
                    judgment_leaf=None,
                    issuance=None,
                )
            )
            continue
        judgment = source_lean_judgment_leaf(
            contract_sha256=RAW_SOURCE_LEAN_MATCH_CONTRACT.contract_sha256,
            source_atom_sha256s=source.source_atom_leaf_sha256s,
            lean_declaration_sha256=lean.current_lean_declaration_leaf_sha256,
            verbatim_source_bundle_sha256=source.source_input_bundle_sha256,
            verdict=str(row.get("judgment") or ""),
        )
        evidence_record_sha256 = portable_evidence_sha256(
            {
                "schema": 1,
                "accepted_review_row": dict(row),
                "current_source_material": source.projection(),
                "current_lean_material": lean.projection(),
                "judgment_leaf_sha256": judgment.leaf_sha256,
            }
        )
        issuance = issue_obligation_evidence_attestation(
            leaf_sha256=judgment.leaf_sha256,
            assurance_contract_sha256=EXACT_SEMANTIC_REBIND_ASSURANCE_SHA256,
            authority_sha256=authority,
            evidence_record_sha256=evidence_record_sha256,
        )
        items.append(
            SemanticPrerequisiteJudgmentResolution(
                coordinate=coordinate,
                action="reuse_accepted_judgment",
                reason=(
                    "accepted row is bound to the current source bundle, exact "
                    "declaration content, and independently revalidated semantic leaf"
                ),
                judgment_leaf=judgment,
                issuance=issuance,
            )
        )
    return SemanticPrerequisiteJudgmentResolutionPlan(items=tuple(items))
