#!/usr/bin/env python3
"""Project already-validated v11 claims into portable obligation evidence.

This adapter does not validate a final paper closeout and does not invoke Lean
or an LLM.  Its caller must first authenticate the accepted transaction and
the exact current input carriers with their existing strict validators.  The
adapter then projects direct v11 source/Spec/proof facts into the portable leaf
schemas without using names, paths, lines, timestamps, or engine versions as
semantic identities.

Only the direct v11 claim subgraph is projected here.  Raw recursive/component
review, source-scope dispositions, prerequisites, and the focused build remain
separate authenticated inputs. Consequently this module cannot publish a
complete paper-closeout graph by itself. Fresh closeout and historical
migration call the same deterministic projector after their distinct
authorities have validated those inputs.
"""

from __future__ import annotations

import hashlib
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.source_claim_atom_schema import (
    graph_native_source_spec_realization_identity_sha256,
    obligation_source_component_sha256,
    source_claim_atom_semantic_sha256,
    source_claim_atoms_semantic_sha256,
    source_spec_correspondence_item_identity_sha256,
)
from scripts.obligation_evidence_contracts import (
    FOCUSED_BUILD_CONTRACT,
    LEAN_DECLARATION_CONTRACT,
    LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT,
    LEAN_PROOF_ENDPOINT_CONTRACT,
    LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT,
    PROOF_REALIZATION_CONTRACT,
    RAW_SOURCE_LEAN_MATCH_CONTRACT,
    SOURCE_ATOM_CONTRACT,
)
from scripts.obligation_evidence_graph import (
    LeanSemanticTargetKind,
    ObligationEvidenceGraph,
    ObligationEvidenceLeaf,
    ProofRealizationMode,
    build_evidence_leaf,
    build_obligation_graph,
    lean_declaration_leaf,
    lean_proof_endpoint_leaf,
    lean_reviewed_semantic_prerequisite_leaf,
    lean_reviewed_semantic_target_leaf,
    proof_realization_leaf,
    source_atom_leaf,
    source_lean_judgment_leaf,
)
from scripts.obligation_evidence_issuance import (
    ObligationEvidenceIssuance,
    issue_obligation_evidence_attestation,
)
from scripts.obligation_preflight import ObligationStructuralPreflight
from scripts.obligation_routes import (
    EvidenceRouteSet,
    ObligationRouteError,
    source_item_primary_anchor_sha256s,
)
from scripts.paper_build_command import is_exact_portable_paper_build_command
from scripts.portable_evidence_identity import (
    canonical_json_bytes,
    portable_evidence_sha256,
)
from scripts.corrected_target_identity import (
    corrected_target_approval_excerpt_material,
    corrected_target_screening_binding_is_current,
)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
DIRECT_V11_PROJECTION_SCHEMA = 1

SOURCE_ATOM_CONTRACT_SHA256 = SOURCE_ATOM_CONTRACT.contract_sha256
LEAN_DECLARATION_CONTRACT_SHA256 = LEAN_DECLARATION_CONTRACT.contract_sha256
LEAN_PROOF_ENDPOINT_CONTRACT_SHA256 = LEAN_PROOF_ENDPOINT_CONTRACT.contract_sha256
LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT_SHA256 = (
    LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT.contract_sha256
)
PROOF_REALIZATION_CONTRACT_SHA256 = PROOF_REALIZATION_CONTRACT.contract_sha256
SOURCE_LEAN_JUDGMENT_CONTRACT_SHA256 = RAW_SOURCE_LEAN_MATCH_CONTRACT.contract_sha256
FOCUSED_BUILD_CONTRACT_SHA256 = FOCUSED_BUILD_CONTRACT.contract_sha256


class ObligationEvidenceProjectionError(ValueError):
    """Validated historical carriers cannot project the required exact leaf."""


def _sha256(value: object, field: str) -> str:
    text = str(value or "").strip().lower()
    if not SHA256_RE.fullmatch(text):
        raise ObligationEvidenceProjectionError(f"{field} is not SHA-256")
    return text


def _mapping(value: object, field: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ObligationEvidenceProjectionError(f"{field} is not an object")
    return value


def _nonempty(value: object, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ObligationEvidenceProjectionError(f"{field} is empty")
    return value.strip()


def _record_sha256(value: object) -> str:
    """Hash an exact legacy provenance record without making it leaf identity."""

    return hashlib.sha256(canonical_json_bytes(value)).hexdigest()


def _issuance(
    leaf: ObligationEvidenceLeaf,
    *,
    issuance_authority_sha256: str,
    issuance_assurance_contract_sha256: str,
    evidence_record: object,
) -> ObligationEvidenceIssuance:
    return issue_obligation_evidence_attestation(
        leaf_sha256=leaf.leaf_sha256,
        assurance_contract_sha256=issuance_assurance_contract_sha256,
        authority_sha256=issuance_authority_sha256,
        evidence_record_sha256=_record_sha256(evidence_record),
    )


def _manifest_index(value: object) -> dict[str, Mapping[str, Any]]:
    payload = _mapping(value, "manifest authority")
    if payload.get("schema") != 1 or not isinstance(payload.get("entries"), list):
        raise ObligationEvidenceProjectionError(
            "manifest authority schema is unsupported"
        )
    result: dict[str, Mapping[str, Any]] = {}
    required = {
        "authority_binding_sha256",
        "context_id",
        "elaborated_proposition_graph_sha256",
        "elaborated_signature_sha256",
        "manifest_payload_sha256",
        "qualified_declaration",
        "semantic_dependency_sha256",
    }
    for raw in payload["entries"]:
        entry = _mapping(raw, "manifest authority entry")
        if set(entry) != required:
            raise ObligationEvidenceProjectionError(
                "manifest authority entry fields are malformed"
            )
        declaration = _nonempty(
            entry.get("qualified_declaration"), "manifest declaration"
        )
        for field in required - {"qualified_declaration"}:
            _sha256(entry.get(field), f"manifest {field}")
        if declaration in result:
            raise ObligationEvidenceProjectionError(
                f"manifest authority duplicates {declaration}"
            )
        result[declaration] = entry
    return result


def _lean_leaf(
    manifests: Mapping[str, Mapping[str, Any]],
    declaration: str,
    target_kind: LeanSemanticTargetKind,
) -> ObligationEvidenceLeaf:
    try:
        manifest = manifests[declaration]
    except KeyError as exc:
        raise ObligationEvidenceProjectionError(
            f"manifest authority omits {declaration}"
        ) from exc
    return lean_declaration_leaf(
        contract_sha256=LEAN_DECLARATION_CONTRACT_SHA256,
        semantic_target_kind=target_kind,
        elaborated_signature_sha256=manifest["elaborated_signature_sha256"],
        elaborated_proposition_graph_sha256=manifest[
            "elaborated_proposition_graph_sha256"
        ],
        semantic_dependency_sha256=manifest["semantic_dependency_sha256"],
    )


def _source_role_contract(item: Mapping[str, Any]) -> str:
    corrected_target = item.get("corrected_target")
    corrected_semantics: object = None
    if corrected_target is not None:
        target = _mapping(corrected_target, "corrected target")
        approval = _mapping(target.get("approval"), "corrected-target approval")
        defect_ids = target.get("governing_defect_ids")
        if not isinstance(defect_ids, list) or any(
            not isinstance(value, str) or not value.strip() for value in defect_ids
        ):
            raise ObligationEvidenceProjectionError(
                "corrected-target governing defect IDs are malformed"
            )
        approval_excerpt = corrected_target_approval_excerpt_material(approval)
        if approval_excerpt is not None:
            approval_authority_kind = "unique_normalized_artifact_excerpt"
            approval_authority_sha256 = approval_excerpt[1]
        else:
            approval_authority_kind = "historical_whole_artifact"
            approval_authority_sha256 = _sha256(
                approval.get("artifact_sha256"),
                "corrected-target approval artifact",
            )
        corrected_semantics = {
            "schema": target.get("schema"),
            "statement": _nonempty(
                target.get("statement"), "corrected-target statement"
            ),
            "governing_defect_ids": sorted(value.strip() for value in defect_ids),
            "archival_equivalence_claimed": target.get("archival_equivalence_claimed"),
            "archival_source_quote_sha256": _sha256(
                target.get("archival_source_quote_sha256"),
                "corrected-target source quote",
            ),
            "approval_kind": _nonempty(
                approval.get("kind"), "corrected-target approval kind"
            ),
            "approval_target_statement_sha256": _sha256(
                approval.get("target_statement_sha256"),
                "corrected-target approved statement",
            ),
            "approval_authority_kind": approval_authority_kind,
            "approval_authority_sha256": approval_authority_sha256,
        }
    semantic_fields = (
        "source_kind",
        "claim_bearing",
        "coverage_status",
        "inventory_role",
        "protocol_role",
        "source_scope_classification",
        "user_approved_scope_exclusion",
        "scope_disposition",
    )
    projection = {field: item[field] for field in semantic_fields if field in item}
    if corrected_semantics is not None:
        projection["corrected_target_semantics"] = corrected_semantics
    return portable_evidence_sha256({"schema": 1, "source_role": projection})


def _quote_digests(item: Mapping[str, Any]) -> set[str]:
    try:
        return set(source_item_primary_anchor_sha256s(item))
    except ObligationRouteError as exc:
        raise ObligationEvidenceProjectionError(str(exc)) from exc


def _source_leaves(
    *,
    item: Mapping[str, Any],
    source_artifact_sha256: str,
) -> tuple[ObligationEvidenceLeaf, ...]:
    leaves = _source_atom_leaves(
        item=item, source_artifact_sha256=source_artifact_sha256
    )
    atoms = item.get("source_claim_atoms")
    if not isinstance(atoms, list) or not atoms:
        raise ObligationEvidenceProjectionError("direct v11 item has no source atoms")
    current_atoms_sha = source_claim_atoms_semantic_sha256(atoms)
    if not current_atoms_sha:
        raise ObligationEvidenceProjectionError("source-claim atoms are malformed")
    correspondence = _mapping(
        item.get("source_spec_correspondence"), "source_spec_correspondence"
    )
    if (
        _sha256(
            correspondence.get("source_atoms_sha256"),
            "correspondence source atoms",
        )
        != current_atoms_sha
    ):
        raise ObligationEvidenceProjectionError(
            "source correspondence does not bind the current atoms"
        )
    return leaves


def _validated_graph_native_realization_receipt(
    *,
    source_item_id: str,
    item: Mapping[str, Any],
    contract: Mapping[str, Any],
    receipt: object,
) -> Mapping[str, Any]:
    """Validate one graph-native replacement for the legacy worksheet."""

    raw = _mapping(receipt, "graph-native realization receipt")
    required = {
        "authority",
        "source_item_key",
        "spec_declaration",
        "evidence_declaration",
        "evidence_mode",
        "semantic_shape",
        "source_atoms_sha256",
        "item_identity_sha256",
        "spec_closure_sha256",
        "spec_surface_sha256",
        "closure_environment_sha256",
    }
    if set(raw) != required or raw.get("authority") != "v11_graph_native_v1":
        raise ObligationEvidenceProjectionError(
            "graph-native realization receipt is malformed"
        )
    atoms_sha = source_claim_atoms_semantic_sha256(item.get("source_claim_atoms"))
    expected_fields = {
        "source_item_key": source_item_id,
        "spec_declaration": str(contract.get("spec_declaration") or "").strip(),
        "evidence_declaration": str(contract.get("evidence_declaration") or "").strip(),
        "evidence_mode": str(contract.get("evidence_mode") or "").strip(),
        "semantic_shape": str(contract.get("semantic_shape") or "").strip(),
        "source_atoms_sha256": atoms_sha,
    }
    if any(str(raw.get(field) or "").strip() != value for field, value in expected_fields.items()):
        raise ObligationEvidenceProjectionError(
            "graph-native realization receipt belongs to a different source route"
        )
    closure_sha = _sha256(raw.get("spec_closure_sha256"), "Spec closure")
    surface_sha = _sha256(raw.get("spec_surface_sha256"), "Spec surface")
    environment_sha = _sha256(
        raw.get("closure_environment_sha256"), "Spec closure environment"
    )
    expected_identity = graph_native_source_spec_realization_identity_sha256(
        contract,
        source_atoms_sha256=atoms_sha,
        spec_closure_sha256=closure_sha,
        spec_surface_sha256=surface_sha,
        closure_environment_sha256=environment_sha,
    )
    if _sha256(raw.get("item_identity_sha256"), "realization identity") != expected_identity:
        raise ObligationEvidenceProjectionError(
            "graph-native realization receipt identity is stale"
        )
    return raw


def _source_atom_leaves(
    *,
    item: Mapping[str, Any],
    source_artifact_sha256: str,
) -> tuple[ObligationEvidenceLeaf, ...]:
    """Project explicit claim atoms or exact source anchors without locators."""

    # Validate every displayed source anchor. A source atom may intentionally
    # identify a narrower exact line slice inside that larger verbatim bundle,
    # so its independently validated quote digest need not equal the whole
    # anchor digest.
    anchor_digests = _quote_digests(item)
    role_contract = _source_role_contract(item)
    atoms = item.get("source_claim_atoms")
    leaves: list[ObligationEvidenceLeaf] = []
    if isinstance(atoms, list) and atoms:
        for raw in atoms:
            atom = _mapping(raw, "source atom")
            quote_sha = _sha256(atom.get("source_quote_sha256"), "source atom quote")
            # Validate the historical human decomposition as provenance, but
            # never use its paraphrase, ID, route name, locator, or order as
            # source semantics. The shared source-atom schema distinguishes
            # exact clauses within one quote by their verbatim bytes.
            _nonempty(atom.get("semantic_claim"), "source atom claim")
            component_sha = obligation_source_component_sha256(atom)
            if not component_sha:
                raise ObligationEvidenceProjectionError(
                    "source atom has no valid shared source-component identity"
                )
            leaves.append(
                source_atom_leaf(
                    contract_sha256=SOURCE_ATOM_CONTRACT_SHA256,
                    source_artifact_sha256=source_artifact_sha256,
                    source_quote_sha256=quote_sha,
                    source_component_sha256=component_sha,
                    source_role_contract_sha256=role_contract,
                )
            )
    else:
        semantic_claim = _nonempty(item.get("statement"), "source item statement")
        for quote_sha in sorted(anchor_digests):
            leaves.append(
                source_atom_leaf(
                    contract_sha256=SOURCE_ATOM_CONTRACT_SHA256,
                    source_artifact_sha256=source_artifact_sha256,
                    source_quote_sha256=quote_sha,
                    source_component_sha256=portable_evidence_sha256(
                        {
                            "schema": 1,
                            "source_quote_sha256": quote_sha,
                            "semantic_claim": " ".join(semantic_claim.split()),
                        }
                    ),
                    source_role_contract_sha256=role_contract,
                )
            )
    if len({leaf.leaf_sha256 for leaf in leaves}) != len(leaves):
        raise ObligationEvidenceProjectionError(
            "source item has duplicate source-atom leaf semantics"
        )
    return tuple(leaves)


def _validate_direct_judgment_protocol(
    screening: Mapping[str, Any], row: Mapping[str, Any]
) -> str:
    """Validate the accepted legacy lane, then return the stable obligation.

    Prompt names and rendering protocol versions authenticate how the legacy
    record was issued.  They are not part of the mathematical comparison once
    that accepted record has been projected onto exact source and Lean leaves.
    A genuinely stronger future comparison is represented by a new obligation
    contract, not by every prompt-text or engine revision.
    """

    _nonempty(screening.get("prompt_version"), "v11 prompt version")
    _nonempty(row.get("source_input_protocol"), "source input protocol")
    _nonempty(row.get("lean_target_protocol"), "Lean target protocol")
    return SOURCE_LEAN_JUDGMENT_CONTRACT_SHA256


def _portable_correspondence_identity(
    *,
    atoms: list[Mapping[str, Any]],
    atom_leaves: tuple[ObligationEvidenceLeaf, ...],
    correspondence: Mapping[str, Any],
    spec_leaf_sha256: str,
    endpoint_leaf_sha256: str,
    relation: ProofRealizationMode,
) -> str:
    """Project a validated legacy correspondence without locator-bound hashes."""

    # Bindings use the current legacy atom digest, so construct the migration
    # mapping through the current validator's public single-atom authority.
    legacy_to_leaf = {
        source_claim_atom_semantic_sha256(atom): leaf.leaf_sha256
        for atom, leaf in zip(atoms, atom_leaves)
    }
    if any(not key for key in legacy_to_leaf) or len(legacy_to_leaf) != len(atoms):
        raise ObligationEvidenceProjectionError(
            "source atoms cannot be associated with portable leaves"
        )

    raw_bindings = correspondence.get("source_atom_bindings")
    if not isinstance(raw_bindings, list) or len(raw_bindings) != len(atoms):
        raise ObligationEvidenceProjectionError(
            "source correspondence atom bindings are incomplete"
        )
    bindings = []
    for raw_binding in raw_bindings:
        binding = _mapping(raw_binding, "source correspondence atom binding")
        legacy_atom = _sha256(
            binding.get("source_atom_sha256"), "correspondence source atom"
        )
        try:
            leaf_sha = legacy_to_leaf[legacy_atom]
        except KeyError as exc:
            raise ObligationEvidenceProjectionError(
                "source correspondence binding names a different atom"
            ) from exc
        components = binding.get("spec_component_sha256s")
        if not isinstance(components, list) or not components:
            raise ObligationEvidenceProjectionError(
                "source correspondence binding has no Spec components"
            )
        bindings.append(
            {
                "source_atom_leaf_sha256": leaf_sha,
                "spec_component_sha256s": sorted(
                    _sha256(component, "Spec component") for component in components
                ),
            }
        )

    raw_dispositions = correspondence.get("closure_node_dispositions")
    if not isinstance(raw_dispositions, list):
        raise ObligationEvidenceProjectionError(
            "source correspondence node dispositions are malformed"
        )
    dispositions = []
    for raw_disposition in raw_dispositions:
        disposition = _mapping(raw_disposition, "closure node disposition")
        projected: dict[str, Any] = {
            "closure_component_sha256": _sha256(
                disposition.get("closure_component_sha256"),
                "closure disposition component",
            )
        }
        legacy_atom = disposition.get("source_atom_sha256")
        if legacy_atom is not None:
            try:
                projected["source_atom_leaf_sha256"] = legacy_to_leaf[
                    _sha256(legacy_atom, "closure disposition source atom")
                ]
            except KeyError as exc:
                raise ObligationEvidenceProjectionError(
                    "closure disposition names a different source atom"
                ) from exc
        basis = disposition.get("semantic_basis")
        if basis is not None:
            semantic_basis = _mapping(basis, "closure disposition semantic basis")
            projected["semantic_basis"] = {
                "artifact_sha256": _sha256(
                    semantic_basis.get("artifact_sha256"),
                    "semantic-basis artifact",
                ),
                "semantic_statement": _nonempty(
                    semantic_basis.get("semantic_statement"),
                    "semantic-basis statement",
                ),
            }
        declaration_pin = disposition.get("pinned_declaration_identity_sha256")
        if declaration_pin is not None:
            projected["pinned_declaration_identity_sha256"] = _sha256(
                declaration_pin, "closure disposition declaration"
            )
        dispositions.append(projected)

    return portable_evidence_sha256(
        {
            "schema": 1,
            "spec_leaf_sha256": spec_leaf_sha256,
            "endpoint_leaf_sha256": endpoint_leaf_sha256,
            "relation": relation.value,
            "source_atom_bindings": sorted(
                bindings, key=lambda value: value["source_atom_leaf_sha256"]
            ),
            "closure_node_dispositions": sorted(
                dispositions,
                key=lambda value: value["closure_component_sha256"],
            ),
            "spec_closure_sha256": _sha256(
                correspondence.get("spec_closure_sha256"), "Spec closure"
            ),
            "spec_surface_sha256": _sha256(
                correspondence.get("spec_surface_sha256"), "Spec surface"
            ),
            "closure_environment_sha256": _sha256(
                correspondence.get("closure_environment_sha256"),
                "Spec closure environment",
            ),
        }
    )


def _validate_direct_judgment_attestation(
    screening: Mapping[str, Any],
    row: Mapping[str, Any],
    *,
    source_item_id: str,
) -> None:
    """Fail closed on accepted v11 attestations without hashing prose into a leaf."""

    _nonempty(screening.get("validator"), "v11 validator")
    _sha256(row.get("source_input_bundle_sha256"), "source input bundle")
    _sha256(row.get("lean_expanded_statement_sha256"), "expanded Lean statement")
    _sha256(row.get("paper_statement_sha256"), "paper statement")
    _nonempty(row.get("reason"), "v11 review reason")
    if screening.get("schema") == 3:
        if _nonempty(row.get("source_item"), "v11 source item") != source_item_id:
            raise ObligationEvidenceProjectionError(
                "schema-3 screening row names a different source item"
            )
        _sha256(
            row.get("source_review_target_sha256"),
            "source review target",
        )
        _sha256(
            row.get("review_claim_manifest_sha256"),
            "Lean review-claim manifest",
        )
        _sha256(
            row.get("review_claim_atoms_sha256"),
            "Lean review-claim atoms",
        )


@dataclass(frozen=True)
class DirectV11LeafProjection:
    """One integrity-only direct-claim subgraph and its navigation index."""

    graph: ObligationEvidenceGraph
    navigation: Mapping[str, Mapping[str, Any]]
    issuances: tuple[ObligationEvidenceIssuance, ...]
    issuance_authority_sha256: str

    def projection(self) -> dict[str, Any]:
        return {
            "schema": DIRECT_V11_PROJECTION_SCHEMA,
            "acceptance_credential": False,
            "complete_paper_closeout_graph": False,
            "issuance_authority_sha256": self.issuance_authority_sha256,
            "graph": self.graph.projection(),
            "issuances": [issuance.projection() for issuance in self.issuances],
            "navigation": {
                key: dict(value) for key, value in sorted(self.navigation.items())
            },
        }


@dataclass(frozen=True)
class ValidatedDirectV11Claim:
    """One normalized direct claim shared by projection and terminal checks."""

    source_item_id: str
    item: Mapping[str, Any]
    contract: Mapping[str, Any]
    spec_name: str
    endpoint_name: str
    relation: ProofRealizationMode
    review_name: str
    review_kind: LeanSemanticTargetKind
    screening_row: Mapping[str, Any]


def validated_direct_v11_claims(
    *,
    source_map: object,
    v11_screening: object,
    route_set: EvidenceRouteSet,
) -> tuple[str, tuple[ValidatedDirectV11Claim, ...]]:
    """Validate and normalize the one direct-v11 semantic surface."""

    source = _mapping(source_map, "paper statement map")
    source_artifact = _sha256(source.get("source_artifact_sha256"), "source artifact")
    items = _mapping(source.get("items"), "paper statement-map items")
    screening = _mapping(v11_screening, "v11 screening")
    if screening.get("schema") not in {2, 3}:
        raise ObligationEvidenceProjectionError("v11 screening schema is unsupported")
    screening_items = _mapping(screening.get("items"), "v11 screening items")
    claims: list[ValidatedDirectV11Claim] = []
    screened_targets: set[str] = set()
    result_routes = route_set.result_routes()
    for route in sorted(result_routes, key=lambda value: value.source_item_id):
        source_item_id = route.source_item_id
        try:
            item = _mapping(items[source_item_id], f"source item {source_item_id}")
            relation = ProofRealizationMode(route.evidence_mode)
            review_kind = LeanSemanticTargetKind(
                route.semantic_review_target_kind.value
            )
        except (KeyError, ValueError) as exc:
            raise ObligationEvidenceProjectionError(
                f"typed result route is not projectable: {source_item_id}"
            ) from exc
        spec_name = route.spec_declaration
        endpoint_name = route.evidence_declaration
        review_name = route.semantic_review_declaration
        contract = {
            "spec_declaration": spec_name,
            "evidence_declaration": endpoint_name,
            "evidence_mode": relation.value,
            "semantic_shape": "plain",
        }
        if review_name != spec_name:
            raise ObligationEvidenceProjectionError(
                "direct v11 projection requires the reviewed semantic target "
                "to be the registered Spec declaration"
            )
        try:
            row = _mapping(screening_items[review_name], "v11 screening row")
        except KeyError as exc:
            raise ObligationEvidenceProjectionError(
                f"current direct-v11 material omits {review_name}"
            ) from exc
        if (
            _nonempty(
                row.get("semantic_target_declaration"), "screening target declaration"
            )
            != review_name
        ):
            raise ObligationEvidenceProjectionError(
                "screening row is indexed under a different declaration"
            )
        judgment = row.get("judgment")
        if judgment not in {"matches", "matches_approved_corrected_target"}:
            raise ObligationEvidenceProjectionError(
                f"screening target {review_name} is not an accepted match"
            )
        if judgment == "matches_approved_corrected_target":
            corrected_target = _mapping(
                item.get("corrected_target"), "approved corrected target"
            )
            if (
                not corrected_target_screening_binding_is_current(
                    row, corrected_target
                )
                or corrected_target.get("archival_equivalence_claimed") is not False
            ):
                raise ObligationEvidenceProjectionError(
                    f"screening target {review_name} has no exact approved correction"
                )
        _validate_direct_judgment_attestation(
            screening,
            row,
            source_item_id=source_item_id,
        )
        _validate_direct_judgment_protocol(screening, row)
        screened_targets.add(review_name)
        claims.append(
            ValidatedDirectV11Claim(
                source_item_id=str(source_item_id),
                item=item,
                contract=contract,
                spec_name=spec_name,
                endpoint_name=endpoint_name,
                relation=relation,
                review_name=review_name,
                review_kind=review_kind,
                screening_row=row,
            )
        )
    if not claims:
        raise ObligationEvidenceProjectionError(
            "validated inputs contain no direct v11 semantic contracts"
        )
    unexpected_screening = sorted(set(screening_items) - screened_targets)
    if unexpected_screening:
        raise ObligationEvidenceProjectionError(
            "v11 screening has rows outside the direct statement-map targets: "
            + ", ".join(unexpected_screening)
        )
    return source_artifact, tuple(claims)


def validate_current_direct_v11_semantic_targets(
    *,
    claims: tuple[ValidatedDirectV11Claim, ...],
    current_semantic_targets: Mapping[str, object],
) -> None:
    """Require Lean's current transparent targets to equal the reviewed ones."""

    expected = {claim.review_name for claim in claims}
    if set(current_semantic_targets) != expected:
        raise ObligationEvidenceProjectionError(
            "current Lean semantic-target inventory differs from the v11 claims"
        )
    for claim in claims:
        raw_target = current_semantic_targets.get(claim.review_name)
        target = _mapping(raw_target, f"current Lean target {claim.review_name}")
        current_digest = _sha256(
            target.get("display_sha256"),
            f"current Lean target {claim.review_name}",
        )
        reviewed_digest = _sha256(
            claim.screening_row.get("lean_expanded_statement_sha256"),
            f"reviewed Lean target {claim.review_name}",
        )
        if current_digest != reviewed_digest:
            raise ObligationEvidenceProjectionError(
                f"current Lean semantic target changed: {claim.review_name}"
            )


@dataclass(frozen=True)
class SemanticPrerequisiteLeafProjection:
    """Paper/library-neutral prerequisite judgment subgraph."""

    graph: ObligationEvidenceGraph
    navigation: Mapping[str, Mapping[str, Any]]
    issuances: tuple[ObligationEvidenceIssuance, ...]
    unresolved_declarations: tuple[str, ...]
    issuance_authority_sha256: str

    def projection(self) -> dict[str, Any]:
        return {
            "schema": 1,
            "acceptance_credential": False,
            "complete_paper_closeout_graph": False,
            "issuance_authority_sha256": self.issuance_authority_sha256,
            "graph": self.graph.projection(),
            "issuances": [issuance.projection() for issuance in self.issuances],
            "unresolved_declarations": list(self.unresolved_declarations),
            "navigation": {
                key: dict(value) for key, value in sorted(self.navigation.items())
            },
        }


@dataclass(frozen=True)
class SourceRouteLeafProjection:
    """Complete exact-source subgraph for every preflight route."""

    graph: ObligationEvidenceGraph
    navigation: Mapping[str, tuple[str, ...]]
    issuances: tuple[ObligationEvidenceIssuance, ...]
    issuance_authority_sha256: str

    def projection(self) -> dict[str, Any]:
        return {
            "schema": 1,
            "acceptance_credential": False,
            "complete_paper_closeout_graph": False,
            "issuance_authority_sha256": self.issuance_authority_sha256,
            "graph": self.graph.projection(),
            "issuances": [issuance.projection() for issuance in self.issuances],
            "navigation": {
                source_item_id: list(digests)
                for source_item_id, digests in sorted(self.navigation.items())
            },
        }


@dataclass(frozen=True)
class FocusedBuildLeafProjection:
    leaf: ObligationEvidenceLeaf
    issuance: ObligationEvidenceIssuance
    issuance_authority_sha256: str

    def projection(self) -> dict[str, Any]:
        return {
            "schema": 1,
            "acceptance_credential": False,
            "issuance_authority_sha256": self.issuance_authority_sha256,
            "leaf": self.leaf.projection(),
            "issuance": self.issuance.projection(),
        }


def project_focused_build_leaf_from_validated_inputs(
    *,
    focused_build_receipt: object,
    lean_import_closure_receipt: object,
    target_leaf_sha256s: tuple[str, ...],
    issuance_authority_sha256: str,
    issuance_assurance_contract_sha256: str,
) -> FocusedBuildLeafProjection:
    """Project a passed focused build onto portable current-control material."""

    issuance_authority = _sha256(issuance_authority_sha256, "issuance authority")
    assurance_contract = _sha256(
        issuance_assurance_contract_sha256, "issuance assurance contract"
    )
    focused = _mapping(focused_build_receipt, "focused build receipt")
    closure_receipt = _mapping(
        lean_import_closure_receipt, "Lean import closure receipt"
    )
    if focused.get("schema") not in {1, 2, 3}:
        raise ObligationEvidenceProjectionError(
            "focused build receipt schema is unsupported"
        )
    if focused.get("result") != "passed":
        raise ObligationEvidenceProjectionError("focused build did not pass")
    paper = _nonempty(focused.get("paper"), "focused build paper")
    if (
        closure_receipt.get("schema") != 1
        or closure_receipt.get("acceptance_credential") is not False
        or _nonempty(closure_receipt.get("paper"), "closure receipt paper") != paper
    ):
        raise ObligationEvidenceProjectionError(
            "Lean import closure receipt schema or paper is unsupported"
        )
    command = _nonempty(focused.get("command"), "focused build command")
    target = _nonempty(focused.get("target"), "focused build target")
    if not is_exact_portable_paper_build_command(command, target):
        raise ObligationEvidenceProjectionError(
            "focused build command is not the exact portable paper target"
        )
    canonical_argv = ["lake", "build", target]
    closure = _mapping(
        closure_receipt.get("lean_import_closure"), "Lean import closure"
    )
    closure_sha256 = _sha256(
        closure_receipt.get("lean_import_closure_sha256"),
        "Lean import closure",
    )
    if portable_evidence_sha256(closure) != closure_sha256:
        raise ObligationEvidenceProjectionError("Lean import closure identity is stale")
    focused_schema = focused.get("schema")
    if focused_schema == 3 and (
        _sha256(
            focused.get("lean_import_closure_sha256"),
            "focused build Lean import closure",
        )
        != closure_sha256
        or _nonempty(focused.get("lean_entrypoint"), "focused build Lean entrypoint")
        != _nonempty(closure.get("entrypoint"), "Lean import closure entrypoint")
    ):
        raise ObligationEvidenceProjectionError(
            "focused build receipt and Lean import closure disagree"
        )
    controls = closure.get("build_controls")
    if not isinstance(controls, list):
        raise ObligationEvidenceProjectionError(
            "Lean import closure has no build controls"
        )
    toolchains = [
        control
        for control in controls
        if isinstance(control, Mapping) and control.get("path") == "lean-toolchain"
    ]
    if len(toolchains) != 1:
        raise ObligationEvidenceProjectionError(
            "Lean import closure does not identify one toolchain"
        )
    toolchain_sha256 = _sha256(toolchains[0].get("sha256"), "Lean toolchain")
    target_leaves = tuple(
        sorted(
            _sha256(value, "focused build target leaf") for value in target_leaf_sha256s
        )
    )
    if not target_leaves or len(set(target_leaves)) != len(target_leaves):
        raise ObligationEvidenceProjectionError(
            "focused build target leaves are empty or duplicated"
        )
    leaf = build_evidence_leaf(
        contract_sha256=FOCUSED_BUILD_CONTRACT_SHA256,
        target_declaration_sha256s=target_leaves,
        build_command_sha256=portable_evidence_sha256(
            {"schema": 1, "argv": canonical_argv}
        ),
        toolchain_sha256=toolchain_sha256,
        lean_import_closure_sha256=closure_sha256,
    )
    issuance = _issuance(
        leaf,
        issuance_authority_sha256=issuance_authority,
        issuance_assurance_contract_sha256=assurance_contract,
        evidence_record={
            "focused_build_receipt": focused,
            "lean_import_closure_receipt": closure_receipt,
        },
    )
    return FocusedBuildLeafProjection(
        leaf=leaf,
        issuance=issuance,
        issuance_authority_sha256=issuance_authority,
    )


def _project_source_route_leaf_material(
    *,
    source_map: object,
    preflight: ObligationStructuralPreflight,
) -> tuple[
    Mapping[str, ObligationEvidenceLeaf],
    Mapping[str, tuple[str, ...]],
]:
    """Project exact source leaves and navigation without issuing evidence."""

    if not isinstance(preflight, ObligationStructuralPreflight):
        raise ObligationEvidenceProjectionError(
            "source-route projection requires the nominal structural preflight"
        )
    try:
        preflight.require_current()
    except ValueError as exc:
        raise ObligationEvidenceProjectionError(str(exc)) from exc
    source = _mapping(source_map, "paper statement map")
    if source.get("paper") != preflight.paper:
        raise ObligationEvidenceProjectionError(
            "source map belongs to a different structural preflight"
        )
    source_artifact = _sha256(source.get("source_artifact_sha256"), "source artifact")
    if source_artifact != preflight.source_artifact_sha256:
        raise ObligationEvidenceProjectionError(
            "source map artifact differs from structural preflight"
        )
    items = _mapping(source.get("items"), "paper statement-map items")
    expected_items = set(preflight.route_obligation_counts)
    if set(items) != expected_items:
        raise ObligationEvidenceProjectionError(
            "source-map items differ from structural preflight"
        )
    leaves: dict[str, ObligationEvidenceLeaf] = {}
    navigation: dict[str, tuple[str, ...]] = {}
    for source_item_id, raw_item in sorted(
        items.items(), key=lambda entry: str(entry[0])
    ):
        item = _mapping(raw_item, f"source item {source_item_id}")
        source_leaves = _source_atom_leaves(
            item=item,
            source_artifact_sha256=source_artifact,
        )
        actual_quotes = tuple(
            sorted(
                str(leaf.semantic_payload["source_quote_sha256"])
                for leaf in source_leaves
            )
        )
        if actual_quotes != preflight.route_source_quote_sha256s[source_item_id]:
            raise ObligationEvidenceProjectionError(
                f"source route {source_item_id} differs from structural preflight"
            )
        navigation[str(source_item_id)] = tuple(
            sorted(leaf.leaf_sha256 for leaf in source_leaves)
        )
        for leaf in source_leaves:
            leaves[leaf.leaf_sha256] = leaf
    return MappingProxyType(leaves), MappingProxyType(navigation)


def project_source_route_leaf_navigation_from_validated_inputs(
    *,
    source_map: object,
    preflight: ObligationStructuralPreflight,
) -> Mapping[str, tuple[str, ...]]:
    """Return current exact source-atom identities without issuing evidence."""

    _leaves, navigation = _project_source_route_leaf_material(
        source_map=source_map,
        preflight=preflight,
    )
    return navigation


def project_source_route_leaf_material_from_validated_inputs(
    *,
    source_map: object,
    preflight: ObligationStructuralPreflight,
) -> tuple[
    Mapping[str, ObligationEvidenceLeaf],
    Mapping[str, tuple[str, ...]],
]:
    """Return exact current atom leaves and navigation without issuing evidence."""

    return _project_source_route_leaf_material(
        source_map=source_map,
        preflight=preflight,
    )


def project_source_route_leaves_from_validated_inputs(
    *,
    source_map: object,
    preflight: ObligationStructuralPreflight,
    issuance_authority_sha256: str,
    issuance_assurance_contract_sha256: str,
) -> SourceRouteLeafProjection:
    """Project every exact source route after one complete structural preflight."""

    issuance_authority = _sha256(issuance_authority_sha256, "issuance authority")
    assurance_contract = _sha256(
        issuance_assurance_contract_sha256, "issuance assurance contract"
    )
    leaves, navigation = _project_source_route_leaf_material(
        source_map=source_map,
        preflight=preflight,
    )
    issuances: dict[str, ObligationEvidenceIssuance] = {}
    source = _mapping(source_map, "paper statement map")
    items = _mapping(source.get("items"), "paper statement-map items")
    for source_item_id, leaf_sha256s in sorted(navigation.items()):
        item = _mapping(items[source_item_id], f"source item {source_item_id}")
        for leaf_sha256 in leaf_sha256s:
            leaf = leaves[leaf_sha256]
            issuance = _issuance(
                leaf,
                issuance_authority_sha256=issuance_authority,
                issuance_assurance_contract_sha256=assurance_contract,
                evidence_record=item,
            )
            issuances[issuance.issuance_sha256] = issuance
    graph = build_obligation_graph(leaves.values(), root_leaf_sha256s=sorted(leaves))
    return SourceRouteLeafProjection(
        graph=graph,
        navigation=MappingProxyType(navigation),
        issuances=tuple(issuance for _digest, issuance in sorted(issuances.items())),
        issuance_authority_sha256=issuance_authority,
    )


def _project_prerequisite_ledger(
    *,
    ledger: Mapping[str, Any],
    declaration_field: str,
    declaration_content_sha_field: str,
    semantic_target_protocol_field: str,
    semantic_target_sha_field: str,
    source_items: Mapping[str, Any],
    source_artifact_sha256: str,
    manifests: Mapping[str, Mapping[str, Any]],
    current_semantic_signature_sha256s: Mapping[str, str] | None,
    issuance_authority_sha256: str,
    issuance_assurance_contract_sha256: str,
) -> tuple[
    dict[str, ObligationEvidenceLeaf],
    set[str],
    dict[str, Mapping[str, Any]],
    set[str],
    dict[str, ObligationEvidenceIssuance],
]:
    if ledger.get("schema") != 1:
        raise ObligationEvidenceProjectionError(
            "semantic prerequisite ledger schema is unsupported"
        )
    prompt_version = _nonempty(
        ledger.get("prompt_version"), "semantic prerequisite prompt version"
    )
    target_protocol = _nonempty(
        ledger.get("target_protocol"), "semantic prerequisite target protocol"
    )
    rows = _mapping(ledger.get("items"), "semantic prerequisite rows")
    leaves: dict[str, ObligationEvidenceLeaf] = {}
    roots: set[str] = set()
    navigation: dict[str, Mapping[str, Any]] = {}
    unresolved: set[str] = set()
    issuances: dict[str, ObligationEvidenceIssuance] = {}
    for row_key, raw_row in sorted(rows.items(), key=lambda entry: str(entry[0])):
        row = _mapping(raw_row, "semantic prerequisite row")
        declaration = _nonempty(
            row.get(declaration_field), "semantic prerequisite declaration"
        )
        if str(row_key) != declaration:
            raise ObligationEvidenceProjectionError(
                "semantic prerequisite row key disagrees with its declaration"
            )
        accepted_judgment = str(row.get("judgment") or "").strip()
        if accepted_judgment not in {
            "matches",
            "matches_approved_corrected_target",
        }:
            raise ObligationEvidenceProjectionError(
                f"semantic prerequisite {declaration} is not an accepted match"
            )
        if (
            _nonempty(
                row.get(semantic_target_protocol_field),
                "semantic prerequisite row target protocol",
            )
            != target_protocol
        ):
            raise ObligationEvidenceProjectionError(
                "semantic prerequisite row target protocol is stale"
            )
        source_item_id = _nonempty(
            row.get("source_item"), "semantic prerequisite source item"
        )
        try:
            source_item = _mapping(
                source_items[source_item_id], "semantic prerequisite source item"
            )
        except KeyError as exc:
            raise ObligationEvidenceProjectionError(
                f"semantic prerequisite names missing source item {source_item_id}"
            ) from exc
        if accepted_judgment == "matches_approved_corrected_target":
            corrected_target = _mapping(
                source_item.get("corrected_target"),
                "approved prerequisite corrected target",
            )
            if (
                not corrected_target_screening_binding_is_current(
                    row, corrected_target
                )
                or corrected_target.get("archival_equivalence_claimed") is not False
            ):
                raise ObligationEvidenceProjectionError(
                    f"semantic prerequisite {declaration} has no exact approved correction"
                )
        source_leaves = _source_atom_leaves(
            item=source_item,
            source_artifact_sha256=source_artifact_sha256,
        )
        # These fields authenticate that the accepted legacy review really used
        # exact source and Lean material.  Prompt/validator/reason are issuance
        # provenance and intentionally do not perturb the canonical judgment
        # leaf after validation.
        _nonempty(prompt_version, "semantic prerequisite prompt version")
        _nonempty(target_protocol, "semantic prerequisite target protocol")
        _nonempty(row.get("validator"), "semantic prerequisite validator")
        _nonempty(
            row.get("validator_type"),
            "semantic prerequisite validator type",
        )
        target_sha256 = _sha256(
            row.get(semantic_target_sha_field),
            "semantic prerequisite Lean target",
        )
        _sha256(
            row.get(declaration_content_sha_field),
            "semantic prerequisite declaration content",
        )
        _nonempty(row.get("reason"), "semantic prerequisite reason")
        manifest = manifests.get(declaration)
        if current_semantic_signature_sha256s is not None:
            try:
                current_signature = _sha256(
                    current_semantic_signature_sha256s[declaration],
                    "current prerequisite Lean semantic identity",
                )
            except KeyError as exc:
                raise ObligationEvidenceProjectionError(
                    f"current Lean graph omits semantic identity for {declaration}"
                ) from exc
            lean_leaf = lean_reviewed_semantic_prerequisite_leaf(
                contract_sha256=(
                    LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT.contract_sha256
                ),
                reviewed_semantic_target_sha256=target_sha256,
                elaborated_signature_sha256=current_signature,
            )
            issuance_record: object = {
                "schema": 1,
                "review_record": dict(row),
                "elaborated_signature_sha256": current_signature,
            }
        else:
            lean_leaf = (
                _lean_leaf(
                    manifests,
                    declaration,
                    LeanSemanticTargetKind.SEMANTIC_PREREQUISITE,
                )
                if manifest is not None
                else lean_reviewed_semantic_prerequisite_leaf(
                    contract_sha256=(LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT_SHA256),
                    reviewed_semantic_target_sha256=target_sha256,
                )
            )
            issuance_record = manifest if manifest is not None else row
        judgment = source_lean_judgment_leaf(
            contract_sha256=SOURCE_LEAN_JUDGMENT_CONTRACT_SHA256,
            source_atom_sha256s=[leaf.leaf_sha256 for leaf in source_leaves],
            lean_declaration_sha256=lean_leaf.leaf_sha256,
            verbatim_source_bundle_sha256=_sha256(
                row.get("source_input_bundle_sha256"),
                "semantic prerequisite source bundle",
            ),
            verdict="matches",
        )
        for leaf in (*source_leaves, lean_leaf, judgment):
            leaves[leaf.leaf_sha256] = leaf
        for leaf in source_leaves:
            issued = _issuance(
                leaf,
                issuance_authority_sha256=issuance_authority_sha256,
                issuance_assurance_contract_sha256=(issuance_assurance_contract_sha256),
                evidence_record=source_item,
            )
            issuances[issued.issuance_sha256] = issued
        for leaf, record in (
            (lean_leaf, issuance_record),
            (judgment, row),
        ):
            issued = _issuance(
                leaf,
                issuance_authority_sha256=issuance_authority_sha256,
                issuance_assurance_contract_sha256=(issuance_assurance_contract_sha256),
                evidence_record=record,
            )
            issuances[issued.issuance_sha256] = issued
        roots.add(judgment.leaf_sha256)
        navigation[declaration] = MappingProxyType(
            {
                "source_item_id": source_item_id,
                "declaration": declaration,
                "source_atom_leaf_sha256s": [
                    leaf.leaf_sha256 for leaf in source_leaves
                ],
                "lean_declaration_leaf_sha256": lean_leaf.leaf_sha256,
                "judgment_leaf_sha256": judgment.leaf_sha256,
            }
        )
    return leaves, roots, navigation, unresolved, issuances


def project_semantic_prerequisite_leaves_from_validated_inputs(
    *,
    source_map: object,
    paper_prerequisites: object,
    library_semantic_review: object,
    manifest_authority: object,
    issuance_authority_sha256: str,
    issuance_assurance_contract_sha256: str,
    current_semantic_signature_sha256s: Mapping[str, str] | None = None,
) -> SemanticPrerequisiteLeafProjection:
    """Project paper-local and library prerequisite reviews through one schema."""

    issuance_authority = _sha256(issuance_authority_sha256, "issuance authority")
    assurance_contract = _sha256(
        issuance_assurance_contract_sha256, "issuance assurance contract"
    )
    source = _mapping(source_map, "paper statement map")
    source_artifact = _sha256(source.get("source_artifact_sha256"), "source artifact")
    source_items = _mapping(source.get("items"), "paper statement-map items")
    manifests = (
        {}
        if current_semantic_signature_sha256s is not None
        else _manifest_index(manifest_authority)
    )
    (
        paper_leaves,
        paper_roots,
        paper_navigation,
        paper_unresolved,
        paper_issuances,
    ) = _project_prerequisite_ledger(
        ledger=_mapping(paper_prerequisites, "paper prerequisite ledger"),
        declaration_field="paper_declaration",
        declaration_content_sha_field="paper_declaration_sha256",
        semantic_target_protocol_field="paper_semantic_target_protocol",
        semantic_target_sha_field="paper_semantic_target_sha256",
        source_items=source_items,
        source_artifact_sha256=source_artifact,
        manifests=manifests,
        current_semantic_signature_sha256s=current_semantic_signature_sha256s,
        issuance_authority_sha256=issuance_authority,
        issuance_assurance_contract_sha256=assurance_contract,
    )
    (
        library_leaves,
        library_roots,
        library_navigation,
        library_unresolved,
        library_issuances,
    ) = _project_prerequisite_ledger(
        ledger=_mapping(library_semantic_review, "library semantic-review ledger"),
        declaration_field="library_declaration",
        declaration_content_sha_field="library_definition_sha256",
        semantic_target_protocol_field="library_semantic_target_protocol",
        semantic_target_sha_field="library_semantic_target_sha256",
        source_items=source_items,
        source_artifact_sha256=source_artifact,
        manifests=manifests,
        current_semantic_signature_sha256s=current_semantic_signature_sha256s,
        issuance_authority_sha256=issuance_authority,
        issuance_assurance_contract_sha256=assurance_contract,
    )
    overlap = set(paper_navigation) & set(library_navigation)
    if overlap:
        raise ObligationEvidenceProjectionError(
            "paper and library prerequisite ledgers duplicate declarations: "
            + ", ".join(sorted(overlap))
        )
    leaves = {**paper_leaves, **library_leaves}
    roots = paper_roots | library_roots
    unresolved = paper_unresolved | library_unresolved
    if not roots:
        raise ObligationEvidenceProjectionError(
            "validated inputs contain no projectable semantic prerequisites; "
            "missing declaration leaves: " + ", ".join(sorted(unresolved))
        )
    graph = build_obligation_graph(leaves.values(), root_leaf_sha256s=sorted(roots))
    return SemanticPrerequisiteLeafProjection(
        graph=graph,
        navigation=MappingProxyType({**paper_navigation, **library_navigation}),
        issuances=tuple(
            issuance
            for _digest, issuance in sorted(
                {**paper_issuances, **library_issuances}.items()
            )
        ),
        unresolved_declarations=tuple(sorted(unresolved)),
        issuance_authority_sha256=issuance_authority,
    )


def project_direct_v11_leaves_from_validated_inputs(
    *,
    source_map: object,
    v11_screening: object,
    route_set: EvidenceRouteSet,
    issuance_authority_sha256: str,
    issuance_assurance_contract_sha256: str,
    current_semantic_signature_sha256s: Mapping[str, str] | None = None,
    graph_native_realization_receipts: Mapping[str, Mapping[str, Any]] | None = None,
) -> DirectV11LeafProjection:
    """Project every direct semantic contract in already-validated carriers."""

    issuance_authority = _sha256(issuance_authority_sha256, "issuance authority")
    assurance_contract = _sha256(
        issuance_assurance_contract_sha256, "issuance assurance contract"
    )
    source_artifact, claims = validated_direct_v11_claims(
        source_map=source_map,
        v11_screening=v11_screening,
        route_set=route_set,
    )
    screening = _mapping(v11_screening, "v11 screening")

    leaves: dict[str, ObligationEvidenceLeaf] = {}
    roots: set[str] = set()
    navigation: dict[str, Mapping[str, Any]] = {}
    issuances: dict[str, ObligationEvidenceIssuance] = {}
    for claim in claims:
        source_item_id = claim.source_item_id
        item = claim.item
        contract = claim.contract
        spec_name = claim.spec_name
        endpoint_name = claim.endpoint_name
        relation = claim.relation
        review_name = claim.review_name
        review_kind = claim.review_kind
        row = claim.screening_row

        graph_native_receipt = (
            _validated_graph_native_realization_receipt(
                source_item_id=source_item_id,
                item=item,
                contract=contract,
                receipt=graph_native_realization_receipts.get(source_item_id),
            )
            if graph_native_realization_receipts is not None
            else None
        )
        atom_leaves = (
            _source_atom_leaves(
                item=item,
                source_artifact_sha256=source_artifact,
            )
            if graph_native_receipt is not None
            else _source_leaves(
                item=item,
                source_artifact_sha256=source_artifact,
            )
        )
        current_signature = (
            _sha256(
                current_semantic_signature_sha256s[review_name],
                "current direct Lean semantic identity",
            )
            if current_semantic_signature_sha256s is not None
            and review_name in current_semantic_signature_sha256s
            else None
        )
        if current_semantic_signature_sha256s is not None and current_signature is None:
            raise ObligationEvidenceProjectionError(
                f"current Lean graph omits semantic identity for {review_name}"
            )
        review_leaf = lean_reviewed_semantic_target_leaf(
            contract_sha256=(
                LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT.contract_sha256
                if current_signature is not None
                else LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT_SHA256
            ),
            semantic_target_kind=review_kind,
            reviewed_semantic_target_sha256=_sha256(
                row.get("lean_expanded_statement_sha256"),
                "expanded Lean statement",
            ),
            elaborated_signature_sha256=current_signature,
        )
        spec_leaf = review_leaf
        endpoint_leaf = lean_proof_endpoint_leaf(
            contract_sha256=LEAN_PROOF_ENDPOINT_CONTRACT_SHA256,
            spec_declaration_sha256=spec_leaf.leaf_sha256,
            relation=relation,
        )
        for leaf in (*atom_leaves, review_leaf, spec_leaf, endpoint_leaf):
            leaves[leaf.leaf_sha256] = leaf
        for leaf in atom_leaves:
            issued = _issuance(
                leaf,
                issuance_authority_sha256=issuance_authority,
                issuance_assurance_contract_sha256=assurance_contract,
                evidence_record=item,
            )
            issuances[issued.issuance_sha256] = issued
        for leaf, record in ((review_leaf, row),):
            issued = _issuance(
                leaf,
                issuance_authority_sha256=issuance_authority,
                issuance_assurance_contract_sha256=assurance_contract,
                evidence_record=record,
            )
            issuances[issued.issuance_sha256] = issued
        endpoint_record: object = {
            "schema": 1,
            "source_item_id": str(source_item_id),
            "semantic_contract": dict(contract),
            "source_spec_realization": (
                dict(graph_native_receipt)
                if graph_native_receipt is not None
                else item.get("source_spec_correspondence")
            ),
            "proof_endpoint_evidence": (
                "authenticated_exact_lean_meta_relation_with_separate_"
                "conclusion_provenance_import_closure_and_focused_build"
            ),
        }
        endpoint_issued = _issuance(
            endpoint_leaf,
            issuance_authority_sha256=issuance_authority,
            issuance_assurance_contract_sha256=assurance_contract,
            evidence_record=endpoint_record,
        )
        issuances[endpoint_issued.issuance_sha256] = endpoint_issued

        _validate_direct_judgment_attestation(
            screening,
            row,
            source_item_id=source_item_id,
        )
        judgment = source_lean_judgment_leaf(
            contract_sha256=_validate_direct_judgment_protocol(screening, row),
            source_atom_sha256s=[leaf.leaf_sha256 for leaf in atom_leaves],
            lean_declaration_sha256=review_leaf.leaf_sha256,
            verbatim_source_bundle_sha256=_sha256(
                row.get("source_input_bundle_sha256"), "source input bundle"
            ),
            verdict="matches",
        )
        if graph_native_receipt is not None:
            realization_record = graph_native_receipt
            relation_identity = portable_evidence_sha256(
                {
                    "schema": 1,
                    "authority": "v11_graph_native_realization",
                    "item_identity_sha256": graph_native_receipt[
                        "item_identity_sha256"
                    ],
                    "spec_leaf_sha256": spec_leaf.leaf_sha256,
                    "endpoint_leaf_sha256": endpoint_leaf.leaf_sha256,
                    "relation": relation.value,
                }
            )
        else:
            correspondence = _mapping(
                item.get("source_spec_correspondence"), "source_spec_correspondence"
            )
            current_correspondence = source_spec_correspondence_item_identity_sha256(
                contract, correspondence
            )
            if (
                not current_correspondence
                or _sha256(
                    correspondence.get("item_identity_sha256"),
                    "correspondence item identity",
                )
                != current_correspondence
            ):
                raise ObligationEvidenceProjectionError(
                    "source-spec correspondence identity is stale"
                )
            relation_identity = _portable_correspondence_identity(
                atoms=[
                    _mapping(atom, "source atom")
                    for atom in item["source_claim_atoms"]
                ],
                atom_leaves=atom_leaves,
                correspondence=correspondence,
                spec_leaf_sha256=spec_leaf.leaf_sha256,
                endpoint_leaf_sha256=endpoint_leaf.leaf_sha256,
                relation=relation,
            )
            realization_record = correspondence
        realization = proof_realization_leaf(
            contract_sha256=PROOF_REALIZATION_CONTRACT_SHA256,
            spec_declaration_sha256=spec_leaf.leaf_sha256,
            proof_endpoint_sha256=endpoint_leaf.leaf_sha256,
            relation=relation,
            lean_relation_sha256=relation_identity,
        )
        leaves[judgment.leaf_sha256] = judgment
        leaves[realization.leaf_sha256] = realization
        for leaf, record in ((judgment, row), (realization, realization_record)):
            issued = _issuance(
                leaf,
                issuance_authority_sha256=issuance_authority,
                issuance_assurance_contract_sha256=assurance_contract,
                evidence_record=record,
            )
            issuances[issued.issuance_sha256] = issued
        roots.update((judgment.leaf_sha256, realization.leaf_sha256))
        navigation[str(source_item_id)] = MappingProxyType(
            {
                "source_item_id": str(source_item_id),
                "semantic_review_declaration": review_name,
                "spec_declaration": spec_name,
                "evidence_declaration": endpoint_name,
                "source_atom_leaf_sha256s": [leaf.leaf_sha256 for leaf in atom_leaves],
                "semantic_review_leaf_sha256": review_leaf.leaf_sha256,
                "spec_leaf_sha256": spec_leaf.leaf_sha256,
                "proof_endpoint_leaf_sha256": endpoint_leaf.leaf_sha256,
                "judgment_leaf_sha256": judgment.leaf_sha256,
                "realization_leaf_sha256": realization.leaf_sha256,
            }
        )

    if not roots:
        raise ObligationEvidenceProjectionError(
            "validated inputs contain no direct v11 semantic contracts"
        )
    graph = build_obligation_graph(leaves.values(), root_leaf_sha256s=sorted(roots))
    return DirectV11LeafProjection(
        graph=graph,
        navigation=MappingProxyType(navigation),
        issuances=tuple(issuance for _digest, issuance in sorted(issuances.items())),
        issuance_authority_sha256=issuance_authority,
    )
