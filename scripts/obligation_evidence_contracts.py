#!/usr/bin/env python3
"""Stable semantic obligation contracts shared by all evidence producers.

Contracts describe *what must have been established*, not which prompt, engine,
script, or report representation established it. A substantively stronger
obligation receives a new contract. Implementation and wording revisions do
not. This registry prevents individual migrations/producers from inventing
version-shaped compatibility identities.
"""

from __future__ import annotations

from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, Iterable, Mapping

try:
    from scripts.portable_evidence_identity import portable_evidence_sha256
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from portable_evidence_identity import portable_evidence_sha256


@dataclass(frozen=True)
class ObligationContract:
    family: str
    requirements: tuple[str, ...]
    contract_sha256: str

    def projection(self) -> Mapping[str, Any]:
        return MappingProxyType(
            {
                "schema": 1,
                "family": self.family,
                "requirements": list(self.requirements),
            }
        )


def _contract(family: str, *requirements: str) -> ObligationContract:
    projection = {
        "schema": 1,
        "family": family,
        "requirements": list(requirements),
    }
    return ObligationContract(
        family=family,
        requirements=tuple(requirements),
        contract_sha256=portable_evidence_sha256(projection),
    )


LEGACY_ARTIFACT_BOUND_SOURCE_ATOM_CONTRACT = _contract(
    "source_atom",
    "byte_pinned_source_artifact",
    "exact_verbatim_quote",
    "path_and_line_independent_component_identity",
    "typed_source_role_and_disposition",
)

SOURCE_ATOM_CONTRACT = _contract(
    "source_atom",
    "exact_verbatim_quote",
    "path_line_and_carrier_independent_component_identity",
    "typed_source_role_and_disposition",
    "complete_byte_pinned_source_corpus_bound_by_paper_preflight",
)

LEAN_DECLARATION_CONTRACT = _contract(
    "lean_declaration",
    "lean_elaborated_signature",
    "lean_elaborated_proposition_graph",
    "lean_produced_transitive_semantic_dependency_identity",
)

LEAN_PROOF_ENDPOINT_CONTRACT = _contract(
    "lean_declaration",
    "lean_meta_established_exact_typed_relation_to_spec",
    "specification_leaf_identity",
    "proof_endpoint_route_authenticated_by_accepted_transaction",
    "proof_closure_and_compilation_carried_by_separate_graph_leaves",
)

LEGACY_CONTENT_BOUND_LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT = _contract(
    "lean_declaration",
    "exact_expanded_lean_semantic_target",
    "exact_reviewed_declaration_content",
    "direct_raw_source_comparison_without_name_or_paraphrase_substitution",
    "lean_elaboration_and_compilation_carried_by_separate_closeout_controls",
)

LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT = _contract(
    "lean_declaration",
    "exact_expanded_lean_semantic_target",
    "direct_raw_source_comparison_without_name_or_paraphrase_substitution",
    "lean_elaboration_and_compilation_carried_by_separate_closeout_controls",
    "source_syntax_and_location_retained_only_as_issuance_provenance",
)

LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT = _contract(
    "lean_declaration",
    "exact_expanded_lean_semantic_target_review_record",
    "lean_owned_canonical_elaborated_semantic_identity",
    "direct_raw_source_comparison_without_name_or_paraphrase_substitution",
    "renderer_bytes_are_review_provenance_not_semantic_currentness",
)


# A Lean-declaration leaf's exact payload shape determines the obligation it
# claims to satisfy.  Keep this mapping beside the contracts themselves so a
# consumer cannot reclassify a stronger, identity-bound review leaf merely by
# checking one field before another.
LEAN_DECLARATION_MANIFEST_PAYLOAD_FIELDS = frozenset(
    {
        "semantic_target_kind",
        "elaborated_signature_sha256",
        "elaborated_proposition_graph_sha256",
        "semantic_dependency_sha256",
    }
)
LEAN_PROOF_ENDPOINT_PAYLOAD_FIELDS = frozenset(
    {
        "semantic_target_kind",
        "spec_declaration_sha256",
        "relation",
    }
)
LEAN_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS = frozenset(
    {
        "semantic_target_kind",
        "reviewed_semantic_target_sha256",
    }
)
LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS = frozenset(
    {
        *LEAN_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS,
        "elaborated_signature_sha256",
    }
)
LEGACY_CONTENT_BOUND_LEAN_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS = frozenset(
    {
        *LEAN_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS,
        "declaration_content_sha256",
    }
)

LEAN_DECLARATION_CONTRACT_BY_PAYLOAD_FIELDS: Mapping[
    frozenset[str], ObligationContract
] = MappingProxyType(
    {
        LEAN_DECLARATION_MANIFEST_PAYLOAD_FIELDS: LEAN_DECLARATION_CONTRACT,
        LEAN_PROOF_ENDPOINT_PAYLOAD_FIELDS: LEAN_PROOF_ENDPOINT_CONTRACT,
        LEAN_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS: (
            LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT
        ),
        LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS: (
            LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT
        ),
        LEGACY_CONTENT_BOUND_LEAN_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS: (
            LEGACY_CONTENT_BOUND_LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT
        ),
    }
)


def lean_declaration_contract_for_payload_fields(
    payload_fields: Iterable[object],
) -> ObligationContract | None:
    """Return the one contract defined by an exact Lean payload shape."""

    try:
        key = frozenset(str(field) for field in payload_fields)
    except TypeError:
        return None
    return LEAN_DECLARATION_CONTRACT_BY_PAYLOAD_FIELDS.get(key)

RAW_SOURCE_LEAN_MATCH_CONTRACT = _contract(
    "source_lean_judgment",
    "exact_verbatim_source_atoms",
    "exact_verbatim_context_bundle",
    "complete_lean_semantic_declaration_leaf",
    "direct_source_to_lean_comparison_without_paraphrase_substitution",
    "typed_verdict",
)

PROOF_REALIZATION_CONTRACT = _contract(
    "proof_realization",
    "lean_checked_spec_declaration",
    "lean_checked_proof_endpoint",
    "lean_established_typed_relation",
)

FOCUSED_BUILD_CONTRACT = _contract(
    "build",
    "exact_selected_targets",
    "portable_build_command",
    "lean_toolchain_contract",
    "lean_authored_path_independent_reached_closure",
    "passed_result",
)

PAPER_CLOSURE_CONTRACT = _contract(
    "paper_closure",
    "complete_preflight_owned_paper_index",
    "complete_semantic_obligation_graph",
    "registered_terminal_verifier",
    "current_source_lean_and_build_controls",
)

STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT = _contract(
    "paper_closure",
    "complete_preflight_owned_paper_index",
    "complete_semantic_obligation_graph",
    "nominal_authenticated_strict_closeout_authority",
    "exact_final_holistic_audit_surface",
    "recomputable_source_inventory_correction_defect_and_fidelity_assurance",
    "current_source_review_lean_and_build_controls",
)


TERMINAL_SOURCE_ASSURANCE_V2_CONTRACT = _contract(
    "terminal_source_assurance",
    "complete_source_inventory_correction_defect_and_fidelity_controls",
    "formalization_status_and_assumption_policy_controls",
    "reader_prose_and_repository_visibility_excluded",
    "same_frozen_final_audit_identity_bound_by_terminal_closure",
)


ALL_OBLIGATION_CONTRACTS: Mapping[str, ObligationContract] = MappingProxyType(
    {
        contract.family: contract
        for contract in (
            SOURCE_ATOM_CONTRACT,
            LEAN_DECLARATION_CONTRACT,
            RAW_SOURCE_LEAN_MATCH_CONTRACT,
            PROOF_REALIZATION_CONTRACT,
            FOCUSED_BUILD_CONTRACT,
        )
    }
)

# Historical graph credentials remain directly verifiable under the exact
# contract that issued them.  New producers use ``ALL_OBLIGATION_CONTRACTS``;
# this registry is only the set of canonical contracts the current verifier
# can interpret, not an engine-version or paper-specific compatibility table.
REGISTERED_OBLIGATION_CONTRACT_SHA256S: Mapping[str, frozenset[str]] = (
    MappingProxyType(
        {
            **{
                family: frozenset({contract.contract_sha256})
                for family, contract in ALL_OBLIGATION_CONTRACTS.items()
            },
            "source_atom": frozenset(
                {
                    LEGACY_ARTIFACT_BOUND_SOURCE_ATOM_CONTRACT.contract_sha256,
                    SOURCE_ATOM_CONTRACT.contract_sha256,
                }
            ),
            "lean_declaration": frozenset(
                {
                    LEAN_DECLARATION_CONTRACT.contract_sha256,
                    LEAN_PROOF_ENDPOINT_CONTRACT.contract_sha256,
                    LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT.contract_sha256,
                    LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT.contract_sha256,
                    LEGACY_CONTENT_BOUND_LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT.contract_sha256,
                }
            ),
            "paper_closure": frozenset(
                {
                    PAPER_CLOSURE_CONTRACT.contract_sha256,
                    STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT.contract_sha256,
                }
            ),
        }
    )
)
