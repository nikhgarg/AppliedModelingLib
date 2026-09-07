from __future__ import annotations

import unittest

from scripts.obligation_evidence_contracts import (
    ALL_OBLIGATION_CONTRACTS,
    LEAN_PROOF_ENDPOINT_CONTRACT,
    LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT,
    LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS,
    LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT,
    LEGACY_ARTIFACT_BOUND_SOURCE_ATOM_CONTRACT,
    LEGACY_CONTENT_BOUND_LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT,
    REGISTERED_OBLIGATION_CONTRACT_SHA256S,
    TERMINAL_SOURCE_ASSURANCE_V2_CONTRACT,
    lean_declaration_contract_for_payload_fields,
)
from scripts.portable_evidence_identity import portable_evidence_sha256


class ObligationEvidenceContractTests(unittest.TestCase):
    def test_terminal_source_assurance_v2_contract_separates_status_controls(self) -> None:
        contract = TERMINAL_SOURCE_ASSURANCE_V2_CONTRACT
        self.assertEqual(contract.family, "terminal_source_assurance")
        self.assertIn(
            "formalization_status_and_assumption_policy_controls",
            contract.requirements,
        )
        self.assertIn(
            "reader_prose_and_repository_visibility_excluded",
            contract.requirements,
        )
        self.assertEqual(
            portable_evidence_sha256(dict(contract.projection())),
            contract.contract_sha256,
        )

    def test_registry_has_one_stable_contract_per_semantic_family(self) -> None:
        self.assertEqual(
            set(ALL_OBLIGATION_CONTRACTS),
            {
                "source_atom",
                "lean_declaration",
                "source_lean_judgment",
                "proof_realization",
                "build",
            },
        )
        for family, contract in ALL_OBLIGATION_CONTRACTS.items():
            projection = dict(contract.projection())
            self.assertEqual(projection["family"], family)
            self.assertEqual(
                portable_evidence_sha256(projection), contract.contract_sha256
            )
            serialized = repr(projection).lower()
            for forbidden in (
                "prompt_version",
                "engine_version",
                "validator",
                "reviewer",
                "resolved_path",
                "line_start",
                "commit_sha",
            ):
                self.assertNotIn(forbidden, serialized)

    def test_historical_source_atom_contract_is_explicit_not_a_version_bridge(self) -> None:
        registered = REGISTERED_OBLIGATION_CONTRACT_SHA256S["source_atom"]
        self.assertEqual(
            registered,
            frozenset(
                {
                    ALL_OBLIGATION_CONTRACTS["source_atom"].contract_sha256,
                    LEGACY_ARTIFACT_BOUND_SOURCE_ATOM_CONTRACT.contract_sha256,
                }
            ),
        )
        self.assertNotEqual(
            ALL_OBLIGATION_CONTRACTS["source_atom"].contract_sha256,
            LEGACY_ARTIFACT_BOUND_SOURCE_ATOM_CONTRACT.contract_sha256,
        )

    def test_reviewed_target_contract_separates_meaning_from_syntax(self) -> None:
        current = LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT
        historical = LEGACY_CONTENT_BOUND_LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT
        self.assertIn("exact_expanded_lean_semantic_target", current.requirements)
        self.assertNotIn("exact_reviewed_declaration_content", current.requirements)
        self.assertIn("exact_reviewed_declaration_content", historical.requirements)
        self.assertEqual(
            REGISTERED_OBLIGATION_CONTRACT_SHA256S["lean_declaration"],
            frozenset(
                {
                    ALL_OBLIGATION_CONTRACTS["lean_declaration"].contract_sha256,
                    LEAN_PROOF_ENDPOINT_CONTRACT.contract_sha256,
                    LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT.contract_sha256,
                    LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT.contract_sha256,
                    LEGACY_CONTENT_BOUND_LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT.contract_sha256,
                }
            ),
        )

    def test_identity_bound_review_payload_selects_its_stronger_contract(self) -> None:
        self.assertEqual(
            lean_declaration_contract_for_payload_fields(
                LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS
            ),
            LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT,
        )
        self.assertIsNone(
            lean_declaration_contract_for_payload_fields(
                {
                    *LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS,
                    "unexpected_field",
                }
            )
        )


if __name__ == "__main__":
    unittest.main()
