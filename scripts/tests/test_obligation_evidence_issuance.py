from __future__ import annotations

import copy
import tempfile
import unittest
from pathlib import Path

from scripts.obligation_evidence_issuance import (
    ObligationEvidenceIssuanceError,
    issue_obligation_evidence_attestation,
    validate_obligation_evidence_issuance,
)
from scripts.obligation_evidence_store import (
    load_obligation_evidence_issuance,
    load_obligation_leaf,
    store_issued_obligation_leaf,
    store_obligation_evidence_issuance,
)
from scripts.obligation_evidence_graph import source_atom_leaf


def sha(character: str) -> str:
    return character * 64


class ObligationEvidenceIssuanceTests(unittest.TestCase):
    def issuance(self):
        return issue_obligation_evidence_attestation(
            leaf_sha256=sha("1"),
            assurance_contract_sha256=sha("2"),
            authority_sha256=sha("3"),
            evidence_record_sha256=sha("4"),
        )

    def test_issuance_is_provenance_not_acceptance(self) -> None:
        issuance = self.issuance()
        self.assertFalse(issuance.projection()["acceptance_credential"])
        corrupt = copy.deepcopy(issuance.projection())
        corrupt["authority_sha256"] = sha("5")
        with self.assertRaisesRegex(
            ObligationEvidenceIssuanceError, "identity is corrupt"
        ):
            validate_obligation_evidence_issuance(corrupt)

    def test_issuance_storage_is_portable_and_content_addressed(self) -> None:
        with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
            roots = (Path(first), Path(second))
            for root in roots:
                (root / "papers" / "Fixture").mkdir(parents=True)
            issuance = self.issuance()
            paths = [
                store_obligation_evidence_issuance(root, "Fixture", issuance)
                for root in roots
            ]
            self.assertEqual(paths[0].read_bytes(), paths[1].read_bytes())
            self.assertEqual(
                load_obligation_evidence_issuance(
                    roots[0],
                    "Fixture",
                    issuance.leaf_sha256,
                    issuance.issuance_sha256,
                ),
                issuance,
            )
            self.assertNotIn(str(roots[0]).encode(), paths[0].read_bytes())
            self.assertFalse(
                (
                    roots[0]
                    / "papers"
                    / "Fixture"
                    / "audit"
                    / "obligation_evidence"
                    / "attestations"
                    / "sha256"
                ).exists()
            )
            with self.assertRaisesRegex(
                ValueError, "obligation issuance is unavailable"
            ):
                load_obligation_evidence_issuance(
                    roots[0],
                    "Fixture",
                    sha("9"),
                    issuance.issuance_sha256,
                )

    def test_leaf_is_durable_before_separate_issuance_publication(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            leaf = source_atom_leaf(
                contract_sha256=sha("1"),
                source_artifact_sha256=sha("2"),
                source_quote_sha256=sha("3"),
                source_component_sha256=sha("4"),
                source_role_contract_sha256=sha("5"),
            )
            issuance = issue_obligation_evidence_attestation(
                leaf_sha256=leaf.leaf_sha256,
                assurance_contract_sha256=sha("6"),
                authority_sha256=sha("7"),
                evidence_record_sha256=sha("8"),
            )
            store_issued_obligation_leaf(root, "Fixture", leaf, issuance)
            self.assertEqual(
                load_obligation_leaf(root, "Fixture", leaf.leaf_sha256), leaf
            )

            wrong = issue_obligation_evidence_attestation(
                leaf_sha256=sha("9"),
                assurance_contract_sha256=sha("6"),
                authority_sha256=sha("7"),
                evidence_record_sha256=sha("8"),
            )
            with self.assertRaisesRegex(
                ValueError, "different obligation leaf"
            ):
                store_issued_obligation_leaf(root, "Fixture", leaf, wrong)
            self.assertEqual(
                load_obligation_leaf(root, "Fixture", leaf.leaf_sha256), leaf
            )


if __name__ == "__main__":
    unittest.main()
