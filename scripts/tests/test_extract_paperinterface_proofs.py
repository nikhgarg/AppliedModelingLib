"""Tests for the Lean-range-authorized PaperInterface proof extraction."""

from __future__ import annotations

import unittest

from scripts.extract_paperinterface_proofs import ProofBlock, relocate_proof_blocks


class PaperInterfaceProofExtractionTests(unittest.TestCase):
    def test_relocation_uses_exact_lean_ranges_and_preserves_order(self) -> None:
        interface = """namespace Fixture\n\ndef alphaSpec : Prop := True\ntheorem alpha : alphaSpec := by trivial\n\ndef betaSpec : Prop := True\ntheorem beta : betaSpec := by trivial\n\nend Fixture\n"""
        proof = """namespace Fixture\nend Fixture\n\n/-! ## Current source-ledger proof endpoints -/\n\nnamespace Fixture.ProofInterface\nend Fixture.ProofInterface\n"""

        rewritten_interface, rewritten_proof = relocate_proof_blocks(
            interface,
            proof,
            paper="Fixture",
            blocks=(
                ProofBlock("Fixture.PaperInterface.alpha", 4, 4),
                ProofBlock("Fixture.PaperInterface.beta", 7, 7),
            ),
        )

        self.assertNotIn("theorem alpha", rewritten_interface)
        self.assertNotIn("theorem beta", rewritten_interface)
        self.assertIn("def alphaSpec", rewritten_interface)
        self.assertIn("def betaSpec", rewritten_interface)
        self.assertLess(
            rewritten_proof.index("theorem alpha"),
            rewritten_proof.index("theorem beta"),
        )
        self.assertLess(
            rewritten_proof.index("theorem beta"),
            rewritten_proof.index("Current source-ledger proof endpoints"),
        )
        self.assertIn("end\n\nend PaperInterface\n\nend Fixture", rewritten_proof)

    def test_relocation_accepts_plain_paper_namespace_and_installs_marker(self) -> None:
        interface = """namespace Fixture\n\n\ndef alphaSpec : Prop := True\ntheorem alpha : alphaSpec := by trivial\n\nend Fixture\n"""
        proof = """namespace Fixture\nend Fixture\n"""

        rewritten_interface, rewritten_proof = relocate_proof_blocks(
            interface,
            proof,
            paper="Fixture",
            blocks=(ProofBlock("Fixture.alpha", 5, 5),),
        )

        self.assertNotIn("theorem alpha", rewritten_interface)
        self.assertIn("def alphaSpec", rewritten_interface)
        self.assertIn("namespace Fixture\n\nnoncomputable section", rewritten_proof)
        self.assertIn("theorem alpha", rewritten_proof)
        self.assertIn("end Fixture", rewritten_proof)
        self.assertEqual(
            rewritten_proof.count("Current source-ledger proof endpoints"), 1
        )


if __name__ == "__main__":
    unittest.main()
