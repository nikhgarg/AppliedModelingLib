#!/usr/bin/env python3
"""Tests for the shared cheap review-surface structural preflight."""

from __future__ import annotations

import unittest

from scripts.review_surface_structure import validate_review_surface_structure


class ReviewSurfaceStructureTests(unittest.TestCase):
    def test_valid_surface_resolves_paper_and_assumption_declarations(self) -> None:
        result = validate_review_surface_structure(
            {
                "intake_freeze_required": True,
                "review_surface": {
                    "include_names": ["mainSpec"],
                    "proof_module": "Fixture.ProofInterface",
                    "proposition_spec_proofs": {"mainSpec": "main"},
                    "assumption_names": ["Fixture.paper_assumption_boundary"],
                    "proof_boundary_names": ["Fixture.paper_assumption_boundary"],
                    "auxiliary_names": ["helper"],
                    "quarantined_auxiliary_names": ["helper"],
                }
            },
            interface_text=(
                "def mainSpec : Prop := True\n"
                "lemma helper : True := by trivial\n"
            ),
            assumption_text=(
                "axiom paper_assumption_boundary : True\n"
            ),
            proof_text="theorem main : mainSpec := by trivial\n",
            proof_source_module="Fixture.ProofInterface",
        )
        self.assertTrue(result.current, result.errors)
        self.assertEqual(result.include_names, ("mainSpec",))

    def test_all_stale_membership_errors_are_reported_together(self) -> None:
        result = validate_review_surface_structure(
            {
                "intake_freeze_required": True,
                "review_surface": {
                    "include_names": ["missingMain"],
                    "assumption_names": ["missingAssumption"],
                    "proof_boundary_names": ["notAnAssumption"],
                    "auxiliary_names": ["missingAuxiliary"],
                    "quarantined_auxiliary_names": ["notAuxiliary"],
                }
            },
            interface_text="def actualSpec : Prop := True\n",
        )
        rendered = "\n".join(result.errors)
        self.assertIn("proof_boundary_names must also be assumption_names", rendered)
        self.assertIn("quarantined_auxiliary_names must also be auxiliary_names", rendered)
        self.assertIn("missingMain", rendered)
        self.assertIn("missingAssumption", rendered)
        self.assertIn("missingAuxiliary", rendered)

    def test_duplicate_configuration_is_rejected(self) -> None:
        result = validate_review_surface_structure(
            {
                "review_surface": {
                    "include_names": ["mainSpec", "mainSpec"],
                }
            },
            interface_text="def mainSpec : Prop := True\n",
        )
        self.assertTrue(
            any("duplicate names" in error for error in result.errors), result.errors
        )

    def test_source_condition_items_are_distinct_from_assumption_declarations(self) -> None:
        result = validate_review_surface_structure(
            {
                "review_surface": {
                    "include_names": ["mainSpec"],
                    "source_condition_items": ["conditions_c123"],
                }
            },
            interface_text="def mainSpec : Prop := True\n",
        )
        self.assertTrue(result.current, result.errors)
        self.assertEqual(result.source_condition_items, frozenset({"conditions_c123"}))
        self.assertEqual(result.assumption_names, frozenset())

    def test_duplicate_source_condition_items_are_rejected(self) -> None:
        result = validate_review_surface_structure(
            {
                "review_surface": {
                    "include_names": ["mainSpec"],
                    "source_condition_items": ["conditions_c123", "conditions_c123"],
                }
            },
            interface_text="def mainSpec : Prop := True\n",
        )
        self.assertTrue(
            any("source_condition_items contains duplicate names" in error for error in result.errors),
            result.errors,
        )

    def test_proof_route_mismatch_is_rejected_before_lean(self) -> None:
        result = validate_review_surface_structure(
            {
                "intake_freeze_required": True,
                "review_surface": {
                    "include_names": ["mainSpec"],
                    "proof_module": "Fixture",
                    "proposition_spec_proofs": {"mainSpec": "main"},
                }
            },
            interface_text="def mainSpec : Prop := True\n",
            proof_text="def main : Prop := True\n",
            proof_source_module="Fixture.ProofInterface",
        )
        rendered = "\n".join(result.errors)
        self.assertIn("proof_module does not match", rendered)
        self.assertIn("endpoint must be a theorem or lemma", rendered)

    def test_colocated_legacy_proof_route_remains_valid(self) -> None:
        source = (
            "def mainSpec : Prop := True\n"
            "theorem main : mainSpec := by trivial\n"
        )
        result = validate_review_surface_structure(
            {
                "review_surface": {
                    "include_names": ["mainSpec"],
                    "proposition_spec_proofs": {"mainSpec": "main"},
                }
            },
            interface_text=source,
            proof_text=source,
            proof_source_module="Fixture.PaperInterface",
        )
        self.assertTrue(result.current, result.errors)


if __name__ == "__main__":
    unittest.main()
