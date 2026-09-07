from __future__ import annotations

import unittest

from scripts import review_dashboard
from scripts import semantic_obligation_review


class SemanticObligationReviewTests(unittest.TestCase):
    def test_dashboard_imports_only_the_authoritative_validators_it_uses(self) -> None:
        for name in (
            "semantic_obligation_ledger_error",
            "signature_manifest_atom_digest",
        ):
            self.assertIs(
                getattr(review_dashboard, name),
                getattr(semantic_obligation_review, name),
            )

    def test_dashboard_imports_only_the_authoritative_schema_constants_it_uses(self) -> None:
        for name in (
            "SOURCE_DEFINITION_SEMANTIC_KINDS",
            "CONDITIONAL_BOUNDARY_RESOLUTION",
        ):
            self.assertIs(
                getattr(review_dashboard, name),
                getattr(semantic_obligation_review, name),
            )

    def test_missing_semantic_obligation_ledger_fails_closed(self) -> None:
        self.assertEqual(
            semantic_obligation_review.semantic_obligation_ledger_error({}),
            "missing source_obligations/lean_obligations lists",
        )

    def test_missing_nested_reviews_fail_closed(self) -> None:
        self.assertIn(
            "invalid schema_version",
            semantic_obligation_review.operational_complexity_review_error(
                {}, "complexity-conclusion"
            ),
        )
        self.assertIn(
            "invalid schema_version",
            semantic_obligation_review.fidelity_risk_review_error(
                {}, {}, {}, "matches", "not_algorithmic"
            ),
        )
        self.assertIn(
            "invalid source_quantification",
            semantic_obligation_review.semantic_scope_review_error(
                {}, {}, {}, {}, "matches"
            ),
        )


if __name__ == "__main__":
    unittest.main()
