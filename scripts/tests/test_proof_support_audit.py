#!/usr/bin/env python3
"""Focused regression tests for the source-proof-support coverage lane."""

from __future__ import annotations

import sys
import json
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    import_root_text = str(import_root)
    if import_root_text not in sys.path:
        sys.path.insert(0, import_root_text)

from scripts import review_dashboard  # noqa: E402


class ProofSupportAuditTests(unittest.TestCase):
    def test_explicit_proof_support_requires_transparent_proof_routed_spec(self) -> None:
        """Support stays audited without becoming a duplicate paper claim row."""

        source_item = {
            "source_kind": "lemma",
            "source_status": "support_only",
            "inventory_role": "proof_support",
            "support_lean_declarations": ["Demo.PaperInterface.mainResultSpec"],
        }
        route = review_dashboard.ReviewItem(
            name="mainResultSpec",
            kind="def",
            lean_statement="def mainResultSpec : Prop := True",
            paper_statement="The main result has the stated conclusion.",
            agent_statement="The main result has the stated conclusion.",
            is_proposition_spec=True,
            proposition_spec_role="proof_routed",
            proposition_spec_proof="mainResultSpec_proof",
        )
        self.assertTrue(
            review_dashboard._source_inventory_item_is_explicit_proof_support(
                source_item
            )
        )
        self.assertFalse(
            review_dashboard._source_inventory_item_requires_review_row(
                "intermediate_lemma", source_item
            )
        )
        self.assertEqual(
            review_dashboard._proof_support_coverage_error(
                source_item,
                {"support_declarations": ["mainResultSpec"]},
                {"mainResultSpec": route},
            ),
            "",
        )

        route.proposition_spec_role = "translation_only"
        self.assertIn(
            "proof-routed source result",
            review_dashboard._proof_support_coverage_error(
                source_item,
                {"support_declarations": ["mainResultSpec"]},
                {"mainResultSpec": route},
            ),
        )
        self.assertIn(
            "exactly match",
            review_dashboard._proof_support_coverage_error(
                source_item,
                {"support_declarations": ["anotherSpec"]},
                {"mainResultSpec": route},
            ),
        )

    def test_generic_support_only_item_remains_a_review_obligation(self) -> None:
        """A bare status label is never enough to suppress a source claim."""

        item = {
            "title": "Proposition: a visible source assertion",
            "source_kind": "proposition",
            "source_status": "support_only",
            "support_lean_declarations": ["someHelper"],
        }
        self.assertFalse(
            review_dashboard._source_inventory_item_is_explicit_proof_support(item)
        )
        self.assertTrue(
            review_dashboard._source_inventory_item_requires_review_row(
                "source_proposition", item
            )
        )

    def test_inventory_keeps_the_new_role_marker_absent_for_ordinary_items(self) -> None:
        """Adding the proof-support lane must not stale unrelated source pins."""

        with tempfile.TemporaryDirectory() as temp_dir:
            paper = Path(temp_dir) / "Paper"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "ordinary": {
                                "statement": "A source definition.",
                                "source_kind": "definition",
                            },
                            "support": {
                                "statement": "A source lemma used in a proof.",
                                "source_kind": "lemma",
                                "inventory_role": "proof_support",
                            },
                        }
                    }
                ),
                encoding="utf-8",
            )
            inventory = review_dashboard.paper_statement_inventory(paper)
            self.assertNotIn("inventory_role", inventory["ordinary"])
            self.assertEqual(inventory["support"]["inventory_role"], "proof_support")


if __name__ == "__main__":
    unittest.main()
