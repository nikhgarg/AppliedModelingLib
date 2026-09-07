#!/usr/bin/env python3
"""Tests for automatic settled-review-context projection at closeout."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.current_closeout.approved_contexts import (
    apply_approved_review_context_projection,
    current_approved_review_context_projection,
    expected_approved_review_context_projection,
)
from scripts.source_review_input import validated_approved_review_contexts


class ApprovedReviewContextSyncTests(unittest.TestCase):
    def test_configured_authority_is_materialized_without_touching_other_fields(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (audit / "v11_source_map_preparation_config.json").write_text(
                json.dumps(
                    {
                        "add_source_items": {
                            "claim": {"model_convention_ids": ["decision-1"]}
                        }
                    }
                ),
                encoding="utf-8",
            )
            (audit / "source_proof_fidelity.json").write_text(
                json.dumps(
                    {
                        "model_conventions": [
                            {
                                "id": "decision-1",
                                "source_locator": "source.txt:1-2",
                                "classification": "user_approved_source_model_convention",
                                "formal_meaning": "Use the approved calendar-time reading.",
                                "why_needed": "It fixes the observation-window convention.",
                                "checked_scope": "The claim and its source-model premise.",
                                "report_summary": "Calendar-time first reports are used.",
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )
            source_map = {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "statement": "Claim text",
                        "semantic_contract": {"spec_declaration": "Fixture.claimSpec"},
                    }
                },
            }

            projection, error = expected_approved_review_context_projection(
                folder,
                source_map,
            )

            self.assertEqual(error, "")
            assert projection is not None
            updated = apply_approved_review_context_projection(source_map, projection)
            self.assertEqual(updated["items"]["claim"]["statement"], "Claim text")
            self.assertEqual(
                updated["items"]["claim"]["semantic_contract"],
                {"spec_declaration": "Fixture.claimSpec"},
            )
            self.assertEqual(
                updated["items"]["claim"]["model_convention_ids"],
                ["decision-1"],
            )
            contexts, validation_error = validated_approved_review_contexts(
                updated["items"]["claim"]
            )
            self.assertEqual(validation_error, "")
            self.assertEqual([context["id"] for context in contexts], ["decision-1"])
            self.assertEqual(
                current_approved_review_context_projection(updated),
                projection,
            )

    def test_unknown_authority_fails_before_reviewer_queue_generation(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (audit / "source_proof_fidelity.json").write_text(
                '{"model_conventions": []}\n', encoding="utf-8"
            )
            source_map = {
                "paper": "Fixture",
                "items": {
                    "claim": {"model_convention_ids": ["missing-decision"]}
                },
            }

            projection, error = expected_approved_review_context_projection(
                folder,
                source_map,
            )

            self.assertIsNone(projection)
            self.assertIn("unknown convention `missing-decision`", error)


if __name__ == "__main__":
    unittest.main()
