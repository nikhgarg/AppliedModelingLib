"""Tests for automatic validation-report projection of settled decisions."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.approved_review_context_report import (
    approved_review_contexts_for_report,
    current_approved_review_context_report_errors,
    replace_approved_review_context_block,
)
from scripts.source_review_input import materialize_approved_review_contexts


class ApprovedReviewContextReportTests(unittest.TestCase):
    def test_historical_map_without_projection_schema_is_not_reopened(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "paper": "Fixture",
                        "items": {
                            "claim": {
                                "model_convention_ids": ["HISTORICAL-CONVENTION"]
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            contexts, error = approved_review_contexts_for_report(folder)
            self.assertEqual(contexts, [])
            self.assertEqual(error, "")

    def test_current_source_context_stays_out_of_the_report(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            source_item = {
                "model_convention_ids": ["FIXTURE-CALENDAR-01"],
                "approved_review_context_schema": 1,
            }
            contexts, error = materialize_approved_review_contexts(
                source_item,
                source_proof_fidelity={
                    "model_conventions": [
                        {
                            "id": "FIXTURE-CALENDAR-01",
                            "source_locator": "source.txt:1",
                            "classification": "source_text_model_convention",
                            "formal_meaning": "Count first reports in calendar time.",
                            "report_summary": (
                                "An incident born before the interval may first "
                                "report inside it."
                            ),
                            "why_needed": "Birth and first-report windows differ.",
                            "checked_scope": "The process lemma and its prerequisites.",
                        }
                    ]
                },
            )
            self.assertEqual(error, "")
            source_item["approved_review_contexts"] = contexts
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "paper": "Fixture",
                        "approved_review_context_schema": 1,
                        "items": {"claim": source_item},
                    }
                ),
                encoding="utf-8",
            )
            report = folder / "FINAL_VALIDATION_REPORT.md"
            report.write_text(
                "# Report\n\n"
                "## 10. Source Clarifications and Exact Readings\n\n"
                "Other clarification.\n\n"
                "## 11. Paper Issues or Caveats\n\nNone.\n",
                encoding="utf-8",
            )
            self.assertEqual(current_approved_review_context_report_errors(folder), ())
            selected, error = approved_review_contexts_for_report(folder)
            self.assertEqual(error, "")
            rendered = replace_approved_review_context_block(
                report.read_text(encoding="utf-8"),
                contexts=selected,
                path=report,
            )
            report.write_text(rendered, encoding="utf-8")
            self.assertEqual(current_approved_review_context_report_errors(folder), ())
            self.assertNotIn("An incident born before the interval", rendered)
            self.assertNotIn("FIXTURE-CALENDAR-01", rendered)

            report.write_text(
                rendered
                + "\n<!-- BEGIN GENERATED SETTLED REVIEW CONTEXT -->\n"
                + "obsolete\n<!-- END GENERATED SETTLED REVIEW CONTEXT -->\n",
                encoding="utf-8",
            )
            self.assertTrue(current_approved_review_context_report_errors(folder))

    def test_older_context_is_not_projected_into_the_report(self) -> None:

        contexts = [
            {
                "kind": "source_model_convention",
                "id": "FIXTURE-CONTEXT",
                "record_sha256": "a" * 64,
                "formal_meaning": (
                    "The source model uses a positive-mass branch convention. "
                    "The stored semantic record also contains implementation details."
                ),
            }
        ]
        rendered = replace_approved_review_context_block(
            "# Report\n\n## 10. Source Clarifications and Exact Readings\n\n"
            "## 11. Paper Issues or Caveats\n\nNone.\n",
            contexts=contexts,
            path=Path("Fixture/FINAL_VALIDATION_REPORT.md"),
        )
        self.assertNotIn("The source model uses a positive-mass branch convention.", rendered)
        self.assertNotIn("implementation details", rendered)

    def test_source_scoped_approved_assumptions_are_not_global_conventions(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            first, error = materialize_approved_review_contexts(
                {
                    "accepted_additional_assumptions": {
                        "approval_reference": "maintainer decision A",
                        "approved_at": "2026-09-03",
                        "conditions": ["first source-scoped condition"],
                    }
                },
                source_proof_fidelity=None,
            )
            self.assertEqual(error, "")
            second, error = materialize_approved_review_contexts(
                {
                    "accepted_additional_assumptions": {
                        "approval_reference": "maintainer decision B",
                        "approved_at": "2026-09-03",
                        "conditions": ["second source-scoped condition"],
                    }
                },
                source_proof_fidelity=None,
            )
            self.assertEqual(error, "")
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "paper": "Fixture",
                        "approved_review_context_schema": 1,
                        "items": {
                            "first": {
                                "accepted_additional_assumptions": {},
                                "approved_review_context_schema": 1,
                                "approved_review_contexts": first,
                            },
                            "second": {
                                "accepted_additional_assumptions": {},
                                "approved_review_context_schema": 1,
                                "approved_review_contexts": second,
                            },
                        },
                    }
                ),
                encoding="utf-8",
            )
            selected, error = approved_review_contexts_for_report(folder)

        self.assertEqual(error, "")
        self.assertEqual(len(selected), 2)
        self.assertEqual(
            {context["conditions"][0] for context in selected},
            {"first source-scoped condition", "second source-scoped condition"},
        )


if __name__ == "__main__":
    unittest.main()
