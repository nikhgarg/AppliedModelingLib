#!/usr/bin/env python3
"""Tests for the pure review-dashboard terminal-formatting boundary."""

from __future__ import annotations

import contextlib
import io
import unittest

from scripts import review_dashboard
from scripts import review_dashboard_cli


class ReviewDashboardCliTests(unittest.TestCase):
    def test_dashboard_exports_the_pure_formatters(self) -> None:
        for name in (
            "print_surface_audit_warnings",
            "print_statement_audit_warnings",
            "print_paper_coverage_audit_warnings",
            "print_assumption_audit_warnings",
        ):
            self.assertIs(
                getattr(review_dashboard, name),
                getattr(review_dashboard_cli, name),
            )

    def test_clear_summaries_are_silent(self) -> None:
        functions = (
            review_dashboard_cli.print_surface_audit_warnings,
            review_dashboard_cli.print_statement_audit_warnings,
            review_dashboard_cli.print_paper_coverage_audit_warnings,
            review_dashboard_cli.print_assumption_audit_warnings,
        )
        for function in functions:
            with self.subTest(function=function.__name__):
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    self.assertFalse(function([], "Fixture"))
                self.assertEqual(output.getvalue(), "")

    def test_warning_output_retains_paper_and_exact_item_sample(self) -> None:
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            needs_attention = review_dashboard_cli.print_statement_audit_warnings(
                [
                    {
                        "paper": "Fixture",
                        "needs_attention": True,
                        "missing_judgment_count": 1,
                        "missing_judgment": ["Fixture.mainSpec"],
                    }
                ],
                "Fixture",
            )

        rendered = output.getvalue()
        self.assertTrue(needs_attention)
        self.assertIn("Statement-translation audit warnings for Fixture", rendered)
        self.assertIn("Fixture: 1 missing statement-judge row(s)", rendered)
        self.assertIn("missing judgment: `Fixture.mainSpec`", rendered)


if __name__ == "__main__":
    unittest.main()
