#!/usr/bin/env python3
"""Regression tests for the package-owned current closeout command."""

from __future__ import annotations

import unittest
from unittest import mock

from scripts.current_closeout import strict_runner


class CurrentStrictRunnerTests(unittest.TestCase):
    def test_stateful_command_rejects_missing_plan_identity_before_engine(self) -> None:
        with mock.patch.object(
            strict_runner, "runtime_engine_registration_error"
        ) as engine:
            self.assertEqual(strict_runner.main(["--paper", "Fixture"]), 6)
        engine.assert_not_called()

    def test_only_in_process_publication_can_return_success(self) -> None:
        def execute(*_args, **kwargs):
            kwargs["closeout_trace"]["current_closeout_published"] = True
            kwargs["closeout_trace"]["current_closeout_finalization"] = {
                "canonical_receipt": "papers/Fixture/FINAL_CLOSURE_RECEIPT.md"
            }
            return []

        with (
            mock.patch.object(
                strict_runner, "runtime_engine_registration_error", return_value=""
            ),
            mock.patch.object(strict_runner, "execute_paper_closeout", side_effect=execute),
        ):
            self.assertEqual(
                strict_runner.main(
                    ["--paper", "Fixture", "--no-closeout-state"]
                ),
                0,
            )

    def test_zero_findings_without_publication_fails_closed(self) -> None:
        with (
            mock.patch.object(
                strict_runner, "runtime_engine_registration_error", return_value=""
            ),
            mock.patch.object(strict_runner, "execute_paper_closeout", return_value=[]),
        ):
            self.assertEqual(
                strict_runner.main(
                    ["--paper", "Fixture", "--no-closeout-state"]
                ),
                1,
            )


if __name__ == "__main__":
    unittest.main()
