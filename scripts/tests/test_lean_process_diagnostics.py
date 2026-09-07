#!/usr/bin/env python3
"""Tests for fail-closed Lean process diagnostics."""

from __future__ import annotations

import unittest

from scripts.lean_process_diagnostics import (
    bounded_lean_diagnostic_excerpt,
    lean_diagnostic_failure_reason,
)


class LeanProcessDiagnosticsTests(unittest.TestCase):
    def test_clean_output_passes(self) -> None:
        self.assertEqual(
            lean_diagnostic_failure_reason("Build completed successfully.\n", ""),
            "",
        )

    def test_zero_exit_panic_text_fails(self) -> None:
        self.assertEqual(
            lean_diagnostic_failure_reason(
                "",
                "PANIC at Lean.Expr.appArg! Lean.Expr:926:15: application expected\n",
            ),
            "Lean PANIC output",
        )

    def test_internal_error_text_fails(self) -> None:
        self.assertEqual(
            lean_diagnostic_failure_reason("Lean internal error while simplifying", ""),
            "Lean internal-error output",
        )

    def test_pathologically_large_output_fails(self) -> None:
        reason = lean_diagnostic_failure_reason(
            "x" * 101,
            "",
            max_output_bytes=100,
        )
        self.assertIn("pathologically large Lean diagnostic output", reason)

    def test_excerpt_prioritizes_fatal_diagnostic_over_warning_prelude(self) -> None:
        excerpt = bounded_lean_diagnostic_excerpt(
            "warning: harmless linter\nPANIC at Lean.Expr.appArg!\nbacktrace:\nframe",
            "",
        )
        self.assertTrue(excerpt.startswith("PANIC at Lean.Expr.appArg!"))
        self.assertNotIn("harmless linter", excerpt)

    def test_excerpt_prioritizes_target_failure_over_generic_lake_error(self) -> None:
        excerpt = bounded_lean_diagnostic_excerpt(
            (
                "warning: replayed linter warning\n"
                "✖ [42/43] Building Paper.Target\n"
                "Paper/Target.lean:12:3: error: type mismatch\n"
                "details\n"
            ),
            "error: build failed\n",
            max_lines=3,
            max_chars=200,
        )
        self.assertTrue(excerpt.startswith("Paper/Target.lean:12:3: error"))
        self.assertIn("type mismatch", excerpt)
        self.assertNotIn("build failed", excerpt)


if __name__ == "__main__":
    unittest.main()
