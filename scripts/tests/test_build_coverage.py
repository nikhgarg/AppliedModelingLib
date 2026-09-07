#!/usr/bin/env python3
"""Focused regression tests for paper-scoped closeout build routing."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    value = str(import_root)
    if value not in sys.path:
        sys.path.insert(0, value)

from scripts import audit_evidence_integrity as integrity  # noqa: E402


class BuildCoverageTests(unittest.TestCase):
    folder = Path("/fixture/papers/FixturePaper")
    status = "formalized"

    def findings(
        self,
        build_target: object,
        *,
        defaults: set[str] | None = None,
        libraries: set[str] | None = None,
    ) -> list[integrity.Finding]:
        return integrity.check_build_coverage(
            self.folder,
            self.status,
            {"build_target": build_target},
            defaults if defaults is not None else set(),
            libraries if libraries is not None else {"FixturePaper"},
        )

    def test_registered_paper_build_does_not_need_default_target(self) -> None:
        findings = self.findings(
            "lake build FixturePaper",
            defaults={"UnrelatedPackageTarget"},
        )

        self.assertEqual(findings, [])

    def test_registered_paper_module_build_is_a_focused_route(self) -> None:
        findings = self.findings(
            "env LEAN_NUM_THREADS=1 lake build +FixturePaper.PaperInterface",
            defaults=set(),
        )

        self.assertEqual(findings, [])

    def test_qualified_paper_module_build_is_a_focused_route(self) -> None:
        findings = self.findings(
            "lake build FixturePaper.PaperInterface",
            defaults=set(),
        )

        self.assertEqual(findings, [])

    def test_direct_interface_elaboration_is_a_focused_route(self) -> None:
        findings = self.findings(
            "lake build AppliedModelingLib.Shared && "
            "lake env lean papers/FixturePaper/PaperInterface.lean",
            defaults=set(),
            libraries={"FixturePaper", "AppliedModelingLib"},
        )

        self.assertEqual(findings, [])

    def test_default_target_cannot_replace_an_explicit_paper_build(self) -> None:
        findings = self.findings(
            "",
            defaults={"FixturePaper"},
        )

        self.assertEqual(len(findings), 1)
        self.assertIn("explicit focused `build_target`", findings[0].message)

    def test_unrelated_build_target_is_not_a_paper_build(self) -> None:
        findings = self.findings(
            "lake build AppliedModelingLib",
            defaults={"FixturePaper"},
            libraries={"FixturePaper", "AppliedModelingLib"},
        )

        self.assertEqual(len(findings), 1)
        self.assertIn("explicit focused `build_target`", findings[0].message)

    def test_paper_requires_its_own_declared_lean_library(self) -> None:
        findings = self.findings(
            "lake build FixturePaper",
            libraries={"AppliedModelingLib"},
        )

        self.assertEqual(len(findings), 1)
        self.assertIn("not declared in `lean_lib`", findings[0].message)


if __name__ == "__main__":
    unittest.main()
