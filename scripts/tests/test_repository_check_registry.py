#!/usr/bin/env python3
"""Tests for the declarative ordinary repository-check executor."""

from __future__ import annotations

import unittest

from scripts import audit_repository
from scripts.repository_check_registry import (
    RegisteredCheck,
    execute_registered_checks,
    ordinary_repository_checks,
    reusable_library_checks,
)


class RepositoryCheckRegistryTests(unittest.TestCase):
    def test_executor_preserves_declared_order_and_runs_each_check_once(self) -> None:
        calls: list[str] = []

        def check(name: str, value: int) -> RegisteredCheck[int]:
            def run() -> list[int]:
                calls.append(name)
                return [value]

            return RegisteredCheck(name, run)

        findings = execute_registered_checks(
            (check("first", 1), check("second", 2), check("third", 3))
        )

        self.assertEqual(findings, [1, 2, 3])
        self.assertEqual(calls, ["first", "second", "third"])

    def test_duplicate_check_name_fails_before_duplicate_execution(self) -> None:
        calls: list[str] = []
        checks = (
            RegisteredCheck("same", lambda: calls.append("first") or []),
            RegisteredCheck("same", lambda: calls.append("second") or []),
        )

        with self.assertRaisesRegex(ValueError, "duplicated"):
            execute_registered_checks(checks)

        self.assertEqual(calls, ["first"])

    def test_non_list_result_fails_closed(self) -> None:
        check = RegisteredCheck("wrong-shape", lambda: ())  # type: ignore[arg-type]

        with self.assertRaisesRegex(TypeError, "did not return a list"):
            execute_registered_checks((check,))

    def test_ordinary_registry_names_the_complete_check_surface(self) -> None:
        checks = ordinary_repository_checks(
            audit_repository,
            include_active=False,
            strict_style=True,
            library_premise_audit=True,
            paper_filter="Fixture",
            require_source_bytes=True,
            deep_paper_prose=False,
        )

        self.assertEqual(
            tuple(check.name for check in checks),
            (
                "sorries",
                "axiom_like_declarations",
                "hidden_variable_premises",
                "guarded_checks",
                "library_source_assumption_standards",
                "library_reusable_provenance_language",
                "library_standard_definition_audits",
                "library_source_hygiene",
                "generic_source_reference_hygiene",
                "paper_contract",
                "final_report_status_alignment",
                "final_report_human_facing_front_matter",
                "dag_and_validation_report_closeout",
                "review_launcher_readiness",
                "dag_status_styles",
                "paper_facing_ledgers",
                "post_paper_audit_interfaces",
                "machine_paper_status",
                "status_label_vocabulary",
                "generated_human_status_labels",
                "readme_status_tables",
                "tracked_artifacts",
                "stale_architecture_terms",
                "root_readme_policy",
                "human_facing_readme",
                "strict_lean_style",
                "library_certificate_boundaries",
            ),
        )

    def test_library_registry_uses_the_file_scoped_checks(self) -> None:
        checks = reusable_library_checks(
            audit_repository,
            files=(),
            strict_style=False,
            library_premise_audit=False,
        )

        self.assertEqual(
            tuple(check.name for check in checks),
            (
                "sorries",
                "axiom_like_declarations",
                "hidden_variable_premises",
                "guarded_checks",
                "library_source_assumption_standards",
                "library_reusable_provenance_language",
                "library_standard_definition_audits",
                "library_source_hygiene",
                "generic_source_reference_hygiene",
            ),
        )


if __name__ == "__main__":
    unittest.main()
