from __future__ import annotations

import unittest

from scripts.statement_sidecar_audit import statement_sidecar_summary_issues


class StatementSidecarAuditTests(unittest.TestCase):
    def issues(
        self,
        *,
        status: str = "formalized",
        surface: dict[str, object] | None = None,
        statements: dict[str, object] | None = None,
        coverage: dict[str, object] | None = None,
        assumptions: dict[str, object] | None = None,
        lanes: dict[str, bool] | None = None,
        v11_required: bool = False,
        screening_errors: tuple[str, ...] = (),
        coverage_errors: tuple[str, ...] = (),
    ):
        return statement_sidecar_summary_issues(
            "FixturePaper",
            status,
            surface={"has_completed_audit": True} if surface is None else surface,
            statements={} if statements is None else statements,
            paper_coverage={} if coverage is None else coverage,
            assumptions={} if assumptions is None else assumptions,
            bridge_lanes=(
                {"review_surface": False, "statement": False, "coverage": False}
                if lanes is None
                else lanes
            ),
            v11_required=v11_required,
            v11_screening_errors=screening_errors,
            v11_coverage_errors=coverage_errors,
        )

    def test_clean_summaries_emit_no_issues(self) -> None:
        self.assertEqual(self.issues(), ())

    def test_completed_status_requires_explicit_surface_audit(self) -> None:
        issues = self.issues(surface={})
        self.assertEqual(len(issues), 1)
        self.assertEqual(issues[0].artifact, "audit/review_surface_llm.json")
        self.assertIn("missing explicit review-surface LLM pass", issues[0].message)

    def test_each_summary_lane_keeps_its_artifact_and_reason(self) -> None:
        issues = self.issues(
            surface={"has_completed_audit": True},
            statements={"needs_attention": True, "mismatch_count": 2},
            coverage={
                "needs_attention": True,
                "missing_inventory": True,
                "partial_count": 3,
                "stale_inventory": True,
                "source_to_lean_needs_attention": True,
                "row_statement_match_mismatch_count": 4,
            },
            assumptions={"needs_attention": True, "uncertain_count": 5},
        )
        self.assertEqual(
            [issue.artifact for issue in issues],
            [
                "audit/paper_coverage_llm.json",
                "audit/paper_coverage_llm.json",
                "audit/statement_match_llm.json",
                "audit/assumption_match_llm.json",
            ],
        )
        messages = "\n".join(issue.message for issue in issues)
        self.assertIn("missing required source-statement inventory", messages)
        self.assertIn("3 partially covered source statement(s)", messages)
        self.assertIn("stale source-inventory digest", messages)
        self.assertIn(
            "4 source-to-row link with mismatched row-local statement judgment(s)",
            messages,
        )
        self.assertIn("2 statement mismatch(s)", messages)
        self.assertIn("5 uncertain assumption-provenance judgment(s)", messages)

    def test_bridge_lanes_suppress_only_their_legacy_summaries(self) -> None:
        issues = self.issues(
            surface={"needs_attention": True},
            statements={"needs_attention": True},
            coverage={
                "needs_attention": True,
                "source_to_lean_needs_attention": True,
                "row_statement_match_missing_count": 1,
            },
            assumptions={"needs_attention": True, "missing_judgment_count": 1},
            lanes={"review_surface": True, "statement": True, "coverage": True},
        )
        self.assertEqual(len(issues), 1)
        self.assertEqual(issues[0].artifact, "audit/assumption_match_llm.json")

    def test_v11_errors_are_bounded_and_keep_distinct_artifacts(self) -> None:
        issues = self.issues(
            v11_required=True,
            screening_errors=tuple(f"screen-{index}" for index in range(10)),
            coverage_errors=("coverage-one",),
        )
        self.assertEqual(len(issues), 2)
        self.assertEqual(
            [issue.artifact for issue in issues],
            [
                "audit/v11_raw_source_spec_screening.json",
                "audit/paper_statement_map.json",
            ],
        )
        self.assertIn("screen-7; ...", issues[0].message)
        self.assertNotIn("screen-8", issues[0].message)
        self.assertIn("coverage-one", issues[1].message)


if __name__ == "__main__":
    unittest.main()
