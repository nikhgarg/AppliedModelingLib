#!/usr/bin/env python3
"""Focused tests for public release artifact path hygiene."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.public_release_artifact_policy import (  # noqa: E402
    public_release_artifact_issues,
)


class PublicReleaseArtifactPolicyTests(unittest.TestCase):
    def test_canonical_current_audit_artifacts_are_allowed(self) -> None:
        paths = [
            "papers/Fixture/audit/paper_statement_map.json",
            "papers/Fixture/audit/public_source_role_projection.json",
            "papers/Fixture/audit/source_record_audit.json",
            "papers/Fixture/audit/source_record_match_llm.json",
            "papers/Fixture/audit/source_proof_fidelity.json",
            "papers/Fixture/audit/lean_to_tex_llm.json",
            "papers/Fixture/audit/statement_match_llm.json",
            "papers/Fixture/audit/review_surface_llm.json",
            "papers/Fixture/audit/paper_coverage_llm.json",
            "papers/Fixture/audit/assumption_match_llm.json",
            "papers/Fixture/audit/defect_support_match_llm.json",
        ]

        self.assertEqual(public_release_artifact_issues(paths), [])

    def test_exact_status_referenced_supplement_is_allowed(self) -> None:
        receipt = (
            "papers/Fixture/audit/"
            "source_record_current_revalidation_2026-08-14.json"
        )

        self.assertTrue(public_release_artifact_issues([receipt]))
        self.assertEqual(
            public_release_artifact_issues(
                [receipt], current_audit_artifacts=[receipt]
            ),
            [],
        )
        self.assertTrue(
            public_release_artifact_issues(
                [receipt],
                current_audit_artifacts=[
                    "papers/Other/audit/"
                    "source_record_current_revalidation_2026-08-14.json"
                ],
            )
        )

    def test_working_audit_markers_are_never_excepted(self) -> None:
        paths = [
            "papers/Fixture/audit/legacy/source_record_audit.json",
            "papers/Fixture/audit/source_record_audit.before_refresh.json",
            "papers/Fixture/audit/source_record_historical_snapshot.json",
            "papers/Fixture/audit/manual_review_template.json",
            "papers/Fixture/audit/semantic_review_noncanonical_draft.json",
            "papers/Fixture/audit/receipt_reissue_action_scaffold.json",
            "papers/Fixture/audit/public_source_role_projection.draft.json",
        ]

        issues = public_release_artifact_issues(paths)

        self.assertEqual(len(issues), len(paths))
        self.assertTrue(all("working-audit-artifact" in issue for issue in issues))
        with self.assertRaisesRegex(ValueError, "working/history material"):
            public_release_artifact_issues(
                [paths[1]], current_audit_artifacts=[paths[1]]
            )

    def test_legacy_paper_root_audit_sidecars_are_rejected(self) -> None:
        paths = [
            "papers/Fixture/lean_to_tex_llm.json",
            "papers/Fixture/source_record_audit.json",
            "papers/TEMPLATE/statement_match_llm.json",
        ]

        issues = public_release_artifact_issues(paths)

        self.assertEqual(len(issues), len(paths))
        self.assertTrue(
            all("legacy-root-audit-artifact" in issue for issue in issues), issues
        )

    def test_private_paper_workflow_documents_are_rejected_structurally(self) -> None:
        paths = [
            "papers/One/FORMALIZATION_PLAN.md",
            "papers/Two/docs/PAPER_NOTES.md",
            "papers/Three/START_HERE_NEXT_AGENT.md",
            "papers/Four/docs/HANDOFF_2026-08-14.md",
            "docs/PUBLIC_UPDATE_HANDOFF_2026-08-14.md",
        ]

        issues = public_release_artifact_issues(paths)

        self.assertEqual(len(issues), len(paths))
        self.assertTrue(all("private-document" in issue for issue in issues))

    def test_contributor_template_plan_is_the_only_plan_exception(self) -> None:
        templates = [
            "papers/TEMPLATE/docs/FORMALIZATION_PLAN.md",
            "skills/econcs-formalizer/templates/FORMALIZATION_PLAN.md",
        ]

        self.assertEqual(public_release_artifact_issues(templates), [])
        self.assertTrue(
            public_release_artifact_issues(
                ["papers/TemplatePaper/docs/FORMALIZATION_PLAN.md"]
            )
        )

    def test_source_extraction_trace_and_generated_caches_are_rejected(self) -> None:
        paths = [
            "papers/One/sources/paper.tex",
            "papers/Two/source_tex/main.tex",
            "papers/Three/.audit_source/source.txt",
            "papers/Four/.review_traces/results.jsonl",
            "papers/Five/source_extraction_cache/page-1.txt",
            "scripts/__pycache__/helper.pyc",
            "papers/Six/source-arxiv.tar",
            "papers/Seven/source/subdir/unreviewed.tex",
            "papers/Eight/Source/unreviewed.tex",
            "papers/Nine/opaque-payload.7z",
        ]

        issues = public_release_artifact_issues(paths)

        issue_paths = {issue.split(": ", 2)[1] for issue in issues}
        self.assertEqual(issue_paths, set(paths))
        self.assertTrue(any("private-source-bundle" in issue for issue in issues))
        self.assertTrue(any("private-cache" in issue for issue in issues))

    def test_semantic_names_do_not_reject_mathematical_trace_code_or_citations(self) -> None:
        paths = [
            "AppliedModelingLib/Foundations/Probability/FiniteHorizonTrace.lean",
            "papers/Fixture/docs/citation_source.txt",
            "docs/SOURCE_FIDELITY.md",
            "papers/Fixture/PostFormalizationReport.md",
        ]

        self.assertEqual(public_release_artifact_issues(paths), [])

    def test_latex_build_debris_is_rejected_only_next_to_its_tex_source(self) -> None:
        paths = [
            "papers/Fixture/docs/HUMAN_REVIEW_PACKET.tex",
            "papers/Fixture/docs/HUMAN_REVIEW_PACKET.aux",
            "papers/Fixture/docs/HUMAN_REVIEW_PACKET.fdb_latexmk",
            "papers/Fixture/docs/HUMAN_REVIEW_PACKET.fls",
            "papers/Fixture/docs/HUMAN_REVIEW_PACKET.log",
            "papers/Fixture/docs/HUMAN_REVIEW_PACKET.out",
            "papers/Fixture/docs/HUMAN_REVIEW_PACKET.synctex.gz",
            "papers/Fixture/docs/HUMAN_REVIEW_PACKET.toc",
            "papers/Fixture/docs/HUMAN_REVIEW_PACKET.xdv",
            "examples/intentional.log",
        ]

        issues = public_release_artifact_issues(paths)

        self.assertEqual(len(issues), 8)
        self.assertTrue(
            all("latex-build-artifact" in issue for issue in issues), issues
        )
        self.assertFalse(
            any("examples/intentional.log" in issue for issue in issues), issues
        )

    def test_paths_and_exceptions_must_be_normalized_repo_paths(self) -> None:
        issues = public_release_artifact_issues(
            ["/papers/Fixture/status.json", "papers/Fixture/../status.json"]
        )

        self.assertEqual(len(issues), 2)
        self.assertTrue(all("unsafe-path" in issue for issue in issues))
        with self.assertRaisesRegex(ValueError, "invalid current audit artifact path"):
            public_release_artifact_issues(
                [], current_audit_artifacts=["../audit/receipt.json"]
            )

    def test_results_are_sorted_and_duplicate_issues_are_suppressed(self) -> None:
        paths = [
            "papers/Zeta/PAPER_NOTES.md",
            "papers/Alpha/PAPER_NOTES.md",
            "papers/Zeta/PAPER_NOTES.md",
        ]

        issues = public_release_artifact_issues(paths)

        self.assertEqual(len(issues), 2)
        self.assertIn("papers/Alpha/PAPER_NOTES.md", issues[0])
        self.assertIn("papers/Zeta/PAPER_NOTES.md", issues[1])


if __name__ == "__main__":
    unittest.main()
