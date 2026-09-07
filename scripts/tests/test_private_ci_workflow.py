from __future__ import annotations

import re
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / ".github" / "workflows" / "lean_action_ci.yml"


class PrivateCIWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.text = WORKFLOW.read_text(encoding="utf-8")

    def step(self, name: str) -> str:
        match = re.search(
            rf"(?ms)^\s*- name: {re.escape(name)}\s*$"
            r"(?P<body>.*?)(?=^\s*- name:|\Z)",
            self.text,
        )
        self.assertIsNotNone(match, name)
        return match.group("body")

    def test_lean_setup_is_bounded_and_skipped_for_docs_only_prs(self) -> None:
        body = self.step("Set up Lean dependencies")
        self.assertRegex(body, r"steps\.change-scope\.outputs\.mode != 'docs'")
        self.assertRegex(body, r"uses: leanprover/lean-action@[0-9a-f]{40}")
        for field in ("auto-config", "build", "test", "lint", "use-github-cache"):
            self.assertRegex(body, rf'{field}:\s*["\']?false["\']?')
        self.assertRegex(body, r'use-mathlib-cache:\s*["\']?true["\']?')
        self.assertRegex(self.text, r'LEAN_NUM_THREADS:\s*["\']?1["\']?')

    def test_pr_scope_is_derived_from_exact_base_and_head(self) -> None:
        checkout = self.step("Check out repository")
        self.assertIn("github.event.pull_request.head.sha", checkout)
        self.assertIn("github.sha", checkout)
        self.assertRegex(checkout, r"persist-credentials:\s*false")

        configured = self.step("Configure trusted CI workspace")
        self.assertIn("$RUNNER_TEMP/econcslib-trusted-$GITHUB_RUN_ID-$GITHUB_RUN_ATTEMPT", configured)
        self.assertIn('>> "$GITHUB_ENV"', configured)
        self.assertNotIn("${{ runner.temp }}", self.text)

        trusted = self.step("Materialize trusted CI implementation")
        self.assertIn('git archive "$BASE_SHA" scripts config', trusted)
        self.assertIn('tar -x -C "$TRUSTED_CI_ROOT"', trusted)
        self.assertIn('BASE_SHA: ${{ github.event.pull_request.base.sha }}', trusted)
        self.assertLess(
            self.text.index("- name: Configure trusted CI workspace"),
            self.text.index("- name: Materialize trusted CI implementation"),
        )

        body = self.step("Classify pull request scope")
        self.assertIn('"$TRUSTED_CI_ROOT/scripts/paper_contribution.py" scope', body)
        self.assertIn('--repo "$GITHUB_WORKSPACE"', body)
        self.assertIn('BASE_SHA: ${{ github.event.pull_request.base.sha }}', body)
        self.assertIn('--base "$BASE_SHA"', body)
        self.assertIn("--head HEAD", body)
        self.assertIn("--github-output", body)
        self.assertIn('echo "mode=integration"', body)
        self.assertNotIn('echo "mode=paper"', body)
        self.assertNotRegex(
            body,
            r"(?m)^\s+python3 scripts/paper_contribution\.py scope",
        )
        self.assertLess(
            self.text.index("- name: Materialize trusted CI implementation"),
            self.text.index("- name: Classify pull request scope"),
        )

    def test_pr_engine_guard_uses_base_branch_implementation(self) -> None:
        body = self.step("Check formalization engine revision (pull request)")
        self.assertIn('TRUSTED_CHECKER="$TRUSTED_CI_ROOT/scripts/', body)
        self.assertIn('--repo "$GITHUB_WORKSPACE"', body)
        self.assertIn('BASE_SHA: ${{ github.event.pull_request.base.sha }}', body)
        self.assertIn('--base-tree "$BASE_SHA"', body)
        self.assertIn('cd "$GITHUB_WORKSPACE"', body)
        self.assertIn('SCOPE_MODE: ${{ steps.contribution-scope.outputs.mode }}', body)
        self.assertIn('[[ "$SCOPE_MODE" == "integration" ]]', body)
        candidate_fallback = re.search(
            r'elif \[\[ "\$SCOPE_MODE" == "integration" \]\]; then(?P<body>.*?)else',
            body,
            re.DOTALL,
        )
        self.assertIsNotNone(candidate_fallback)
        self.assertIn(
            "python3 scripts/check_formalization_engine_revision.py",
            candidate_fallback.group("body"),
        )

    def test_all_pull_request_modes_check_the_committed_diff(self) -> None:
        body = self.step("Check committed pull request formatting")
        self.assertIn("github.event_name == 'pull_request'", body)
        self.assertIn('BASE_SHA: ${{ github.event.pull_request.base.sha }}', body)
        self.assertIn('git diff --check "$BASE_SHA" HEAD --', body)

    def test_isolated_paper_lane_uses_one_scoped_entrypoint(self) -> None:
        body = self.step("Check isolated paper contribution")
        self.assertIn("outputs.mode == 'paper'", body)
        self.assertIn(
            '"$TRUSTED_CI_ROOT/scripts/paper_contribution.py" check "$PAPER"',
            body,
        )
        self.assertIn('--repo "$GITHUB_WORKSPACE"', body)
        self.assertIn('--base "$BASE_SHA"', body)
        self.assertIn("--allow-missing-source-bytes", body)
        for forbidden in (
            "run: lake build",
            "audit_conclusion_provenance.py",
            "audit_evidence_integrity.py",
            "review_dashboard.py",
            "sync_paper_status.py",
        ):
            self.assertNotIn(forbidden, body)

    def test_every_broad_step_requires_integration_even_on_main_pushes(self) -> None:
        broad_steps = (
            "Build Lean targets",
            "Test semantic provenance audits",
            "Audit conclusion-bearing theorem inputs",
            "Audit source-evidence integrity",
            "Audit reusable library provenance",
            "Audit statement translations",
            "Audit paper coverage",
        )
        for name in broad_steps:
            with self.subTest(name=name):
                body = self.step(name)
                self.assertNotIn("github.event_name != 'pull_request'", body)
                self.assertIn("steps.change-scope.outputs.mode == 'integration'", body)

    def test_aggregate_only_pr_skips_lean_and_runs_only_projection_check(self) -> None:
        setup = self.step("Set up Lean dependencies")
        self.assertIn("steps.change-scope.outputs.mode != 'docs'", setup)

        aggregate = self.step("Check aggregate-only contribution")
        self.assertIn("outputs.mode == 'aggregate'", aggregate)
        self.assertIn('"$TRUSTED_CI_ROOT/scripts/sync_paper_status.py"', aggregate)
        self.assertIn("--aggregate-only --check", aggregate)
        self.assertIn('--repo "$GITHUB_WORKSPACE"', aggregate)

        for name in (
            "Build Lean targets",
            "Test semantic provenance audits",
            "Audit conclusion-bearing theorem inputs",
            "Audit source-evidence integrity",
            "Audit reusable library provenance",
            "Audit statement translations",
            "Audit paper coverage",
            "Full repository closeout audit",
        ):
            with self.subTest(name=name):
                self.assertNotIn("outputs.mode == 'aggregate'", self.step(name))

    def test_main_push_refreshes_projection_before_checking_it(self) -> None:
        refresh_name = "Check aggregate projection after main push"
        refresh = self.step(refresh_name)
        self.assertIn("github.event_name == 'push'", refresh)
        self.assertIn("sync_paper_status.py --aggregate-only --check", refresh)
        self.assertIn('[[ "$status" -eq 1 ]]', refresh)
        self.assertIn('[[ "$status" -ne 0 ]]', refresh)
        self.assertLess(
            self.text.index(f"- name: {refresh_name}"),
            self.text.index("- name: Check paper status aggregate"),
        )

    def test_full_aggregate_check_remains_hard_failing_for_integration(self) -> None:
        body = self.step("Check paper status aggregate")
        self.assertIn("github.event_name == 'workflow_dispatch'", body)
        self.assertIn("outputs.mode == 'integration'", body)
        self.assertNotIn("outputs.mode == 'aggregate'", body)
        self.assertNotIn("github.event_name != 'pull_request'", body)

    def test_change_selection_uses_trusted_base_for_prs_and_exact_push_base(self) -> None:
        body = self.step("Select changed-work validation")
        self.assertIn('$TRUSTED_CI_ROOT/scripts/ci_change_scope.py', body)
        self.assertIn('github.event.before', body)
        self.assertIn('--base "$EVENT_BASE" --head HEAD', body)
        self.assertIn('echo "mode=integration"', body)
        self.assertNotIn('echo "mode=papers"', body)

    def test_batch_paper_validation_keeps_build_and_evidence_checks(self) -> None:
        build = self.step("Build changed papers and their dependents")
        checks = self.step("Validate selected paper evidence")
        for body in (build, checks):
            self.assertIn("steps.change-scope.outputs.mode == 'papers'", body)
            self.assertIn('"$CI_SCOPE_TOOL"', body)
            self.assertIn('--base "$CI_BASE_SHA" --head HEAD', body)
        self.assertIn(' build ', build)
        self.assertIn(' check ', checks)

    def test_only_successful_trusted_main_runs_save_project_cache(self) -> None:
        restore = self.step("Restore project build cache")
        save = self.step("Save trusted main project build cache")
        prune = self.step("Remove obsolete cached module interfaces")
        self.assertIn('path: .lake/build', restore)
        self.assertIn('path: .lake/build', save)
        self.assertIn("success() && github.event_name == 'push'", save)
        self.assertIn("github.ref == 'refs/heads/main'", save)
        self.assertIn('prune-cache', prune)
        self.assertLess(self.text.index('- name: Remove obsolete cached module interfaces'),
                        self.text.index('- name: Build changed papers and their dependents'))

    def test_integration_build_enumerates_registered_not_only_default_targets(self) -> None:
        body = self.step("Build Lean targets")
        self.assertIn("paper_target_registration.py build-all", body)
        self.assertNotRegex(body, r"run:\s*lake build(?:\s|$)")

    def test_full_closeout_is_not_scheduled_for_paper_lane(self) -> None:
        body = self.step("Full repository closeout audit")
        self.assertIn("outputs.mode == 'integration'", body)
        self.assertNotIn("outputs.mode == 'paper'", body)
        self.assertIn("audit_repository.py --include-active", body)


if __name__ == "__main__":
    unittest.main()
