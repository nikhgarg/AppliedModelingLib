from __future__ import annotations

import os
from pathlib import Path
import re
import subprocess
import tempfile
import textwrap
import unittest


WORKFLOW = Path(__file__).resolve().parents[2] / ".github/workflows/lean_action_ci.yml"


class HostedRunnerDiskBudgetTests(unittest.TestCase):
    def setUp(self) -> None:
        self.workflow = WORKFLOW.read_text()
        match = re.search(
            r"(?ms)^      - name: Make room for Lean build artifacts\n"
            r"(?P<body>.*?)(?=^      - name:)", self.workflow,
        )
        self.assertIsNotNone(match)
        self.step = match.group("body")
        self.script = textwrap.dedent(self.step.split("        run: |\n", 1)[1])

    def execute(self, environment: str | None) -> tuple[subprocess.CompletedProcess, str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            calls = root / "calls"
            # Intercept the destructive command; execute the actual workflow shell.
            sudo = root / "sudo"
            sudo.write_text('#!/bin/sh\nprintf "%s\\n" "$@" >> "$DISK_TEST_CALLS"\n')
            sudo.chmod(0o755)
            env = dict(os.environ, PATH=f"{root}:{os.environ['PATH']}",
                       DISK_TEST_CALLS=str(calls))
            env.pop("RUNNER_ENVIRONMENT", None)
            if environment is not None:
                env["RUNNER_ENVIRONMENT"] = environment
            result = subprocess.run(["bash", "-euo", "pipefail", "-c", self.script],
                                    cwd=root, env=env, text=True, capture_output=True)
            return result, calls.read_text() if calls.exists() else ""

    def test_cleanup_is_before_dependencies_and_excludes_documentation_jobs(self) -> None:
        self.assertIn("steps.change-scope.outputs.mode != 'docs'", self.step)
        self.assertIn("runner.environment == 'github-hosted'", self.step)
        self.assertLess(self.workflow.index("- name: Make room for Lean build artifacts"),
                        self.workflow.index("- name: Set up Lean dependencies"))

    def test_hosted_cleanup_targets_only_the_fixed_unused_sdks(self) -> None:
        result, calls = self.execute("github-hosted")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls.splitlines(), ["rm", "-rf", "--",
                         "/usr/local/lib/android", "/usr/share/dotnet",
                         "/usr/local/.ghcup", "/opt/ghc"])

    def test_nonhosted_or_missing_environment_never_attempts_cleanup(self) -> None:
        for value in (None, "", "self-hosted", "github-hosted; echo unsafe"):
            with self.subTest(environment=value):
                result, calls = self.execute(value)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(calls, "")


if __name__ == "__main__":
    unittest.main()
