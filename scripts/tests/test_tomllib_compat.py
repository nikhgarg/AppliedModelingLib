from __future__ import annotations

import io
import subprocess
import sys
import unittest
from pathlib import Path

from scripts.tomllib_compat import tomllib


ROOT = Path(__file__).resolve().parents[2]


class TomllibCompatTests(unittest.TestCase):
    def test_parser_exposes_standard_loads_and_decode_error(self) -> None:
        payload = tomllib.loads(
            'name = "Fixture"\n[[lean_lib]]\nname = "Paper26Result"\n'
        )
        self.assertEqual(payload["name"], "Fixture")
        self.assertEqual(payload["lean_lib"], [{"name": "Paper26Result"}])
        stream_payload = tomllib.load(
            io.BytesIO(b'agent = "fixture"\nscopes = ["papers/Fixture"]\n')
        )
        self.assertEqual(stream_payload["agent"], "fixture")
        self.assertEqual(stream_payload["scopes"], ["papers/Fixture"])
        with self.assertRaises(tomllib.TOMLDecodeError):
            tomllib.loads("name = 1\nname = 2\n")

    def test_python_cli_entrypoints_import_on_supported_runtime(self) -> None:
        entrypoints = (
            "lean_import_closure.py",
            "paper_contribution.py",
            "paper_target_registration.py",
            "public_release_candidate_guard.py",
            "shared_worktree_status.py",
            "sync_paper_status.py",
            "work_claim.py",
        )
        for entrypoint in entrypoints:
            with self.subTest(entrypoint=entrypoint):
                completed = subprocess.run(
                    [sys.executable, f"scripts/{entrypoint}", "--help"],
                    cwd=ROOT,
                    check=False,
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(
                    completed.returncode,
                    0,
                    completed.stdout + completed.stderr,
                )

    def test_python_310_help_survives_without_site_packages(self) -> None:
        if sys.version_info[:2] != (3, 10):
            self.skipTest("isolated missing-backend regression targets Python 3.10")
        completed = subprocess.run(
            [sys.executable, "-S", "scripts/paper_contribution.py", "--help"],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)

    def test_python_310_doctor_explains_missing_parser(self) -> None:
        if sys.version_info[:2] != (3, 10):
            self.skipTest("isolated missing-backend regression targets Python 3.10")
        completed = subprocess.run(
            [sys.executable, "-S", "scripts/paper_contribution.py", "doctor"],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("pip install -r requirements.txt", completed.stdout + completed.stderr)


if __name__ == "__main__":
    unittest.main()
