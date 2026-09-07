from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import lean_axiom_closure as closure


class LeanAxiomClosureTests(unittest.TestCase):
    def test_parse_print_axioms_output(self) -> None:
        parsed = closure.parse_print_axioms_output(
            "'Paper.clean' does not depend on any axioms\n"
            "'Paper.result' depends on axioms: [propext,\n Paper.boundary]\n"
        )
        self.assertEqual(parsed["Paper.clean"], set())
        self.assertEqual(parsed["Paper.result"], {"propext", "Paper.boundary"})

    def test_runner_requires_exact_requested_inventory(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            completed = subprocess.CompletedProcess(
                args=[],
                returncode=0,
                stdout="'Paper.other' does not depend on any axioms\n",
                stderr="",
            )
            with mock.patch.object(
                closure, "_run_lean_script", return_value=completed
            ):
                with self.assertRaisesRegex(
                    closure.LeanAxiomClosureError,
                    "inexact declaration inventory",
                ):
                    closure.run_lean_axiom_closures(
                        root,
                        "Paper.PaperInterface",
                        ["Paper.result"],
                        require_build=False,
                    )


if __name__ == "__main__":
    unittest.main()
