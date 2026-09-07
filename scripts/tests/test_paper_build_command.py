from __future__ import annotations

import unittest

from scripts.paper_build_command import (
    is_exact_portable_paper_build_command,
)


class PaperBuildCommandTests(unittest.TestCase):
    def test_accepts_only_the_exact_paper_root(self) -> None:
        self.assertTrue(
            is_exact_portable_paper_build_command(
                "lake build +Fixture", "Fixture"
            )
        )
        self.assertTrue(
            is_exact_portable_paper_build_command("lake build Fixture", "Fixture")
        )
        self.assertFalse(
            is_exact_portable_paper_build_command(
                "lake build +Fixture.ProofInterface", "Fixture"
            )
        )
        self.assertFalse(
            is_exact_portable_paper_build_command(
                "env LEAN_NUM_THREADS=1 lake build +Fixture", "Fixture"
            )
        )

    def test_malformed_shell_text_is_rejected(self) -> None:
        self.assertFalse(
            is_exact_portable_paper_build_command("lake build 'Fixture", "Fixture")
        )


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
