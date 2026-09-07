from __future__ import annotations

import unittest
from pathlib import Path

from scripts.current_closeout.declarations import (
    LeanDeclaration,
    typed_qualified_declaration_identity,
)


class LeanDeclarationRecordTests(unittest.TestCase):
    def declaration(self, **overrides: str) -> LeanDeclaration:
        values = {
            "path": Path("/fixture/PaperInterface.lean"),
            "line": 1,
            "kind": "def",
            "name": "claimSpec",
            "source": "def claimSpec : Prop := True",
            "qualified_name": "Fixture.claimSpec",
            "identity_authority": "legacy_source_diagnostic",
        }
        values.update(overrides)
        return LeanDeclaration(**values)  # type: ignore[arg-type]

    def test_legacy_parser_spelling_is_not_an_accepting_identity(self) -> None:
        self.assertEqual(
            typed_qualified_declaration_identity(self.declaration()),
            "",
        )

    def test_lean_environment_identity_is_accepted(self) -> None:
        self.assertEqual(
            typed_qualified_declaration_identity(
                self.declaration(identity_authority="lean_environment")
            ),
            "Fixture.claimSpec",
        )

    def test_lean_environment_record_without_fqn_fails_closed(self) -> None:
        self.assertEqual(
            typed_qualified_declaration_identity(
                self.declaration(
                    identity_authority="lean_environment",
                    qualified_name="",
                )
            ),
            "",
        )


if __name__ == "__main__":
    unittest.main()
