"""Regressions for production declarations versus ordinary Lean identifiers."""

from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts import audit_repository as audit


class LeanCommandHygieneTests(unittest.TestCase):
    def findings(self, source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Fixture.lean"
            path.write_text(source)
            with patch.object(audit, "approved_paper_proof_boundary_declarations", return_value={}):
                return audit.check_axiom_like_declarations_in_files([path])

    def test_constant_identifier_is_not_an_unproved_declaration(self):
        self.assertEqual(self.findings("""def scaled (constant : Nat) (n : Nat) : Nat :=
  constant * n
theorem scaled_zero (constant : Nat) :
    constant * 0 = 0 := Nat.mul_zero constant
"""), [])

    def test_actual_unproved_or_unsafe_declarations_remain_errors(self):
        findings = self.findings("""axiom missingProof : False
axiom 假设 : False
opaque unprovedValue : Nat
unsafe def unchecked : Nat := 0
""")
        self.assertEqual(len(findings), 4)
        self.assertTrue(all(finding.severity == "ERROR" for finding in findings))

    def test_deliberate_axiom_fixture_remains_detectable_outside_production_scope(self):
        path = audit.ROOT / "AppliedModelingLib/Audit/DeclarationGraphFixtureLibrary.lean"
        self.assertTrue(path.is_file())
        self.assertNotIn(path, audit.library_lean_files())
        self.assertNotIn(path, audit.lean_files(include_active=True))
        findings = audit.check_axiom_like_declarations_in_files([path])
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "ERROR")

    def test_production_imports_cannot_reach_fixture_or_tooling_aggregate(self):
        for module in audit.REGRESSION_FIXTURE_MODULES:
            with self.subTest(module=module), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "Production.lean"
                path.write_text("import\n  " + module + "\n")
                findings = audit.check_test_fixture_isolation_in_files([path])
                self.assertEqual(len(findings), 1)
                self.assertEqual(findings[0].severity, "ERROR")


if __name__ == "__main__":
    unittest.main()
