#!/usr/bin/env python3
"""Regression tests for source-item v11 contract patch generation."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import generate_v11_source_contracts_patch as generator  # noqa: E402


class GenerateV11SourceContractsPatchTests(unittest.TestCase):
    def test_definition_result_annotation_is_not_treated_as_a_binder(self) -> None:
        proposition, proof = generator._definition_proposition(
            "review_definition_sample", "(x : Nat) : Nat"
        )
        self.assertEqual(
            proposition,
            "∀ (x : Nat), review_definition_sampleSpec (x := x)",
        )
        self.assertEqual(
            proof,
            "by\n    intro x\n    exact review_definition_sampleSpec_proof x",
        )

    def test_contracts_stay_inside_paper_interface_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text(
                "namespace Fixture\nnamespace PaperInterface\n\n"
                "def review_definition_sample (x : Nat) : Nat := x\n"
                "def review_definition_sampleSpec (x : Nat) : Prop :=\n"
                "  review_definition_sample x = x\n"
                "theorem review_definition_sampleSpec_proof (x : Nat) :\n"
                "    review_definition_sampleSpec x := rfl\n\n"
                "end PaperInterface\nend Fixture\n",
                encoding="utf-8",
            )
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "sample_definition": {
                                "lean_declarations": ["review_definition_sample"]
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            prior_root = generator.ROOT
            generator.ROOT = root
            self.addCleanup(setattr, generator, "ROOT", prior_root)
            patch = generator.generate("Fixture")
        self.assertIn("-end PaperInterface", patch)
        self.assertNotIn("-end Fixture", patch)
        self.assertIn("(x : Nat), review_definition_sampleSpec (x := x)", patch)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
