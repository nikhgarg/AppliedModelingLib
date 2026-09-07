"""Regression tests for the explicit v11 interface migrator."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts import migrate_legacy_paperinterface_v11 as migration


class MigrateLegacyPaperInterfaceV11Tests(unittest.TestCase):
    def _paper_dir(self, root: Path, interface: str) -> Path:
        paper_dir = root / "Demo"
        paper_dir.mkdir()
        (paper_dir / "status.json").write_text(
            json.dumps({"review_surface": {"include_names": ["condition"]}}),
            encoding="utf-8",
        )
        (paper_dir / "ProofBridge.lean").write_text(interface, encoding="utf-8")
        return paper_dir

    def _config(self) -> dict[str, object]:
        return {
            "paper": "Demo",
            "namespace": "Demo",
            "proof_bridge_module": "Demo.ProofBridge",
            "include_names": ["condition"],
            "semantic_imports": [],
            "source_definition_declarations": {"condition": "legacyCondition"},
        }

    def test_direct_prop_definition_becomes_one_semantic_spec(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(
                Path(directory),
                """namespace Demo
namespace ProofBridge
def legacyCondition (p : Prop) : Prop := p
theorem legacyCondition_proved (p : Prop) : legacyCondition p := p
end ProofBridge
end Demo
""",
            )
            paper, proof = migration.render(paper_dir=paper_dir, config=self._config())
        self.assertIn(
            "def conditionSpec (p : Prop) : Prop :=\n"
            "  p",
            paper,
        )
        self.assertIn(
            "theorem condition_realizes_spec (p : Prop) : "
            "Demo.ProofBridge.legacyCondition (p := p) ↔ "
            "conditionSpec (p := p) := by\n"
            "  rfl",
            proof,
        )

    def test_value_definition_needs_an_explicit_source_formula(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(
                Path(directory),
                """namespace Demo
namespace ProofBridge
def legacyCondition (n : Nat) : Nat := n
end ProofBridge
end Demo
""",
            )
            with self.assertRaisesRegex(
                migration.MigrationError, "only direct Prop definitions"
            ):
                migration.render(paper_dir=paper_dir, config=self._config())

    def test_explicit_value_definition_displays_its_transparent_body(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(
                Path(directory),
                """namespace Demo
namespace ProofBridge
def legacyCondition (n : Nat) : Nat := n + 1
end ProofBridge
end Demo
""",
            )
            config = self._config()
            config.pop("source_definition_declarations")
            config["source_value_definition_declarations"] = {
                "condition": "legacyCondition"
            }
            paper, proof = migration.render(paper_dir=paper_dir, config=config)
        self.assertIn(
            "def conditionSpec (n : Nat) : Prop :=\n"
            "  Demo.ProofBridge.legacyCondition (n := n) =\n"
            "    n + 1",
            paper,
        )
        self.assertIn(
            "theorem condition_realizes_spec (n : Nat) : conditionSpec (n := n) := by\n  rfl",
            proof,
        )

    def test_definition_bundle_keeps_each_abbrev_clause_visible(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(
                Path(directory),
                """namespace Demo
namespace ProofBridge
abbrev first (n : Nat) : Nat := n + 1
abbrev second (n : Nat) : Nat := n + 2
end ProofBridge
end Demo
""",
            )
            config = self._config()
            config.pop("source_definition_declarations")
            config["source_definition_bundles"] = {"condition": ["first", "second"]}
            paper, proof = migration.render(paper_dir=paper_dir, config=config)
        self.assertIn("Demo.ProofBridge.first (n := n) = n + 1", paper)
        self.assertIn("Demo.ProofBridge.second (n := n) = n + 2", paper)
        self.assertIn("theorem condition_realizes_spec : conditionSpec := by\n  unfold conditionSpec\n  exact ⟨by intros; rfl, by intros; rfl⟩", proof)

    def test_definition_bundle_can_retain_a_source_theorem_component(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(
                Path(directory),
                """namespace Demo
namespace ProofBridge
abbrev first (n : Nat) : Nat := n + 1
theorem bridge (n : Nat) : first n = n + 1 := by rfl
end ProofBridge
end Demo
""",
            )
            config = self._config()
            config.pop("source_definition_declarations")
            config["source_definition_bundles"] = {"condition": ["first", "bridge"]}
            paper, proof = migration.render(paper_dir=paper_dir, config=config)
        self.assertIn("∀ (n : Nat), Demo.ProofBridge.first (n := n) = n + 1", paper)
        self.assertIn("∀ (n : Nat), first n = n + 1", paper)
        self.assertIn("by intro n; exact Demo.ProofBridge.bridge (n := n)", proof)

    def test_polymorphic_at_alias_requires_an_explicit_special_row(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(
                Path(directory),
                """namespace Demo
namespace ProofBridge
abbrev carrier := @List
end ProofBridge
end Demo
""",
            )
            config = self._config()
            config.pop("source_definition_declarations")
            config["source_definition_bundles"] = {"condition": ["carrier"]}
            with self.assertRaisesRegex(
                migration.MigrationError, "hides its universe binders"
            ):
                migration.render(paper_dir=paper_dir, config=config)

    def test_special_row_cannot_hide_a_theorem_type_behind_type_of(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(
                Path(directory),
                """namespace Demo
namespace ProofBridge
theorem legacyCondition : True := trivial
end ProofBridge
end Demo
""",
            )
            config = self._config()
            config.pop("source_definition_declarations")
            config["special_rows"] = {
                "condition": {
                    "spec": "def conditionSpec : Prop := type_of% (@Demo.ProofBridge.legacyCondition)",
                    "endpoint": "theorem condition : conditionSpec := by exact trivial",
                }
            }
            with self.assertRaisesRegex(migration.MigrationError, "uses `type_of`"):
                migration.render(paper_dir=paper_dir, config=config)

    def test_ordinary_theorem_cannot_hide_a_theorem_type_behind_type_of(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(
                Path(directory),
                """namespace Demo
namespace ProofBridge
theorem condition : type_of% (@Demo.ProofBridge.legacyCondition) := by trivial
theorem legacyCondition : True := trivial
end ProofBridge
end Demo
""",
            )
            config = self._config()
            config.pop("source_definition_declarations")
            with self.assertRaisesRegex(migration.MigrationError, "uses `type_of`"):
                migration.render(paper_dir=paper_dir, config=config)

    def test_external_source_definition_copies_the_complete_source_formula(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(
                Path(directory),
                """namespace Demo
namespace ProofBridge
theorem condition : True := trivial
end ProofBridge
end Demo
""",
            )
            (paper_dir / "SourceDefinitions.lean").write_text(
                """namespace Demo
def sourceCondition {α : Type*} (x : α) : Prop := x = x
end Demo
""",
                encoding="utf-8",
            )
            config = self._config()
            config.pop("source_definition_declarations")
            config["external_source_declarations"] = {
                "condition": {
                    "source_file": "SourceDefinitions.lean",
                    "source_declaration": "sourceCondition",
                }
            }
            paper, proof = migration.render(paper_dir=paper_dir, config=config)
        self.assertIn(
            "def conditionSpec {α : Type*} (x : α) : Prop :=\n  x = x", paper
        )
        self.assertIn(
            "theorem condition_realizes_spec {α : Type*} (x : α) : conditionSpec (α := α) (x := x) := by\n  rfl",
            proof,
        )

    def test_external_source_structure_exposes_every_named_field(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(
                Path(directory),
                """namespace Demo
namespace ProofBridge
theorem condition : True := trivial
end ProofBridge
end Demo
""",
            )
            (paper_dir / "SourceDefinitions.lean").write_text(
                """namespace Demo
structure SourceModel (A B : Type*) where
  encode : A → B
  valid : A → Prop
end Demo
""",
                encoding="utf-8",
            )
            config = self._config()
            config.pop("source_definition_declarations")
            config["external_source_declarations"] = {
                "condition": {
                    "source_file": "SourceDefinitions.lean",
                    "source_declaration": "SourceModel",
                }
            }
            paper, proof = migration.render(paper_dir=paper_dir, config=config)
        self.assertIn(
            "∀ value : Demo.SourceModel A B,\n"
            "    ∃ encode : A → B,\n"
            "    ∃ valid : A → Prop,\n"
            "      value.encode = encode ∧\n"
            "      value.valid = valid",
            paper,
        )
        self.assertIn(
            "exact ⟨value.encode, value.valid, rfl, rfl⟩", proof
        )

    def test_theorem_header_with_let_does_not_absorb_its_proof(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Source.lean"
            path.write_text(
                """namespace Demo
theorem sourceTheorem (n : Nat) :
    let m := n + 1
    m = n + 1 := by rfl

theorem later : True := trivial
end Demo
""",
                encoding="utf-8",
            )
            declarations = migration._theorem_declarations_in_file(path)
        source = declarations["sourceTheorem"][1]
        self.assertIn("let m := n + 1", source)
        self.assertNotIn(":= by", source)
        self.assertNotIn("theorem later", source)

    def test_presentation_sections_keep_main_claims_before_appendix_claims(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(
                Path(directory),
                """namespace Demo
namespace ProofBridge
theorem condition : True := trivial
end ProofBridge
end Demo
""",
            )
            status = json.loads((paper_dir / "status.json").read_text(encoding="utf-8"))
            status["review_surface"]["include_names"] = ["condition", "appendix"]
            (paper_dir / "status.json").write_text(json.dumps(status), encoding="utf-8")
            (paper_dir / "ProofBridge.lean").write_text(
                """namespace Demo
namespace ProofBridge
theorem condition : True := trivial
theorem appendix : True := trivial
end ProofBridge
end Demo
""",
                encoding="utf-8",
            )
            config = self._config()
            config["include_names"] = ["condition", "appendix"]
            config.pop("source_definition_declarations")
            config["presentation_sections"] = [
                {"title": "Main-text source claims", "names": ["condition"]},
                {"title": "Appendix source claims", "names": ["appendix"]},
            ]
            paper, _proof = migration.render(paper_dir=paper_dir, config=config)
        self.assertLess(
            paper.index("## Main-text source claims"),
            paper.index("def conditionSpec"),
        )
        self.assertLess(
            paper.index("def conditionSpec"),
            paper.index("## Appendix source claims"),
        )
        self.assertLess(
            paper.index("## Appendix source claims"),
            paper.index("def appendixSpec"),
        )


if __name__ == "__main__":
    unittest.main()
