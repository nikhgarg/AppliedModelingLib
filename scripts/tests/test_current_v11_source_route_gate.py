from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace

from scripts.current_closeout.source_route_gate import (
    current_v11_source_route_errors,
)


class CurrentV11SourceRouteGateTests(unittest.TestCase):
    def fixture(self, root: Path) -> dict[str, object]:
        folder = root / "papers" / "Fixture"
        interface = folder / "PaperInterface.lean"
        proof = folder / "ProofInterface.lean"
        interface_source = (
            b"def claimSpec : Prop := True\n"
            b"def model : Nat := 1\n"
            b"theorem defectWitness : True := by trivial\n"
        )
        proof_source = b"theorem claimProof : claimSpec := by trivial\n"
        module_sources = {
            "Fixture.PaperInterface": (interface, interface_source),
            "Fixture.ProofInterface": (proof, proof_source),
        }

        def node(
            declaration: str,
            *,
            module: str,
            line: int,
            kind: str,
            source: bytes,
        ) -> dict[str, object]:
            text = source.decode("utf-8").splitlines()[line - 1]
            return {
                "declaration": declaration,
                "module": module,
                "declaration_kind": kind,
                "paper_owned": True,
                "source_presented": True,
                "generated_from_owner": False,
                "review_owner_declaration": declaration,
                "source_range": {
                    "line_start": line,
                    "column_start": 0,
                    "line_end": line,
                    "column_end": len(text),
                },
            }

        inventory = {
            "declarations": [
                node(
                    "Fixture.claimSpec",
                    module="Fixture.PaperInterface",
                    line=1,
                    kind="definition",
                    source=interface_source,
                ),
                node(
                    "Fixture.model",
                    module="Fixture.PaperInterface",
                    line=2,
                    kind="definition",
                    source=interface_source,
                ),
                node(
                    "Fixture.defectWitness",
                    module="Fixture.PaperInterface",
                    line=3,
                    kind="theorem",
                    source=interface_source,
                ),
                node(
                    "Fixture.claimProof",
                    module="Fixture.ProofInterface",
                    line=1,
                    kind="theorem",
                    source=proof_source,
                ),
            ]
        }
        source_map = {
            "semantic_contract_schema": 1,
            "items": {
                "claim": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "lean_declarations": ["Fixture.claimProof"],
                    "support_lean_declarations": ["Fixture.claimSpec"],
                    "source_claim_atoms": [
                        {
                            "reviewed_lean_route": "Fixture.claimProof",
                        }
                    ],
                    "semantic_contract": {
                        "spec_declaration": "Fixture.claimSpec",
                        "evidence_declaration": "Fixture.claimProof",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                },
                "model": {
                    "source_kind": "definition",
                    "claim_bearing": True,
                    "inventory_role": "source_semantic_declaration",
                    "lean_declarations": ["Fixture.model"],
                    "source_claim_atoms": [
                        {
                            "reviewed_lean_route": "Fixture.model",
                        }
                    ],
                },
                "defect": {
                    "source_kind": "claim",
                    "claim_bearing": True,
                    "inventory_role": "quarantined_source_defect",
                    "support_lean_declarations": ["Fixture.defectWitness"],
                },
            },
        }
        status = {"review_surface": {}}
        surface = SimpleNamespace(
            declaration_inventory=inventory,
            module_sources=module_sources,
            library_source_declarations={},
            paper_semantic_targets={"Fixture.model": {}},
            library_semantic_targets={},
        )
        return {
            "source_map": source_map,
            "status": status,
            "surface": surface,
        }

    def errors(self, fixture: dict[str, object]) -> tuple[str, ...]:
        return current_v11_source_route_errors(
            paper_id="Fixture",
            status_payload=fixture["status"],  # type: ignore[arg-type]
            source_map=fixture["source_map"],  # type: ignore[arg-type]
            surface=fixture["surface"],
        )

    def test_exact_typed_route_projection_passes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(Path(temporary))
            errors = self.errors(fixture)
        self.assertEqual(errors, ())

    def test_atom_navigation_cannot_disagree_with_typed_route(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(Path(temporary))
            source_map = fixture["source_map"]
            assert isinstance(source_map, dict)
            source_map["items"]["claim"]["source_claim_atoms"][0][
                "reviewed_lean_route"
            ] = "Fixture.defectWitness"
            errors = self.errors(fixture)
        self.assertTrue(any("does not equal the typed semantic route" in e for e in errors))

    def test_navigation_list_cannot_omit_typed_proof(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(Path(temporary))
            source_map = fixture["source_map"]
            assert isinstance(source_map, dict)
            source_map["items"]["claim"]["lean_declarations"] = [
                "Fixture.defectWitness"
            ]
            errors = self.errors(fixture)
        self.assertTrue(any("omit the typed proof endpoint" in e for e in errors))

    def test_checked_strengthening_navigation_is_not_a_second_graph_root(self) -> None:
        """A retained stronger theorem cannot reopen source-route discovery."""

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(Path(temporary))
            source_map = fixture["source_map"]
            assert isinstance(source_map, dict)
            source_map["items"]["claim"]["support_lean_declarations"] = [
                "Fixture.claimSpec",
                "Fixture.historicalStrengthening",
            ]
            source_map["items"]["claim"]["checked_strengthening_declarations"] = [
                {
                    "declaration": "Fixture.historicalStrengthening",
                    "classification": "checked_strengthening_not_literal_source_coverage",
                }
            ]
            errors = self.errors(fixture)

        self.assertEqual(errors, ())

    def test_direct_source_declaration_needs_lean_semantic_classification(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(Path(temporary))
            surface = fixture["surface"]
            assert isinstance(surface, SimpleNamespace)
            surface.paper_semantic_targets = {}
            errors = self.errors(fixture)
        self.assertTrue(any("lacks one Lean-classified semantic target" in e for e in errors))

    def test_quarantined_defect_needs_typed_theorem_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(Path(temporary))
            source_map = fixture["source_map"]
            assert isinstance(source_map, dict)
            source_map["items"]["defect"]["support_lean_declarations"] = []
            errors = self.errors(fixture)
        self.assertTrue(any("quarantined Lean theorem/lemma" in e for e in errors))

    def test_deep_navigation_cannot_create_a_second_current_route(self) -> None:
        """Historical support links do not reopen Lean graph discovery."""

        with tempfile.TemporaryDirectory() as temporary:
            fixture = self.fixture(Path(temporary))
            source_map = fixture["source_map"]
            assert isinstance(source_map, dict)
            source_map["items"]["historical_support"] = {
                "source_kind": "model_context",
                "claim_bearing": False,
                "inventory_role": "proof_support",
                # This declaration is deliberately absent from the retained
                # current graph.  It is navigation history, not source-to-Lean
                # semantic evidence.
                "support_lean_declarations": ["Fixture.OldHelper"],
            }
            errors = self.errors(fixture)

        self.assertEqual(errors, ())

    def test_gate_import_does_not_load_mixed_audit_monoliths(self) -> None:
        root = Path(__file__).resolve().parents[2]
        environment = dict(os.environ)
        environment["PYTHONPATH"] = str(root)
        probe = """
import sys
import scripts.current_closeout.source_route_gate
for forbidden in (
    "scripts.audit_repository",
    "scripts.audit_evidence_integrity",
    "scripts.review_dashboard",
):
    assert forbidden not in sys.modules, forbidden
"""
        result = subprocess.run(
            [sys.executable, "-c", probe],
            cwd=root,
            env=environment,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
