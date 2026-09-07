from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts.current_closeout.declarations import LeanDeclaration
from scripts.current_closeout.primary_gate import (
    direct_axiom_closure_errors,
    direct_proof_pair_errors,
    evaluate_current_v11_primary_gate,
    partition_review_routes,
)
from scripts.current_closeout.primary_gate_transaction import (
    AcceptedCurrentV11PrimaryGate,
    accepted_current_v11_primary_gate,
    current_v11_primary_gate_result,
    evaluate_and_accept_current_v11_primary_gate,
)
from scripts.evidence_run_context import (
    CommonEvidenceRunContextInputs,
    EvidenceJSONSnapshot,
)
from scripts.obligation_routes import EvidenceRouteSet


class CurrentV11PrimaryGateTests(unittest.TestCase):
    source_path = Path("/fixture/PaperInterface.lean")
    proof_path = Path("/fixture/ProofInterface.lean")

    def declaration(
        self,
        qualified_name: str,
        *,
        path: Path,
        kind: str,
        authority: str = "lean_environment",
    ) -> LeanDeclaration:
        return LeanDeclaration(
            path=path,
            line=1,
            kind=kind,
            name=qualified_name.rsplit(".", 1)[-1],
            source=qualified_name,
            qualified_name=qualified_name,
            identity_authority=authority,
        )

    def declarations(
        self,
        *,
        spec_authority: str = "lean_environment",
    ) -> dict[str, list[LeanDeclaration]]:
        spec = self.declaration(
            "Fixture.claimSpec",
            path=self.source_path,
            kind="def",
            authority=spec_authority,
        )
        proof = self.declaration(
            "Fixture.claimProof",
            path=self.proof_path,
            kind="theorem",
        )
        direct = self.declaration(
            "Fixture.model",
            path=self.source_path,
            kind="def",
        )
        return {
            "Fixture.claimSpec": [spec],
            "claimSpec": [spec],
            "Fixture.claimProof": [proof],
            "claimProof": [proof],
            "Fixture.model": [direct],
            "model": [direct],
        }

    def route_set(self) -> EvidenceRouteSet:
        return EvidenceRouteSet.from_source_map(
            {
                "items": {
                    "claim": {
                        "semantic_contract": {
                            "spec_declaration": "Fixture.claimSpec",
                            "evidence_declaration": "Fixture.claimProof",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        }
                    },
                    "model": {
                        "source_kind": "definition",
                        "inventory_role": "source_semantic_declaration",
                        "lean_declarations": ["Fixture.model"],
                    },
                }
            }
        )

    def partition(
        self,
        *,
        declarations: dict[str, list[LeanDeclaration]] | None = None,
    ):
        return partition_review_routes(
            paper_id="Fixture",
            review_names=("claimSpec", "model"),
            route_set=self.route_set(),
            declarations=declarations or self.declarations(),
        )

    def contracts(self, *, axioms: list[str] | None = None):
        return {
            ("Fixture.claimSpec", "Fixture.claimProof", "proves"): {
                "specification": "Fixture.claimSpec",
                "evidence": "Fixture.claimProof",
                "mode": "proves",
                "matches": True,
                "evidence_axiom_closure_checked": True,
                "evidence_axiom_closure": axioms or [],
                "evidence_is_unsafe": False,
                "evidence_value_has_sorry": False,
            }
        }

    def inventory(self):
        return {
            "declarations": [
                {
                    "declaration": "Fixture.claimSpec",
                    "axiom_closure_checked": True,
                    "axiom_closure": [],
                    "is_unsafe": False,
                    "value_has_sorry": False,
                },
                {
                    "declaration": "Fixture.model",
                    "axiom_closure_checked": True,
                    "axiom_closure": [],
                    "is_unsafe": False,
                    "value_has_sorry": False,
                },
            ]
        }

    def test_partition_and_proof_pair_pass_from_typed_records(self) -> None:
        partition = self.partition()
        self.assertEqual(partition.errors, ())
        self.assertEqual(
            direct_proof_pair_errors(
                paper_id="Fixture",
                partition=partition,
                declarations=self.declarations(),
                source_path=self.source_path,
                proof_declaration_kinds=frozenset({"theorem", "lemma"}),
                contract_rows=self.contracts(),
            ),
            (),
        )

    def test_typed_proof_pair_is_location_agnostic_but_theorem_checked(self) -> None:
        declarations = self.declarations()
        proof = declarations["Fixture.claimProof"][0]
        relocated = self.declaration(
            "Fixture.claimProof",
            path=Path("/fixture/ImportedLibrary.lean"),
            kind="theorem",
        )
        declarations["Fixture.claimProof"] = [relocated]
        declarations["claimProof"] = [relocated]
        self.assertEqual(
            direct_proof_pair_errors(
                paper_id="Fixture",
                partition=self.partition(declarations=declarations),
                declarations=declarations,
                source_path=self.source_path,
                proof_declaration_kinds=frozenset({"theorem", "lemma"}),
                contract_rows=self.contracts(),
            ),
            (),
        )

        nonproof = self.declaration(
            "Fixture.claimProof",
            path=proof.path,
            kind="def",
        )
        declarations["Fixture.claimProof"] = [nonproof]
        declarations["claimProof"] = [nonproof]
        errors = direct_proof_pair_errors(
            paper_id="Fixture",
            partition=self.partition(declarations=declarations),
            declarations=declarations,
            source_path=self.source_path,
            proof_declaration_kinds=frozenset({"theorem", "lemma"}),
            contract_rows=self.contracts(),
        )
        self.assertEqual(len(errors), 1)
        self.assertIn("not a theorem/lemma", errors[0])

    def test_parser_derived_spelling_cannot_enter_current_partition(self) -> None:
        partition = self.partition(
            declarations=self.declarations(
                spec_authority="legacy_source_diagnostic"
            )
        )
        self.assertTrue(partition.errors)
        self.assertIn("has no typed result", partition.errors[0])

    def test_axiom_gate_passes_direct_and_result_routes(self) -> None:
        self.assertEqual(
            direct_axiom_closure_errors(
                paper_id="Fixture",
                include_names=("claimSpec", "model"),
                partition=self.partition(),
                declarations=self.declarations(),
                declaration_inventory=self.inventory(),
                contract_rows=self.contracts(),
                approved_axioms=frozenset(),
            ),
            (),
        )

    def test_axiom_gate_rejects_unapproved_proof_debt(self) -> None:
        errors = direct_axiom_closure_errors(
            paper_id="Fixture",
            include_names=("claimSpec", "model"),
            partition=self.partition(),
            declarations=self.declarations(),
            declaration_inventory=self.inventory(),
            contract_rows=self.contracts(axioms=["Fixture.unapproved"]),
            approved_axioms=frozenset(),
        )
        self.assertEqual(len(errors), 1)
        self.assertIn("Fixture.unapproved", errors[0])

    def test_duplicate_source_routes_fail_closed(self) -> None:
        route_set = EvidenceRouteSet.from_source_map(
            {
                "items": {
                    key: {
                        "semantic_contract": {
                            "spec_declaration": "Fixture.claimSpec",
                            "evidence_declaration": "Fixture.claimProof",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        }
                    }
                    for key in ("first", "second")
                }
            }
        )
        partition = partition_review_routes(
            paper_id="Fixture",
            review_names=("claimSpec",),
            route_set=route_set,
            declarations=self.declarations(),
        )
        self.assertEqual(len(partition.errors), 1)
        self.assertIn("multiple source items", partition.errors[0])

    def test_primary_gate_import_has_no_legacy_or_presentation_authority(self) -> None:
        root = Path(__file__).resolve().parents[2]
        environment = dict(os.environ)
        environment["PYTHONPATH"] = str(root)
        probe = """
import sys
import scripts.current_closeout.primary_gate

for forbidden in (
    "scripts.audit_repository",
    "scripts.audit_evidence_integrity",
    "scripts.review_dashboard",
    "scripts.review_dashboard_packet",
    "scripts.review_surface_structure",
    "scripts.lean_signature_manifest",
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
        self.assertEqual(
            result.returncode,
            0,
            msg=result.stdout + result.stderr,
        )

    def _closed_gate_fixture(
        self,
        root: Path,
        *,
        proof_in_interface: bool = False,
    ) -> dict[str, object]:
        folder = root / "papers" / "Fixture"
        source_path = folder / "PaperInterface.lean"
        proof_path = folder / "ProofInterface.lean"
        interface_source = (
            b"def claimSpec : Prop := True\ndef model : Nat := 1\n"
            + (
                b"theorem claimProof : claimSpec := by trivial\n"
                if proof_in_interface
                else b""
            )
        )
        sources = {
            "Fixture.PaperInterface": (
                source_path,
                interface_source,
            ),
        }
        if not proof_in_interface:
            sources["Fixture.ProofInterface"] = (
                proof_path,
                b"theorem claimProof : claimSpec := by trivial\n",
            )

        def node(
            declaration: str,
            *,
            module: str,
            line: int,
            source: bytes,
            kind: str,
            axioms: list[str] | None = None,
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
                "axiom_closure_checked": True,
                "axiom_closure": axioms or [],
                "is_unsafe": False,
                "value_has_sorry": False,
            }

        inventory = {
            "declarations": [
                node(
                    "Fixture.claimSpec",
                    module="Fixture.PaperInterface",
                    line=1,
                    source=sources["Fixture.PaperInterface"][1],
                    kind="definition",
                ),
                node(
                    "Fixture.model",
                    module="Fixture.PaperInterface",
                    line=2,
                    source=sources["Fixture.PaperInterface"][1],
                    kind="definition",
                ),
                node(
                    "Fixture.claimProof",
                    module=(
                        "Fixture.PaperInterface"
                        if proof_in_interface
                        else "Fixture.ProofInterface"
                    ),
                    line=3 if proof_in_interface else 1,
                    source=(
                        interface_source
                        if proof_in_interface
                        else sources["Fixture.ProofInterface"][1]
                    ),
                    kind="theorem",
                ),
            ]
        }
        atoms = [
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": {"tag": "const", "name": "True"},
                "display": "True",
            }
        ]
        semantic_atoms = [
            {key: value for key, value in atom.items() if key != "display"}
            for atom in atoms
        ]
        atom_digest = hashlib.sha256(
            json.dumps(
                {"schema": 1, "atoms": semantic_atoms},
                ensure_ascii=True,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        ).hexdigest()
        manifest_digest = hashlib.sha256(b"fixture-manifest").hexdigest()
        contracts = self.contracts()
        surface = SimpleNamespace(
            semantic_targets={
                "Fixture.claimSpec": {
                    "review_claim_atoms": atoms,
                    "review_claim_atoms_sha256": atom_digest,
                    "review_claim_manifest_sha256": manifest_digest,
                }
            },
            review_claim_manifests={
                "Fixture.claimSpec": {
                    "claim_atoms": atoms,
                    "claim_atoms_sha256": atom_digest,
                    "manifest_sha256": manifest_digest,
                }
            },
            source_declarations={},
            semantic_contracts=contracts,
            declaration_inventory=inventory,
            module_sources=sources,
        )
        source_map = {
            "items": {
                "claim": {
                    "semantic_contract": {
                        "spec_declaration": "Fixture.claimSpec",
                        "evidence_declaration": "Fixture.claimProof",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    }
                },
                "model": {
                    "source_kind": "definition",
                    "inventory_role": "source_semantic_declaration",
                    "lean_declarations": ["Fixture.model"],
                },
            }
        }
        status = {
            "id": "Fixture",
            "title": "Fixture paper",
            "source_version": "fixture source",
            "build_target": "lake build Fixture",
            "status": "formalized",
            "review_entrypoint": "papers/Fixture/FINAL_VALIDATION_REPORT.md",
            "paper_interface": {
                "path": "papers/Fixture/PaperInterface.lean",
                "oversized": False,
            },
            "review_surface": {
                "source_file": "papers/Fixture/PaperInterface.lean",
                "proof_file": "papers/Fixture/ProofInterface.lean",
                "assumption_source_file": "papers/Fixture/Assumptions.lean",
                "assumption_policy": "strict",
                "include_names": ["claimSpec", "model"],
                "assumption_names": [],
                "auxiliary_names": [],
                "quarantined_auxiliary_names": [],
                "proof_boundary_names": [],
                "proposition_spec_proofs": {"claimSpec": "claimProof"},
            },
        }
        return {
            "folder": folder,
            "surface": surface,
            "source_map": source_map,
            "status": status,
        }

    def _evaluate_fixture(
        self,
        fixture: dict[str, object],
        *,
        semantic_review_current: bool = True,
    ):
        folder = fixture["folder"]
        assert isinstance(folder, Path)
        return evaluate_current_v11_primary_gate(
            repository_root=folder.parents[1],
            paper_id="Fixture",
            folder=folder,
            status_payload=fixture["status"],  # type: ignore[arg-type]
            source_map=fixture["source_map"],  # type: ignore[arg-type]
            surface=fixture["surface"],
            semantic_review_current=semantic_review_current,
            semantic_review_error="fixture semantic mismatch",
        )

    def test_closed_current_primary_gate_accepts_one_typed_graph(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self._closed_gate_fixture(Path(temporary))
            result = self._evaluate_fixture(fixture)
        self.assertTrue(result.accepted, result.errors)

    def test_closed_current_primary_gate_allows_endpoint_in_paper_interface(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self._closed_gate_fixture(
                Path(temporary), proof_in_interface=True
            )
            result = self._evaluate_fixture(fixture)
        self.assertTrue(result.accepted, result.errors)

    def test_closed_current_primary_gate_ignores_stale_status_selection(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self._closed_gate_fixture(Path(temporary))
            status = fixture["status"]
            assert isinstance(status, dict)
            review_surface = status["review_surface"]
            assert isinstance(review_surface, dict)
            review_surface["include_names"] = ["obsoleteSpec"]
            review_surface["source_condition_items"] = ["obsolete-condition"]
            review_surface["proposition_spec_proofs"] = {
                "obsoleteSpec": "obsoleteProof"
            }
            result = self._evaluate_fixture(fixture)
        self.assertTrue(result.accepted, result.errors)

    def test_configured_assumption_uses_lean_owned_support_inventory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self._closed_gate_fixture(Path(temporary))
            folder = fixture["folder"]
            surface = fixture["surface"]
            status = fixture["status"]
            assert isinstance(folder, Path)
            assert isinstance(surface, SimpleNamespace)
            assert isinstance(status, dict)
            assumption_path = folder / "Assumptions.lean"
            assumption_source = b"def sourceCondition : Prop := True\n"
            surface.module_sources["Fixture.Assumptions"] = (
                assumption_path,
                assumption_source,
            )
            surface.declaration_inventory["declarations"].append(
                {
                    "declaration": "Fixture.sourceCondition",
                    "module": "Fixture.Assumptions",
                    "declaration_kind": "definition",
                    "paper_owned": False,
                    "source_presented": False,
                    "generated_from_owner": False,
                    "review_owner_declaration": "Fixture.sourceCondition",
                    "source_range": {
                        "line_start": 1,
                        "column_start": 0,
                        "line_end": 1,
                        "column_end": len("def sourceCondition : Prop := True"),
                    },
                    "axiom_closure_checked": True,
                    "axiom_closure": [],
                    "is_unsafe": False,
                    "value_has_sorry": False,
                }
            )
            review_surface = status["review_surface"]
            assert isinstance(review_surface, dict)
            review_surface["assumption_names"] = ["Fixture.sourceCondition"]
            result = self._evaluate_fixture(fixture)
        self.assertTrue(result.accepted, result.errors)

    def test_unretained_external_source_does_not_empty_support_inventory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self._closed_gate_fixture(Path(temporary))
            surface = fixture["surface"]
            assert isinstance(surface, SimpleNamespace)
            surface.declaration_inventory["declarations"].append(
                {
                    "declaration": "Mathlib.Unretained.externalHelper",
                    "module": "Mathlib.Unretained",
                    "declaration_kind": "definition",
                    "paper_owned": False,
                    "source_presented": False,
                    "generated_from_owner": False,
                    "review_owner_declaration": "Mathlib.Unretained.externalHelper",
                    "source_range": {
                        "line_start": 1,
                        "column_start": 0,
                        "line_end": 1,
                        "column_end": 1,
                    },
                    "axiom_closure_checked": True,
                    "axiom_closure": [],
                    "is_unsafe": False,
                    "value_has_sorry": False,
                }
            )
            result = self._evaluate_fixture(fixture)
        self.assertTrue(result.accepted, result.errors)

    def test_malformed_unrelated_inventory_node_does_not_empty_support_inventory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self._closed_gate_fixture(Path(temporary))
            surface = fixture["surface"]
            assert isinstance(surface, SimpleNamespace)
            surface.declaration_inventory["declarations"].append(
                {
                    "declaration": "Fixture.unreadableHelper",
                    "module": "Fixture.Interface",
                    "declaration_kind": "definition",
                    "paper_owned": False,
                    "source_presented": False,
                    "generated_from_owner": False,
                    "review_owner_declaration": "Fixture.unreadableHelper",
                    "source_range": {"line_start": 999, "line_end": 999},
                    "axiom_closure_checked": True,
                    "axiom_closure": [],
                    "is_unsafe": False,
                    "value_has_sorry": False,
                }
            )
            result = self._evaluate_fixture(fixture)
        self.assertTrue(result.accepted, result.errors)

    def test_status_proof_routing_metadata_is_not_a_second_authority(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self._closed_gate_fixture(Path(temporary))
            status = fixture["status"]
            assert isinstance(status, dict)
            review_surface = status["review_surface"]
            assert isinstance(review_surface, dict)
            review_surface.pop("proof_file")
            review_surface["proposition_spec_proofs"] = {
                "obsoleteSpec": "obsoleteProof"
            }
            result = self._evaluate_fixture(fixture)
        self.assertTrue(result.accepted, result.errors)

    def test_closed_current_primary_gate_keeps_each_obligation_mandatory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            semantic_fixture = self._closed_gate_fixture(root)
            self.assertTrue(
                self._evaluate_fixture(
                    semantic_fixture, semantic_review_current=False
                ).semantic_errors
            )

            proof_fixture = self._closed_gate_fixture(root)
            proof_surface = proof_fixture["surface"]
            assert isinstance(proof_surface, SimpleNamespace)
            proof_surface.semantic_contracts[
                ("Fixture.claimSpec", "Fixture.claimProof", "proves")
            ]["matches"] = False
            self.assertTrue(self._evaluate_fixture(proof_fixture).proof_errors)

            axiom_fixture = self._closed_gate_fixture(root)
            axiom_surface = axiom_fixture["surface"]
            assert isinstance(axiom_surface, SimpleNamespace)
            axiom_surface.declaration_inventory["declarations"][0][
                "axiom_closure"
            ] = ["Fixture.unapproved"]
            self.assertTrue(self._evaluate_fixture(axiom_fixture).axiom_errors)

            structure_fixture = self._closed_gate_fixture(root)
            structure_surface = structure_fixture["surface"]
            assert isinstance(structure_surface, SimpleNamespace)
            structure_surface.review_claim_manifests[
                "Fixture.claimSpec"
            ]["claim_atoms_sha256"] = "0" * 64
            self.assertTrue(
                self._evaluate_fixture(structure_fixture).structure_errors
            )

            metadata_fixture = self._closed_gate_fixture(root)
            metadata_status = metadata_fixture["status"]
            assert isinstance(metadata_status, dict)
            metadata_status.pop("source_version")
            self.assertTrue(
                self._evaluate_fixture(metadata_fixture).configuration_errors
            )

            summary_fixture = self._closed_gate_fixture(root)
            summary_status = summary_fixture["status"]
            assert isinstance(summary_status, dict)
            summary_status["human_summary_review"] = {
                "status": "human_approved"
            }
            self.assertTrue(
                self._evaluate_fixture(summary_fixture).configuration_errors
            )

    def test_configured_assumption_must_resolve_in_exact_assumption_surface(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self._closed_gate_fixture(Path(temporary))
            status = fixture["status"]
            assert isinstance(status, dict)
            review_surface = status["review_surface"]
            assert isinstance(review_surface, dict)
            review_surface["assumption_names"] = ["missingAssumption"]
            result = self._evaluate_fixture(fixture)
        self.assertTrue(result.structure_errors)
        self.assertIn("missingAssumption", result.structure_errors[0])

    def test_nonexistent_boundary_name_cannot_approve_an_axiom(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = self._closed_gate_fixture(Path(temporary))
            status = fixture["status"]
            surface = fixture["surface"]
            assert isinstance(status, dict)
            assert isinstance(surface, SimpleNamespace)
            review_surface = status["review_surface"]
            assert isinstance(review_surface, dict)
            review_surface["assumption_names"] = ["unapproved"]
            review_surface["proof_boundary_names"] = ["unapproved"]
            surface.semantic_contracts[
                ("Fixture.claimSpec", "Fixture.claimProof", "proves")
            ]["evidence_axiom_closure"] = ["Fixture.unapproved"]
            result = self._evaluate_fixture(fixture)
        self.assertFalse(result.axiom_errors)
        self.assertTrue(result.structure_errors)
        self.assertFalse(result.accepted)

    def test_transaction_gate_requires_nominal_context_and_reuses_one_result(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            fixture = self._closed_gate_fixture(root)
            folder = fixture["folder"]
            status = fixture["status"]
            source_map = fixture["source_map"]
            assert isinstance(folder, Path)
            assert isinstance(status, dict)
            assert isinstance(source_map, dict)

            def snapshot(path: Path, payload: dict[str, object]):
                return EvidenceJSONSnapshot(
                    path=path,
                    sha256=hashlib.sha256(
                        json.dumps(payload, sort_keys=True).encode("utf-8")
                    ).hexdigest(),
                    payload=payload,
                    raw_bytes=json.dumps(payload, sort_keys=True).encode("utf-8"),
                )

            context = CommonEvidenceRunContextInputs(
                folder=folder,
                status="formalized",
                audit_config_snapshot=snapshot(
                    root / "papers" / "audit_config.json", {"schema": 1}
                ),
                status_snapshot=snapshot(folder / "status.json", status),
                statement_map_snapshot=snapshot(
                    folder / "audit" / "paper_statement_map.json", source_map
                ),
                source_proof_fidelity_snapshot=None,
                sidecar_snapshots=(),
                source_proof_fidelity_path_error="",
            ).issue_v11(None)
            semantic = SimpleNamespace(
                surface=fixture["surface"],
                selection_error="",
                findings=(),
                semantic_review_current=True,
            )
            with mock.patch(
                "scripts.current_closeout.primary_gate_transaction."
                "current_v11_semantic_review_result",
                return_value=semantic,
            ) as semantic_review:
                first = current_v11_primary_gate_result(
                    root, folder, context=context
                )
                second = current_v11_primary_gate_result(
                    root, folder, context=context
                )
                accepted_result, accepted = (
                    evaluate_and_accept_current_v11_primary_gate(
                        root,
                        folder,
                        context=context,
                    )
                )
                repeated_result, repeated = (
                    evaluate_and_accept_current_v11_primary_gate(
                        root,
                        folder,
                        context=context,
                    )
                )

        self.assertTrue(first.accepted, first.errors)
        self.assertIs(first, second)
        self.assertIs(first, accepted_result)
        self.assertIs(first, repeated_result)
        self.assertIsNotNone(accepted)
        self.assertIs(accepted, repeated)
        self.assertIs(accepted, accepted_current_v11_primary_gate(context))
        copied = replace(context)
        self.assertIsNone(accepted_current_v11_primary_gate(copied))
        with self.assertRaises(TypeError):
            AcceptedCurrentV11PrimaryGate(
                object(),
                context=context,
                result=first,
                surface=accepted.surface,  # type: ignore[union-attr]
            )
        semantic_review.assert_called_once()


if __name__ == "__main__":
    unittest.main()
