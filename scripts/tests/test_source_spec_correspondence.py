#!/usr/bin/env python3
"""Focused regressions for the atom-level theorem-realization closeout lane."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    value = str(import_root)
    if value not in sys.path:
        sys.path.insert(0, value)

import audit_evidence_integrity as integrity  # noqa: E402
import audit_repository as repository  # noqa: E402
import source_manifest_validation as source_manifest  # noqa: E402


def digest(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


def source_atom(*, atom_id: str = "main_clause", route: str = "Fixture.Proof") -> dict[str, str]:
    return {
        "id": atom_id,
        "source_locator": "source.txt:1",
        "semantic_claim": "For every admissible input, the displayed outcome equals zero.",
        "reviewed_lean_route": route,
        # Runtime correspondence validation verifies the receipt's shape; the
        # source-inventory test below exercises current-byte verification in a
        # real canonical artifact fixture.
        "source_quote_sha256": digest("fixture source quote"),
    }


def source_item(*, atom: dict[str, str] | None = None) -> dict[str, object]:
    return {
        "claim_bearing": True,
        "source_kind": "theorem",
        "title": "Theorem 1. Fixture source result",
        "source_location": "source.txt:1",
        "semantic_contract": {
            "spec_declaration": "Fixture.SourceSpec",
            "evidence_declaration": "Fixture.Proof",
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        },
        "source_claim_atoms": [atom or source_atom()],
    }


def closure(*, nodes: list[dict[str, object]] | None = None, failures: list[dict[str, str]] | None = None) -> dict[str, object]:
    return {
        "sha256": digest("closure"),
        "surface_sha256": digest("surface"),
        "closure_module_context_sha256": digest("narrow module context"),
        "surface_mode": "closure_expanded" if not failures else "terminal_fallback",
        "surface": {
            "binder_domains": [],
            "body": {
                "tag": "app",
                "fn": {"tag": "const", "origin": "foundation"},
                "arg": {"tag": "lit", "value": "0"},
            },
        },
        "nodes": nodes or [],
        "failures": failures or [],
    }


def correspondence(
    item: dict[str, object],
    current_closure: dict[str, object],
    *,
    bindings: list[dict[str, object]] | None = None,
    dispositions: list[dict[str, object]] | None = None,
) -> dict[str, object]:
    raw_atoms = item["source_claim_atoms"]
    assert isinstance(raw_atoms, list)
    atom_sha = integrity.source_claim_atom_semantic_sha256(raw_atoms[0])
    component_sha = str(current_closure["surface_sha256"])
    record: dict[str, object] = {
        "schema": 1,
        "source_atoms_sha256": integrity.source_claim_atoms_semantic_sha256(raw_atoms),
        "spec_closure_sha256": current_closure["sha256"],
        "spec_surface_sha256": current_closure["surface_sha256"],
        "closure_environment_sha256": current_closure[
            "closure_module_context_sha256"
        ],
        "source_atom_bindings": bindings
        if bindings is not None
        else [
            {
                "source_atom_sha256": atom_sha,
                "spec_component_sha256s": [component_sha],
                "semantic_bridge": "The source equality is represented by the complete canonical proposition body.",
            }
        ],
        "closure_node_dispositions": dispositions if dispositions is not None else [],
    }
    record["item_identity_sha256"] = integrity.source_spec_correspondence_item_identity_sha256(
        item["semantic_contract"], record
    )
    return record


class SourceSpecCorrespondenceTests(unittest.TestCase):
    def test_valid_subsumed_result_support_is_not_a_second_proof_obligation(
        self,
    ) -> None:
        target = source_item()
        support: dict[str, object] = {
            "claim_bearing": True,
            "source_kind": "lemma",
            "title": "Lemma 1. Displayed proof witnesses",
            "statement": "Lemma 1 displays witnesses supporting Theorem 1.",
            "coverage_status": "subsumed_by_selected_result",
            "inventory_role": "subsumed_by_selected_result",
            "protocol_role": "subsumed_by_selected_result",
            "source_status": "subsumed_by_selected_result",
            "source_scope_classification": (
                "source_resolved_within_paper_observation"
            ),
            "scope_disposition": "supporting_context_for_selected_result",
            "subsumed_by_source_item": "selected_result",
        }
        payload: dict[str, object] = {
            "source_coverage_mode": "named_theoretical_statements",
            "semantic_contract_schema": 1,
            "items": {
                "selected_result": target,
                "support_presentation": support,
            },
        }

        with tempfile.TemporaryDirectory() as temporary, mock.patch.object(
            source_manifest,
            "source_index_byte_pinned_anchor_item_ids",
            return_value=set(),
        ):
            paper = Path(temporary) / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            map_path = audit / "paper_statement_map.json"

            def contract_inventory_messages(
                candidate: dict[str, object],
            ) -> list[str]:
                map_path.write_text(json.dumps(candidate), encoding="utf-8")
                return [
                    finding.message
                    for finding in integrity.semantic_contract_inventory_findings(
                        paper, "formalized", require_source_bytes=False
                    )
                ]

            selected, mode_error = source_manifest._source_map_proof_obligation_items(
                paper, payload
            )
            self.assertEqual(mode_error, "")
            self.assertEqual(set(selected), {"selected_result"})
            self.assertEqual(
                source_manifest.validated_subsumed_result_contract_exemptions(
                    paper, payload
                ),
                {"support_presentation": "selected_result"},
            )
            contract_messages = contract_inventory_messages(payload)
            self.assertFalse(
                any(
                    "claim-bearing source item `support_presentation` lacks semantic_contract"
                    in message
                    for message in contract_messages
                ),
                contract_messages,
            )

            invalid_cases = {
                "missing_target": lambda item, _target: item.update(
                    subsumed_by_source_item="missing"
                ),
                "nested_subsumption": lambda _item, selected_target: selected_target.update(
                    subsumed_by_source_item="support_presentation"
                ),
                "missing_target_contract": lambda _item, selected_target: selected_target.pop(
                    "semantic_contract"
                ),
                "active_support_route": lambda item, _target: item.update(
                    lean_declarations=["Fixture.DuplicateProof"]
                ),
            }
            for case, mutate in invalid_cases.items():
                with self.subTest(case):
                    invalid = copy.deepcopy(payload)
                    invalid_items = invalid["items"]
                    assert isinstance(invalid_items, dict)
                    invalid_support = invalid_items["support_presentation"]
                    invalid_target = invalid_items["selected_result"]
                    assert isinstance(invalid_support, dict)
                    assert isinstance(invalid_target, dict)
                    mutate(invalid_support, invalid_target)
                    invalid_selected, _ = (
                        source_manifest._source_map_proof_obligation_items(
                            paper, invalid
                        )
                    )
                    self.assertIn("support_presentation", invalid_selected)
                    validated, errors = (
                        source_manifest._subsumed_by_selected_result_classification(
                            paper, invalid
                        )
                    )
                    self.assertNotIn("support_presentation", validated)
                    self.assertTrue(errors)
                    contract_messages = contract_inventory_messages(invalid)
                    self.assertTrue(
                        any(
                            "claim-bearing source item `support_presentation` lacks semantic_contract"
                            in message
                            for message in contract_messages
                        ),
                        contract_messages,
                    )

    def test_strict_scope_keeps_out_of_scope_formula_from_blocking_root_receipt(
        self,
    ) -> None:
        """Only source-inventory roots receive strict closure/correspondence work.

        Ordinary semantic contracts outside the named-theory source scope are
        still independently checked.  In particular, a formula's ordinary
        transparency failure remains visible, but cannot make an unrelated
        in-scope theorem lose its exact strict receipt.
        """

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            interface = folder / "PaperInterface.lean"
            (folder / "audit").mkdir(parents=True)
            interface.write_text("namespace Fixture\nend Fixture\n", encoding="utf-8")

            def declaration(
                name: str, kind: str, source: str, line: int
            ) -> repository.LeanDeclaration:
                return repository.LeanDeclaration(interface, line, kind, name, source)

            root_spec = declaration(
                "InScopeSpec",
                "abbrev",
                "abbrev InScopeSpec : Prop := (0 : Nat) = 0",
                1,
            )
            root_proof = declaration(
                "InScopeProof",
                "theorem",
                "theorem InScopeProof : InScopeSpec := rfl",
                2,
            )
            formula_spec = declaration(
                "FormulaSpec",
                "abbrev",
                "abbrev FormulaSpec : Prop := (0 : Nat) = 0",
                3,
            )
            formula_proof = declaration(
                "FormulaProof",
                "theorem",
                "theorem FormulaProof : FormulaSpec := rfl",
                4,
            )
            auxiliary_spec = declaration(
                "AuxiliarySpec",
                "abbrev",
                "abbrev AuxiliarySpec : Prop := (0 : Nat) = 0",
                5,
            )
            auxiliary_proof = declaration(
                "AuxiliaryProof",
                "theorem",
                "theorem AuxiliaryProof : AuxiliarySpec := rfl",
                6,
            )
            declarations = {
                "Fixture.InScopeSpec": [root_spec],
                "Fixture.InScopeProof": [root_proof],
                "Fixture.FormulaSpec": [formula_spec],
                "Fixture.FormulaProof": [formula_proof],
                "Fixture.AuxiliarySpec": [auxiliary_spec],
                "Fixture.AuxiliaryProof": [auxiliary_proof],
            }

            def contract(spec: str, evidence: str) -> dict[str, str]:
                return {
                    "spec_declaration": spec,
                    "evidence_declaration": evidence,
                    "evidence_mode": "proves",
                    "semantic_shape": "plain",
                }

            root_contract = contract("Fixture.InScopeSpec", "Fixture.InScopeProof")
            root_correspondence: dict[str, object] = {
                "schema": 1,
                "source_atoms_sha256": digest("root atoms"),
                "spec_closure_sha256": digest("root closure"),
                "spec_surface_sha256": digest("root surface"),
                "closure_environment_sha256": digest("root environment"),
                "source_atom_bindings": [],
                "closure_node_dispositions": [],
            }
            root_correspondence["item_identity_sha256"] = (
                repository.source_spec_correspondence_item_identity_sha256(
                    root_contract, root_correspondence
                )
            )
            payload: dict[str, object] = {
                "semantic_contract_schema": 1,
                "source_spec_correspondence_schema": 1,
                "items": {
                    "in_scope_root": {
                        "claim_bearing": True,
                        "source_kind": "theorem",
                        "semantic_contract": root_contract,
                        "source_spec_correspondence": root_correspondence,
                    },
                    "out_of_scope_formula": {
                        "claim_bearing": True,
                        "source_kind": "formula",
                        "semantic_contract": contract(
                            "Fixture.FormulaSpec", "Fixture.FormulaProof"
                        ),
                    },
                    "out_of_scope_auxiliary": {
                        "claim_bearing": True,
                        "source_kind": "equation",
                        "semantic_contract": contract(
                            "Fixture.AuxiliarySpec", "Fixture.AuxiliaryProof"
                        ),
                    },
                },
            }
            status_payload = {
                "review_surface": {
                    "include_names": list(declarations),
                    "assumption_names": [],
                }
            }

            class RecordingContext:
                evidence_context = None
                build_input_provider = None

                def __init__(self) -> None:
                    self.scope: tuple[str, ...] = ()
                    self.receipts: list[object] = []

                def record_strict_source_spec_correspondence_scope_keys(
                    self, source_item_keys: object
                ) -> None:
                    assert isinstance(source_item_keys, frozenset)
                    self.scope = tuple(sorted(source_item_keys))

                def record_strict_source_spec_correspondence_receipt(
                    self, receipt: object
                ) -> None:
                    self.receipts.append(receipt)

                def exact_json_payload(self, _path: Path) -> None:
                    return None

            context = RecordingContext()
            closure_requests: list[tuple[str, ...]] = []
            runtime_requests: list[dict[str, object]] = []

            def closure_manifests(*args: object, **_kwargs: object) -> dict[str, object]:
                specs = args[2]
                assert isinstance(specs, list)
                closure_requests.append(tuple(specs))
                return {"Fixture.InScopeSpec": {"fixture": "root closure"}}

            def runtime_errors(
                raw_item: object, _closure: object
            ) -> list[str]:
                assert isinstance(raw_item, dict)
                runtime_requests.append(raw_item)
                return []

            transparent = {
                "Fixture.InScopeSpec": {
                    "passes": True,
                    "failure_tag": "",
                    "failure_declaration": "",
                },
                "Fixture.FormulaSpec": {
                    "passes": False,
                    "failure_tag": "recursive_local_definition",
                    "failure_declaration": "Fixture.executeFormula",
                },
                "Fixture.AuxiliarySpec": {
                    "passes": True,
                    "failure_tag": "",
                    "failure_declaration": "",
                },
            }
            matches = {
                ("Fixture.InScopeSpec", "Fixture.InScopeProof", "proves"): True,
                ("Fixture.FormulaSpec", "Fixture.FormulaProof", "proves"): True,
                ("Fixture.AuxiliarySpec", "Fixture.AuxiliaryProof", "proves"): False,
            }

            with mock.patch.object(
                repository,
                "semantic_contract_closeout_bridge_inventory",
                return_value=(
                    integrity.SemanticContractCloseoutInventory(
                        contract_item_keys=("in_scope_root",),
                        scope_exclusion_item_keys=(),
                    ),
                    [],
                ),
            ), mock.patch(
                "scripts.audit_evidence_integrity.semantic_contract_inventory_findings",
                return_value=[],
            ), mock.patch(
                "scripts.lean_signature_manifest.paper_local_module_names",
                return_value={"Fixture"},
            ), mock.patch(
                "scripts.lean_signature_manifest.foreign_model_definition_scope",
                return_value=((), (), ""),
            ), mock.patch(
                "scripts.lean_signature_manifest.run_lean_semantic_contract_transparency_checks",
                return_value=transparent,
            ), mock.patch(
                "scripts.lean_signature_manifest.run_lean_semantic_contract_closure_manifests",
                side_effect=closure_manifests,
            ), mock.patch(
                "scripts.lean_signature_manifest.run_lean_semantic_contract_matches",
                return_value=matches,
            ), mock.patch.object(
                repository,
                "source_spec_correspondence_runtime_errors",
                side_effect=runtime_errors,
            ):
                findings = repository.paper_statement_map_semantic_contract_findings(
                    "Fixture",
                    folder,
                    "formalized",
                    payload,
                    declarations,
                    set(),
                    status_payload,
                    run_context=context,  # type: ignore[arg-type]
                )

        self.assertEqual(context.scope, ("in_scope_root",))
        self.assertEqual(closure_requests, [("Fixture.InScopeSpec",)])
        self.assertEqual(len(runtime_requests), 1)
        self.assertIs(runtime_requests[0], payload["items"]["in_scope_root"])
        self.assertEqual(
            [getattr(receipt, "source_item_key", "") for receipt in context.receipts],
            ["in_scope_root"],
        )
        messages = [finding.message for finding in findings]
        self.assertTrue(
            any("out_of_scope_formula" in message for message in messages), messages
        )
        self.assertTrue(
            any("out_of_scope_auxiliary" in message for message in messages), messages
        )

    def test_boolean_schema_markers_never_activate_a_versioned_gate(self) -> None:
        self.assertFalse(integrity.schema_version_is_exact(True, 1))
        self.assertFalse(integrity.schema_version_is_supported(True, {1, 2}))
        self.assertTrue(
            integrity.semantic_contract_validation_errors(
                {
                    "spec_declaration": "Fixture.Spec",
                    "evidence_declaration": "Fixture.Proof",
                    "evidence_mode": "proves",
                    "semantic_shape": "plain",
                },
                schema=True,
            )
        )
        self.assertTrue(
            integrity.semantic_surface_validation_errors({"schema": True})
        )

        with tempfile.TemporaryDirectory() as temporary:
            paper = Path(temporary) / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_claim_atoms_schema": True,
                        "source_spec_correspondence_schema": True,
                        "items": {"source_claim": source_item()},
                    }
                ),
                encoding="utf-8",
            )
            atom_messages = [
                finding.message
                for finding in integrity.source_claim_atom_inventory_findings(
                    paper, "formalized"
                )
            ]
            correspondence_messages = [
                finding.message
                for finding in integrity.source_spec_correspondence_inventory_findings(
                    paper, "formalized"
                )
            ]
        self.assertTrue(
            any("source_claim_atoms_schema must be 1" in message for message in atom_messages),
            atom_messages,
        )
        self.assertTrue(
            any(
                "source_spec_correspondence_schema must be 1" in message
                for message in correspondence_messages
            ),
            correspondence_messages,
        )

    def test_only_current_byte_pinned_presentation_aliases_may_inherit_contracts(self) -> None:
        """An alias is a second presentation, not a second Lean-route owner."""

        with tempfile.TemporaryDirectory() as temporary:
            paper = Path(temporary) / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            source = paper / "source.txt"
            source_text = (
                "Theorem 1. Every admissible input has a witness.\n"
                "Theorem 1. Every admissible input has a witness.\n"
            )
            source.write_text(source_text, encoding="utf-8")

            def anchor(line: int) -> dict[str, object]:
                quote = source_text.splitlines()[line - 1]
                return {
                    "path": "source.txt",
                    "line_start": line,
                    "line_end": line,
                    "quoted_text": quote,
                    "quoted_text_sha256": hashlib.sha256(
                        quote.encode("utf-8")
                    ).hexdigest(),
                }

            canonical = source_item(
                atom={
                    "id": "main_clause",
                    "source_locator": "source.txt:1",
                    "semantic_claim": "Every admissible input has a witness.",
                    "reviewed_lean_route": "Fixture.Proof",
                    "source_quote_sha256": hashlib.sha256(
                        source_text.splitlines()[0].encode("utf-8")
                    ).hexdigest(),
                }
            )
            canonical.update(
                {
                    "source_anchor_evidence": [anchor(1)],
                    "statement": source_text.splitlines()[0],
                }
            )
            alias: dict[str, object] = {
                "source_kind": "theorem",
                "claim_bearing": True,
                "source_location": "source.txt:2",
                "source_anchor_evidence": [anchor(2)],
                "statement": source_text.splitlines()[1],
                "source_presentation_alias": {
                    "schema": 1,
                    "relation": "repeated_source_presentation",
                    "canonical_source_item": "canonical",
                    "semantic_basis": (
                        "The independently byte-pinned presentations have the same "
                        "hypotheses, scope, and conclusion."
                    ),
                    "validator": "fixture source reconciliation",
                    "validated_at": "2026-07-29T12:00:00Z",
                },
            }
            payload: dict[str, object] = {
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": hashlib.sha256(
                    source.read_bytes()
                ).hexdigest(),
                "source_coverage_mode": "named_theoretical_statements",
                "source_claim_atoms_schema": 1,
                "source_spec_correspondence_schema": 1,
                "semantic_contract_schema": 1,
                "items": {"canonical": canonical, "appendix_alias": alias},
            }
            map_path = audit / "paper_statement_map.json"
            map_path.write_text(json.dumps(payload), encoding="utf-8")

            self.assertEqual(
                integrity.validated_presentation_alias_contract_exemptions(
                    paper, payload
                ),
                {"appendix_alias": "canonical"},
            )
            strict_messages = [
                finding.message
                for finding in integrity.source_spec_correspondence_inventory_findings(
                    paper, "formalized"
                )
            ]
            contract_messages = [
                finding.message
                for finding in integrity.semantic_contract_inventory_findings(
                    paper, "formalized"
                )
            ]
            self.assertFalse(
                any(
                    "items.appendix_alias: v11 requires an exact semantic_contract"
                    in message
                    for message in strict_messages
                ),
                strict_messages,
            )
            self.assertFalse(
                any(
                    "claim-bearing source item `appendix_alias` lacks semantic_contract"
                    in message
                    for message in contract_messages
                ),
                contract_messages,
            )

            unclaimed = copy.deepcopy(payload)
            unclaimed_alias = unclaimed["items"]["appendix_alias"]
            assert isinstance(unclaimed_alias, dict)
            unclaimed_alias["claim_bearing"] = False
            map_path.write_text(json.dumps(unclaimed), encoding="utf-8")
            strict_messages = [
                finding.message
                for finding in integrity.source_spec_correspondence_inventory_findings(
                    paper, "formalized"
                )
            ]
            self.assertFalse(
                any(
                    "items.appendix_alias: v11 requires claim_bearing: true"
                    in message
                    for message in strict_messages
                ),
                strict_messages,
            )

            malformed = copy.deepcopy(payload)
            malformed_alias = malformed["items"]["appendix_alias"]
            assert isinstance(malformed_alias, dict)
            malformed_alias["lean_declarations"] = ["Fixture.Proof"]
            map_path.write_text(json.dumps(malformed), encoding="utf-8")

            self.assertEqual(
                integrity.validated_presentation_alias_contract_exemptions(
                    paper, malformed
                ),
                {},
            )
            strict_messages = [
                finding.message
                for finding in integrity.source_spec_correspondence_inventory_findings(
                    paper, "formalized"
                )
            ]
            contract_messages = [
                finding.message
                for finding in integrity.semantic_contract_inventory_findings(
                    paper, "formalized"
                )
            ]
            self.assertTrue(
                any(
                    "items.appendix_alias: v11 requires an exact semantic_contract"
                    in message
                    for message in strict_messages
                ),
                strict_messages,
            )
            self.assertTrue(
                any(
                    "claim-bearing source item `appendix_alias` lacks semantic_contract"
                    in message
                    for message in contract_messages
                ),
                contract_messages,
            )

    def test_atom_identity_ignores_source_and_lean_navigation_renames(self) -> None:
        first = source_atom(atom_id="old_id", route="Old.Namespace.Proof")
        second = source_atom(atom_id="new_id", route="New.Namespace.Proof")
        self.assertEqual(
            integrity.source_claim_atom_semantic_sha256(first),
            integrity.source_claim_atom_semantic_sha256(second),
        )
        self.assertEqual(
            integrity.source_claim_atoms_semantic_sha256([first]),
            integrity.source_claim_atoms_semantic_sha256([second]),
        )

    def test_strict_lane_allows_a_transparent_atomic_predicate_surface(self) -> None:
        declaration = repository.LeanDeclaration(
            path=Path("PaperInterface.lean"),
            line=1,
            kind="def",
            name="AtomicSpec",
            source=(
                "def AtomicSpec (input : Nat) : Prop := "
                "sourceFacingPredicate input"
            ),
        )
        legacy_error = repository.semantic_contract_spec_structure_error(
            {}, declaration
        )
        strict_error = repository.semantic_contract_spec_structure_error(
            {}, declaration, require_visible_syntax=False
        )
        self.assertIn("no visible logical/mathematical structure", legacy_error)
        self.assertEqual(strict_error, "")

    def test_strict_lane_uses_lean_closure_for_tactic_bodied_prop_definition(self) -> None:
        declaration = repository.LeanDeclaration(
            path=Path("PaperInterface.lean"),
            line=1,
            kind="def",
            name="QuantifiedSpec",
            source=(
                "def QuantifiedSpec : Prop := by\n"
                "  exact forall input : Nat, input = input"
            ),
        )
        legacy_error = repository.semantic_contract_spec_structure_error(
            {}, declaration
        )
        strict_error = repository.semantic_contract_spec_structure_error(
            {}, declaration, require_visible_syntax=False
        )
        self.assertIn("must state a proposition", legacy_error)
        self.assertEqual(strict_error, "")

    def test_named_argument_in_binder_does_not_truncate_prop_signature(self) -> None:
        declaration = repository.LeanDeclaration(
            path=Path("PaperInterface.lean"),
            line=1,
            kind="def",
            name="ProbabilitySpec",
            source=(
                "def ProbabilitySpec {m : Nat} "
                "(h : 0 < ((Finset.univ (α := Fin m)).card : Nat)) : Prop := "
                "h = h"
            ),
        )
        self.assertEqual(
            repository.declaration_result_type_text(declaration.source), "Prop"
        )
        self.assertEqual(
            repository.semantic_contract_spec_structure_error({}, declaration), ""
        )

    def test_missing_correspondence_is_a_strict_lane_failure(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            paper = Path(temporary) / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            payload = {
                "source_claim_atoms_schema": 1,
                "source_spec_correspondence_schema": 1,
                "semantic_contract_schema": 1,
                "items": {"renamed_source_row": source_item()},
            }
            (audit / "paper_statement_map.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            findings = integrity.source_spec_correspondence_inventory_findings(
                paper, "formalized"
            )
        self.assertTrue(
            any("requires source_spec_correspondence" in finding.message for finding in findings)
        )

    def test_future_closeout_requirement_rejects_a_legacy_map_without_reissuing_it(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            paper = Path(temporary) / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            (paper / "status.json").write_text(
                json.dumps(
                    {
                        "status": "formalized",
                        "review_surface": {
                            "require_source_spec_correspondence": True,
                        },
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            findings = integrity.source_spec_correspondence_inventory_findings(
                paper, "formalized"
            )
        self.assertTrue(
            any("requires source_spec_correspondence_schema" in finding.message for finding in findings)
        )

    def test_strict_lane_cannot_omit_an_inventoried_source_result_from_contracts(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            paper = Path(temporary) / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            payload = {
                "source_claim_atoms_schema": 1,
                "source_spec_correspondence_schema": 1,
                "items": {
                    # The source-inventory classification selects the required
                    # target. `claim_bearing` is a receipt requirement, not a
                    # way to remove an actual named source theorem from v11.
                    "arbitrary_navigation_key": {
                        "source_kind": "theorem",
                        "source_location": "source.txt:1",
                        "statement": "Theorem 1. A named source theorem.",
                        "claim_bearing": False,
                    }
                },
            }
            (audit / "paper_statement_map.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            findings = integrity.source_spec_correspondence_inventory_findings(
                paper, "formalized"
            )
        messages = [finding.message for finding in findings]
        self.assertTrue(
            any("requires claim_bearing: true for every in-scope named source claim" in message for message in messages),
            messages,
        )
        self.assertTrue(
            any("requires an exact semantic_contract for every in-scope named source claim" in message for message in messages),
            messages,
        )

    def test_strict_correspondence_uses_semantic_proof_scope(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            paper = Path(temporary) / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            map_path = audit / "paper_statement_map.json"

            def messages_for(
                mode: str,
                *,
                title: str | None = None,
                corrected: bool = False,
                legacy_corrected: bool = False,
                excluded: bool = False,
                owns_correspondence: bool = False,
                source_kind: str = "claim",
            ) -> list[str]:
                item: dict[str, object] = {
                    "source_kind": source_kind,
                    "claim_bearing": True,
                    "statement": (
                        "The proof records an intermediate inequality before the "
                        "named result."
                    ),
                }
                if title is not None:
                    item["title"] = title
                if corrected:
                    item["coverage_status"] = "corrected_source_statement"
                if legacy_corrected:
                    item["source_status"] = "corrected_source_statement"
                if excluded:
                    item["user_approved_scope_exclusion"] = {
                        "schema": 1,
                        "approval_kind": "explicit_user_instruction",
                    }
                if owns_correspondence:
                    item["source_spec_correspondence"] = {}
                map_path.write_text(
                    json.dumps(
                        {
                            "source_coverage_mode": mode,
                            "source_claim_atoms_schema": 1,
                            "source_spec_correspondence_schema": 1,
                            "items": {"opaque_navigation_key": item},
                        }
                    ),
                    encoding="utf-8",
                )
                return [
                    finding.message
                    for finding in integrity.source_spec_correspondence_inventory_findings(
                        paper, "formalized"
                    )
                ]

            ordinary = messages_for("named_theoretical_statements")
            self.assertFalse(
                any("requires an exact semantic_contract" in message for message in ordinary),
                ordinary,
            )
            self.assertFalse(
                any("requires at least one" in message for message in ordinary),
                ordinary,
            )

            deep = messages_for("deep_paper_with_all_prose_claims")
            self.assertTrue(
                any("requires an exact semantic_contract" in message for message in deep),
                deep,
            )

            named = messages_for(
                "named_theoretical_statements",
                title="Claim 8. Intermediate inequality",
            )
            self.assertTrue(
                any("requires an exact semantic_contract" in message for message in named),
                named,
            )

            corrected = messages_for("named_theoretical_statements", corrected=True)
            self.assertTrue(
                any("requires an exact semantic_contract" in message for message in corrected),
                corrected,
            )

            legacy_corrected = messages_for(
                "named_theoretical_statements", legacy_corrected=True
            )
            self.assertTrue(
                any(
                    "requires an exact semantic_contract" in message
                    for message in legacy_corrected
                ),
                legacy_corrected,
            )

            excluded = messages_for(
                "deep_paper_with_all_prose_claims",
                excluded=True,
                source_kind="example",
            )
            self.assertFalse(
                any("requires an exact semantic_contract" in message for message in excluded),
                excluded,
            )

            excluded_record = messages_for(
                "deep_paper_with_all_prose_claims",
                excluded=True,
                owns_correspondence=True,
                source_kind="example",
            )
            self.assertTrue(
                any("active semantic proof scope" in message for message in excluded_record),
                excluded_record,
            )

    def test_each_current_atom_requires_its_own_bridge_row(self) -> None:
        item = source_item()
        second = source_atom(atom_id="second", route="Fixture.Other")
        second["source_locator"] = "source.txt:2"
        second["semantic_claim"] = "The same conclusion also holds for the explicitly stated boundary case."
        item["source_claim_atoms"] = [item["source_claim_atoms"][0], second]
        current = closure()
        record = correspondence(item, current)
        record["item_identity_sha256"] = integrity.source_spec_correspondence_item_identity_sha256(
            item["semantic_contract"], record
        )
        errors = integrity.source_spec_correspondence_validation_errors(
            record,
            raw_atoms=item["source_claim_atoms"],
            raw_contract=item["semantic_contract"],
        )
        self.assertTrue(any("cover every current source claim atom" in error for error in errors))

    def test_runtime_rejects_a_component_absent_from_the_current_surface(self) -> None:
        item = source_item()
        current = closure()
        record = correspondence(item, current)
        record["source_atom_bindings"][0]["spec_component_sha256s"] = [digest("bogus")]
        record["item_identity_sha256"] = integrity.source_spec_correspondence_item_identity_sha256(
            item["semantic_contract"], record
        )
        item["source_spec_correspondence"] = record
        errors = repository.source_spec_correspondence_runtime_errors(item, current)
        self.assertTrue(any("absent from the current canonical surface" in error for error in errors))

    def test_current_atom_to_surface_receipt_is_accepted_without_name_credit(self) -> None:
        item = source_item()
        current = closure()
        item["source_spec_correspondence"] = correspondence(item, current)
        self.assertEqual(
            repository.source_spec_correspondence_runtime_errors(item, current), []
        )

    def test_runtime_rejects_stale_closure_hash(self) -> None:
        item = source_item()
        current = closure()
        item["source_spec_correspondence"] = correspondence(item, current)
        stale = copy.deepcopy(current)
        stale["sha256"] = digest("changed closure")
        errors = repository.source_spec_correspondence_runtime_errors(item, stale)
        self.assertTrue(any("spec_closure_sha256 is stale" in error for error in errors))

    def test_workspace_terminal_requires_an_explicit_pinned_basis(self) -> None:
        workspace_node: dict[str, object] = {
            "structural_path": "body/fn",
            "node_role": "terminal",
            "origin_class": "workspace",
            "canonical_identity": {"tag": "declaration", "declaration_type_hash": "7"},
            "pinned_declaration_identity_sha256": digest("workspace terminal"),
        }
        current = closure(
            nodes=[workspace_node],
            failures=[
                {
                    "tag": "unregistered_workspace_dependency",
                    "declaration": "Some.Workspace.Primitive",
                }
            ],
        )
        item = source_item()
        item["source_spec_correspondence"] = correspondence(item, current)
        errors = repository.source_spec_correspondence_runtime_errors(item, current)
        self.assertTrue(any("lack a source-contract disposition" in error for error in errors))

    def test_proof_projection_nodes_are_machine_owned(self) -> None:
        proof_projection: dict[str, object] = {
            "structural_path": "body/arg",
            "node_role": "proof_projection",
            "origin_class": "paper",
            "canonical_identity": {
                "tag": "declaration",
                "declaration_kind": "theorem",
                "declaration_type_hash": "11",
            },
        }
        current = closure(nodes=[proof_projection])
        item = source_item()
        item["source_spec_correspondence"] = correspondence(item, current)

        self.assertEqual(
            repository.source_spec_correspondence_runtime_errors(item, current), []
        )

    def test_expanded_recursive_data_nodes_are_machine_owned(self) -> None:
        # Lean emits this role only after it has entered a paper-owned
        # inductive/constructor expansion.  Requiring a separate source row
        # would duplicate the already checked recursive data edge.
        recursive_data: dict[str, object] = {
            "structural_path": "body/constructor/field/recursive",
            "node_role": "recursive_data_terminal",
            "origin_class": "paper",
            "canonical_identity": {
                "tag": "inductive",
                "declaration_kind": "inductive",
                "declaration_type_hash": "17",
            },
        }
        current = closure(nodes=[recursive_data])
        item = source_item()
        item["source_spec_correspondence"] = correspondence(item, current)

        self.assertEqual(
            repository.source_spec_correspondence_runtime_errors(item, current), []
        )

    def test_unsafe_paper_terminal_failures_remain_rejected_after_projection(self) -> None:
        for failure_tag in (
            "opaque_local_dependency",
            "theorem_local_dependency",
            "axiom_local_dependency",
        ):
            with self.subTest(failure_tag=failure_tag):
                paper_terminal: dict[str, object] = {
                    "structural_path": "body",
                    "node_role": "terminal",
                    "origin_class": "paper",
                    "canonical_identity": {
                        "tag": "declaration",
                        "declaration_kind": failure_tag.split("_", 1)[0],
                        "declaration_type_hash": "23",
                    },
                }
                current = closure(
                    nodes=[paper_terminal],
                    failures=[
                        {"tag": failure_tag, "declaration": "Fixture.Hidden"}
                    ],
                )
                item = source_item()
                item["source_spec_correspondence"] = correspondence(item, current)

                errors = repository.source_spec_correspondence_runtime_errors(
                    item, current
                )
                self.assertTrue(
                    any("non-resolvable semantic dependency failure" in error for error in errors)
                )

    def test_structural_rename_preserves_component_and_item_reuse_identity(self) -> None:
        first_node: dict[str, object] = {
            "structural_path": "body/fn",
            "node_role": "terminal",
            "origin_class": "paper",
            "declaration": "Fixture.OldHelper",
            "canonical_identity": {"tag": "definition", "declaration_type_hash": "9"},
        }
        second_node = dict(first_node)
        second_node["declaration"] = "Renamed.Helper"
        self.assertEqual(
            repository.semantic_contract_closure_node_component_sha256(first_node),
            repository.semantic_contract_closure_node_component_sha256(second_node),
        )

        first_item = source_item(atom=source_atom(atom_id="source_old", route="Old.Proof"))
        second_item = source_item(atom=source_atom(atom_id="source_new", route="New.Proof"))
        second_item["semantic_contract"] = {
            "spec_declaration": "New.SourceSpec",
            "evidence_declaration": "New.Proof",
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        }
        current = closure()
        first_record = correspondence(first_item, current)
        second_record = correspondence(second_item, current)
        self.assertEqual(
            first_record["item_identity_sha256"], second_record["item_identity_sha256"]
        )


if __name__ == "__main__":
    unittest.main()
