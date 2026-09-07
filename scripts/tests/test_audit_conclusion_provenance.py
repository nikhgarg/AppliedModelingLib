#!/usr/bin/env python3
"""Focused regressions for semantic conclusion-provenance classification."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from typing import Mapping
from unittest.mock import patch

from scripts import evidence_run_context as EVIDENCE_CONTEXT

from scripts import audit_evidence_integrity as EVIDENCE


ROOT = Path(__file__).resolve().parents[2]
GATE_PATH = ROOT / "scripts" / "audit_conclusion_provenance.py"
SPEC = importlib.util.spec_from_file_location("econcs_conclusion_gate_tests", GATE_PATH)
assert SPEC is not None and SPEC.loader is not None
GATE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GATE
SPEC.loader.exec_module(GATE)


def model_record_item(
    *,
    record: str = "Fixture.ModelCarrier",
    row: str = "reviewed_row",
    binder: str = "input_data",
    relation: str = "",
    source_antecedent_eligible: bool = True,
) -> dict[str, object]:
    return {
        "row": row,
        "binder": binder,
        "judgment_key": f"{row}.{binder} : {record}",
        "kind": "record_conclusion_input",
        "record": record,
        "conclusion_fields": [
            {
                "judgment_key": f"{record}.semantic_constraint",
                "source_antecedent_eligible": source_antecedent_eligible,
                "relation_to_row_result": relation,
                "semantic_kind": "proposition",
            }
        ],
        "valid_constructors": [],
        "conditional_constructors": [],
        "rejected_constructors": [],
    }


def multi_surface_audit_payload(key: str) -> dict[str, object]:
    boundary_digest = "a" * 64
    conclusion_digest = "b" * 64
    digest_schema = GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA

    def item(kind: str, digest: str, marker: str) -> dict[str, object]:
        return {
            "judgment_key": key,
            "kind": kind,
            "source_record_item_digest_schema": digest_schema,
            "source_record_item_semantic_id": marker * 64,
            "source_record_item_context_sha256": ("c" if marker == "a" else "d") * 64,
            "source_record_item_sha256": digest,
            "reviewed_elaborated_signature_identities": [
                {
                    "qualified_declaration": "Fixture.PaperInterface.reviewed_row",
                    "elaborated_signature_sha256": ("e" if marker == "a" else "f") * 64,
                }
            ],
            "source_record_item_reuse_eligibility": {
                "eligible": True,
                "blockers": [],
            },
        }

    return {
        "prompt_version": "fixture-prompt",
        "source_record_audit_sha256": "current-aggregate-receipt",
        "boundary_input_items": [
            item("semantic_proposition_premise", boundary_digest, "a")
        ],
        "conclusion_dependency_items": [
            item("aliased_conclusion_bridge_input", conclusion_digest, "b")
        ],
    }


def multi_surface_judgment() -> dict[str, object]:
    digest_schema = GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    return {
        "classification": "validated_source_assumption",
        "validator": "fixture semantic reviewer",
        "validated_at": "2026-07-26T12:00:00Z",
        "prompt_version": "fixture-prompt",
        # Deliberately stale: this test exercises item-local reuse after an
        # unrelated aggregate source-record receipt refresh.
        "source_record_audit_sha256": "prior-aggregate-receipt",
        "source_record_item_sha256s": [
            {
                "kind": "semantic_proposition_premise",
                "source_record_item_digest_schema": digest_schema,
                "source_record_item_sha256": "a" * 64,
            },
            {
                "kind": "aliased_conclusion_bridge_input",
                "source_record_item_digest_schema": digest_schema,
                "source_record_item_sha256": "b" * 64,
            },
        ],
        "source_location": "source.tex:10",
    }


def fixture_sha256(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def issued_current_fixture_snapshot(
    payload: Mapping[str, object],
    *,
    source_path: Path | None = None,
    paper_statement_map_sha256: str = "",
    current_judgments: Mapping[str, dict[str, object]] | None = None,
) -> object:
    """Issue current, exact-object-bound evidence for conclusion-only tests."""

    current_payload = {
        **payload,
        "paper": "Fixture",
        "prompt_version": GATE.SOURCE_RECORD_PROMPT_VERSION,
    }
    raw = (
        source_path.read_bytes()
        if source_path is not None
        else json.dumps(current_payload, sort_keys=True).encode("utf-8")
    )
    parsed = GATE.source_record_audit_snapshot_from_bytes(
        "Fixture",
        raw,
        source_path=source_path,
    )
    assert parsed is not None
    return GATE._issued_source_record_audit_snapshot(
        paper="Fixture",
        payload=parsed.payload,
        source_file_sha256=parsed.source_file_sha256,
        source_path=parsed.source_path,
        paper_statement_map_sha256=paper_statement_map_sha256,
        current_judgments_override=current_judgments,
        identity_validated=True,
        payload_is_immutable=True,
    )


def corrected_bridge_item(
    *,
    row: str,
    declaration: str,
    key: str,
    digest_seed: str,
) -> dict[str, object]:
    return {
        "row": row,
        "qualified_declaration": declaration,
        "judgment_key": key,
        "reviewed_declaration_identity": {
            "qualified_declaration": declaration,
            "declaration_sha256": fixture_sha256(digest_seed + " declaration"),
        },
        "source_record_item_digest_schema": GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        "source_record_item_semantic_id": fixture_sha256(digest_seed + " semantic"),
        "source_record_item_context_sha256": fixture_sha256(digest_seed + " context"),
        "source_record_item_sha256": fixture_sha256(digest_seed + " item"),
        "reviewed_elaborated_signature_identities": [
            {
                "qualified_declaration": declaration,
                "elaborated_signature_sha256": fixture_sha256(
                    digest_seed + " elaborated"
                ),
            }
        ],
        "source_record_item_reuse_eligibility": {
            "eligible": True,
            "blockers": [],
        },
    }


def transparent_subtype_domain_item(
    *,
    declaration: str = "Fixture.PaperInterface.restricted_row",
    context_declaration: str | None = None,
    context_signature_seed: str = "signature",
    predicate_relation: str = "",
    blocked_routes: list[dict[str, object]] | None = None,
    predicate_result_bridges: list[dict[str, object]] | None = None,
) -> dict[str, object]:
    """Build one fully pinned restricted-subtype data item for gate tests."""

    key = "restricted_row.p : OrderedPair n"
    declaration_sha = fixture_sha256("restricted declaration")
    signature_sha = fixture_sha256("signature")
    context_declaration = context_declaration or declaration
    context_signature_sha = fixture_sha256(context_signature_seed)
    source_identity = {
        "source_key": "source appendix pair scope",
        "source_map_item_sha256": fixture_sha256("source map item"),
        "source_semantic_sha256": fixture_sha256("source semantic item"),
    }
    reviewed_identity = {
        "qualified_declaration": declaration,
        "declaration_sha256": declaration_sha,
    }
    signature = {
        "qualified_declaration": declaration,
        "elaborated_signature_sha256": signature_sha,
    }
    association = {
        "reviewed_declaration_identity": reviewed_identity,
        "source_item_identities": [source_identity],
        "reviewed_elaborated_signature_identity": signature,
        "semantic_association_sha256": fixture_sha256("semantic association"),
    }
    context_association = {
        "reviewed_declaration_identity": {
            "qualified_declaration": context_declaration,
            "declaration_sha256": declaration_sha,
        },
        "source_item_identities": [source_identity],
        "reviewed_elaborated_signature_identity": {
            "qualified_declaration": context_declaration,
            "elaborated_signature_sha256": context_signature_sha,
        },
        "semantic_association_sha256": fixture_sha256("semantic association"),
    }
    return {
        "row": "restricted_row",
        "binder": "p",
        "judgment_key": key,
        "kind": "transparent_subtype_domain_input",
        "conclusion_fields": [],
        "valid_constructors": [],
        "conditional_constructors": [],
        "rejected_constructors": [],
        "domain_data_only": True,
        "subtype_domain_semantic_data_only": True,
        "subtype_expansion_complete": True,
        "subtype_carrier_is_definitely_data": True,
        "subtype_predicate_result_relation": predicate_relation,
        "subtype_predicate_record_dependencies": [],
        "subtype_carrier_record_dependencies": [],
        "subtype_predicate_record_binder_dependencies": [],
        "subtype_predicate_result_bridges": predicate_result_bridges or [],
        "subtype_predicate_proposition_alias_expansion": {
            "expanded_type": "lo.val < hi.val",
            "transparent_steps": [],
            "blocked_routes": blocked_routes or [],
        },
        "reviewed_declaration_identity": reviewed_identity,
        "reviewed_elaborated_signature_identities": [signature],
        "source_contract_association": association,
        "subtype_domain_source_context": {
            "schema": 1,
            "required_kind": "restricted_subtype_domain",
            "status": "satisfied",
            "association": context_association,
            "selected_contexts": [
                {
                    "source_semantic_sha256": source_identity[
                        "source_semantic_sha256"
                    ],
                    "context_sha256": fixture_sha256("source context"),
                    "semantic_context_sha256": fixture_sha256(
                        "semantic source context"
                    ),
                    "kind": "restricted_subtype_domain",
                    "source_location": "source.tex:10",
                    "source_anchor_evidence": [{"path": "source.tex"}],
                }
            ],
            "failure_reasons": [],
        },
        "source_record_item_digest_schema": GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        "source_record_item_semantic_id": fixture_sha256("subtype semantic"),
        "source_record_item_context_sha256": fixture_sha256("subtype context"),
        "source_record_item_sha256": fixture_sha256("subtype item"),
        "source_record_item_reuse_eligibility": {
            "eligible": True,
            "blockers": [],
        },
    }


def corrected_bridge_field(
    *,
    key: str,
    model_spec: str,
    declaration: str,
) -> dict[str, object]:
    item = corrected_bridge_item(
        row="corrected_target",
        declaration=declaration,
        key=key,
        digest_seed=key,
    )
    item["path"] = f"{model_spec} -> {model_spec}.approved_field"
    return item


class CorrectedModelConclusionBridgeTests(unittest.TestCase):
    """The corrected-target route is exact, current, and never paper-wide."""

    paper = "Fixture"
    row = "corrected_target"
    declaration = "Fixture.PaperInterface.corrected_target"
    semantic_key = "semantic-model::corrected_target"
    assumption_row = "approved_assumption"
    assumption_declaration = "Fixture.approved_assumption"
    assumption_key = "semantic-model::approved_assumption"
    model_spec = "Fixture.CorrectedModel"
    field_key = "Fixture.CorrectedModel.approved_field"
    audit_digest = fixture_sha256("bridge aggregate receipt")
    raw_integrity_digest = fixture_sha256("bridge raw receipt")
    scope_digest = fixture_sha256("bridge scope receipt")
    approval_digest = fixture_sha256("bridge approval")
    archive_digest = fixture_sha256("bridge archive")
    correction_id = "FIXTURE-CORR-1"

    def test_graph_native_realization_receipt_needs_no_persisted_correspondence(
        self,
    ) -> None:
        atoms = [
            {
                "id": "source_clause",
                "source_locator": "source.tex:10",
                "semantic_claim": "Every feasible input has the stated outcome.",
                "reviewed_lean_route": "Fixture.claim_proof",
                "source_quote_sha256": fixture_sha256("verbatim source clause"),
            }
        ]
        contract = {
            "spec_declaration": "Fixture.claimSpec",
            "evidence_declaration": "Fixture.claim_proof",
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        }
        receipt_fields = {
            "source_atoms_sha256": GATE.source_claim_atoms_semantic_sha256(atoms),
            "spec_closure_sha256": fixture_sha256("semantic closure"),
            "spec_surface_sha256": fixture_sha256("expanded Spec surface"),
            "closure_environment_sha256": fixture_sha256("Lean graph environment"),
        }
        receipt = GATE.StrictSourceSpecCorrespondenceReceipt(
            source_item_key="source_claim",
            spec_declaration="Fixture.claimSpec",
            evidence_declaration="Fixture.claim_proof",
            evidence_mode="proves",
            semantic_shape="plain",
            item_identity_sha256=(
                GATE.graph_native_source_spec_realization_identity_sha256(
                    contract,
                    **receipt_fields,
                )
            ),
            authority="v11_graph_native_v1",
            **receipt_fields,
        )
        item = {
            "claim_bearing": True,
            "semantic_contract": contract,
            "source_claim_atoms": atoms,
        }

        self.assertTrue(GATE._strict_source_spec_runtime_matches_item(item, receipt))
        self.assertNotIn("source_spec_correspondence", item)
        changed = json.loads(json.dumps(item))
        changed["source_claim_atoms"][0]["semantic_claim"] = "A changed claim."
        self.assertFalse(
            GATE._strict_source_spec_runtime_matches_item(changed, receipt)
        )

    def _payload(self) -> dict[str, object]:
        semantic_item = corrected_bridge_item(
            row=self.row,
            declaration=self.declaration,
            key=self.semantic_key,
            digest_seed="bridge semantic item",
        )
        assumption_item = corrected_bridge_item(
            row=self.assumption_row,
            declaration=self.assumption_declaration,
            key=self.assumption_key,
            digest_seed="bridge assumption item",
        )
        field = corrected_bridge_field(
            key=self.field_key,
            model_spec=self.model_spec,
            declaration=self.declaration,
        )
        semantic_item["expanded_lean_surface"] = {
            "record_field_types": [
                {"path": f"{self.model_spec} -> {self.field_key}"}
            ]
        }
        return {
            "paper": self.paper,
            "prompt_version": GATE.SOURCE_RECORD_PROMPT_VERSION,
            "source_record_audit_sha256": self.audit_digest,
            "source_record_audit_integrity_sha256": self.raw_integrity_digest,
            "formalization_scope": {
                "kind": "author_approved_corrected_model",
                "scope_id": "fixture-corrected-scope",
                "approval_artifact_sha256": self.approval_digest,
                "base_archive_sha256": self.archive_digest,
                "model_spec_declaration": self.model_spec,
                "target_result_declarations": [self.declaration],
                "correction_ids": [self.correction_id],
                "archival_equivalence_claimed": False,
                "scope_sha256": self.scope_digest,
            },
            "expected_semantic_model_judgment_keys": [
                self.semantic_key,
                self.assumption_key,
            ],
            "semantic_model_items": [semantic_item, assumption_item],
            "recursive_field_items": [field],
            "missing_configured_review_rows": [],
            "recursion_failures": [],
            "conclusion_dependency_items": [
                {
                    "row": self.row,
                    "binder": "model_input",
                    "kind": "record_conclusion_input",
                    "record": self.model_spec,
                    "reviewed_declaration_identity": dict(
                        semantic_item["reviewed_declaration_identity"]
                    ),
                    "reviewed_elaborated_signature_identities": [
                        dict(signature)
                        for signature in semantic_item[
                            "reviewed_elaborated_signature_identities"
                        ]
                    ],
                    "conclusion_fields": [
                        {
                            "judgment_key": self.field_key,
                            "source_antecedent_eligible": True,
                            "relation_to_row_result": "",
                        }
                    ],
                    "valid_constructors": [],
                    "conditional_constructors": [],
                    "rejected_constructors": [],
                }
            ],
            "reachable_paper_interface_auxiliary_dependencies": [],
            "unresolved_reachable_paper_interface_auxiliaries": [],
            "ambiguous_reachable_paper_interface_auxiliary_references": [],
            "reachable_paper_interface_auxiliary_quarantine_configuration_errors": [],
        }

    def _contract(self, payload: dict[str, object]) -> dict[str, object]:
        semantic_item = payload["semantic_model_items"][0]
        assert isinstance(semantic_item, dict)
        assumption_item = payload["semantic_model_items"][1]
        assert isinstance(assumption_item, dict)
        field = payload["recursive_field_items"][0]
        assert isinstance(field, dict)
        semantic_digest = semantic_item["source_record_item_sha256"]
        field_digest = field["source_record_item_sha256"]
        return {
            "schema": 3,
            "scope_id": "fixture-corrected-scope",
            "model_spec_declaration": self.model_spec,
            "target_result_declarations": [self.declaration],
            "semantic_item_keys": [self.semantic_key, self.assumption_key],
            "source_record_audit_sha256": self.audit_digest,
            "source_record_audit_integrity_sha256": self.raw_integrity_digest,
            "source_record_scope_sha256": self.scope_digest,
            "semantic_item_mappings": [
                {
                    "source_record_item_key": self.semantic_key,
                    "source_record_item_sha256": semantic_digest,
                    "qualified_declaration": self.declaration,
                },
                {
                    "source_record_item_key": self.assumption_key,
                    "source_record_item_sha256": assumption_item[
                        "source_record_item_sha256"
                    ],
                    "qualified_declaration": self.assumption_declaration,
                },
            ],
            "target_result_mappings": [
                {
                    "target_declaration": self.declaration,
                    "source_record_item_key": self.semantic_key,
                    "source_record_item_sha256": semantic_digest,
                }
            ],
            "assumption_mappings": [
                {
                    "assumption_declaration": self.assumption_declaration,
                    "source_record_item_key": self.assumption_key,
                    "source_record_item_sha256": assumption_item[
                        "source_record_item_sha256"
                    ],
                }
            ],
            "model_field_mappings": [
                {
                    "source_record_item_key": self.field_key,
                    "source_record_item_sha256": field_digest,
                }
            ],
        }

    def _status(self, contract_digest: str) -> dict[str, object]:
        return {
            "status": "formalized",
            "review_surface": {
                "include_names": [self.row],
                "assumption_names": [self.assumption_row],
            },
            "formalization_scope": {
                "kind": "author_approved_corrected_model",
                "scope_id": "fixture-corrected-scope",
                "approval": {
                    "artifact_sha256": self.approval_digest,
                },
                "base_archive": {"sha256": self.archive_digest},
                "model_spec_declaration": self.model_spec,
                "target_result_declarations": [self.declaration],
                "correction_ids": [self.correction_id],
                "archival_equivalence_claimed": False,
                "semantic_contract": {
                    "path": "audit/corrected_model_semantic_contract.json",
                    "sha256": contract_digest,
                },
            },
        }

    def _write_fixture(
        self,
        root: Path,
        *,
        contract_mutator: object | None = None,
        payload_mutator: object | None = None,
    ) -> dict[str, object]:
        paper = root / self.paper
        audit = paper / "audit"
        audit.mkdir(parents=True)
        payload = self._payload()
        if callable(payload_mutator):
            payload_mutator(payload)
        contract = self._contract(payload)
        if callable(contract_mutator):
            contract_mutator(contract)
        contract_path = audit / "corrected_model_semantic_contract.json"
        contract_path.write_text(json.dumps(contract, sort_keys=True), encoding="utf-8")
        status = self._status(hashlib.sha256(contract_path.read_bytes()).hexdigest())
        (paper / "status.json").write_text(
            json.dumps(status, sort_keys=True), encoding="utf-8"
        )
        return payload

    def _run_fixture_gate(
        self,
        *,
        current_contract: bool = True,
        contract_mutator: object | None = None,
        payload_mutator: object | None = None,
    ) -> list[object]:
        old_papers = GATE.PAPERS
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            payload = self._write_fixture(
                root,
                contract_mutator=contract_mutator,
                payload_mutator=payload_mutator,
            )

            try:
                GATE.PAPERS = root
                snapshot = issued_current_fixture_snapshot(payload)
                with (
                    patch.object(
                        GATE,
                        "reachable_paper_interface_auxiliary_findings",
                        return_value=[],
                    ),
                    patch.object(
                        GATE,
                        "author_approved_corrected_scope_contract_is_current",
                        return_value=current_contract,
                    ),
                ):
                    return GATE.audit_paper(
                        self.paper,
                        source_record_snapshot=snapshot,
                    )
            finally:
                GATE.PAPERS = old_papers

    def test_exact_current_contract_covers_matching_declaration_and_signature(self) -> None:
        findings = self._run_fixture_gate()

        self.assertEqual(findings, [])

    def test_corrected_bridge_parses_the_frozen_contract_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            payload = self._write_fixture(root)
            folder = root / self.paper
            contract_path = (
                folder / "audit" / "corrected_model_semantic_contract.json"
            )
            exact_contract = contract_path.read_bytes()
            status = json.loads((folder / "status.json").read_bytes())
            # The live replacement is deliberately valid JSON but not the
            # contract whose digest/status were frozen by the transaction.
            contract_path.write_text("{}\n", encoding="utf-8")

            bridge = GATE.corrected_model_conclusion_bridge(
                self.paper,
                payload,
                folder=folder,
                status_payload_override=status,
                corrected_scope_current=True,
                input_raw_bytes_override={
                    contract_path.resolve(): exact_contract,
                },
            )
            missing_snapshot_bridge = GATE.corrected_model_conclusion_bridge(
                self.paper,
                payload,
                folder=folder,
                status_payload_override=status,
                corrected_scope_current=True,
                input_raw_bytes_override={},
            )

        self.assertIsNotNone(bridge)
        self.assertIsNone(missing_snapshot_bridge)

    def test_same_row_with_different_qualified_declaration_is_not_waived(self) -> None:
        def change_dependency_declaration(payload: dict[str, object]) -> None:
            dependencies = payload["conclusion_dependency_items"]
            assert isinstance(dependencies, list)
            dependency = dependencies[0]
            assert isinstance(dependency, dict)
            identity = dependency["reviewed_declaration_identity"]
            assert isinstance(identity, dict)
            identity["qualified_declaration"] = "Fixture.PaperInterface.other_row"
            signatures = dependency["reviewed_elaborated_signature_identities"]
            assert isinstance(signatures, list)
            signatures[0]["qualified_declaration"] = "Fixture.PaperInterface.other_row"

        findings = self._run_fixture_gate(
            payload_mutator=change_dependency_declaration
        )

        self.assertEqual(len(findings), 1)
        self.assertIn("source-model record has no current exact source provenance", findings[0].message)

    def test_same_declaration_with_different_elaborated_signature_is_not_waived(self) -> None:
        def change_dependency_signature(payload: dict[str, object]) -> None:
            dependencies = payload["conclusion_dependency_items"]
            assert isinstance(dependencies, list)
            dependency = dependencies[0]
            assert isinstance(dependency, dict)
            signatures = dependency["reviewed_elaborated_signature_identities"]
            assert isinstance(signatures, list)
            signatures[0]["elaborated_signature_sha256"] = fixture_sha256(
                "different elaborated signature"
            )

        findings = self._run_fixture_gate(payload_mutator=change_dependency_signature)

        self.assertEqual(len(findings), 1)
        self.assertIn("source-model record has no current exact source provenance", findings[0].message)

    def test_unexpanded_local_input_is_not_waived_by_its_enclosing_row(self) -> None:
        def add_unexpanded_local_input(payload: dict[str, object]) -> None:
            dependencies = payload["conclusion_dependency_items"]
            assert isinstance(dependencies, list)
            dependencies.append(
                {
                    "row": self.row,
                    "binder": "p",
                    "kind": "unexpanded_local_reducible_type_input",
                    "conclusion_fields": [],
                    "valid_constructors": [],
                    "conditional_constructors": [],
                    "rejected_constructors": [],
                }
            )

        findings = self._run_fixture_gate(payload_mutator=add_unexpanded_local_input)

        self.assertEqual(len(findings), 1)
        self.assertIn("no paper-local constructor", findings[0].message)

    def test_stale_contract_receipt_does_not_suppress_a_dependency(self) -> None:
        def stale(contract: dict[str, object]) -> None:
            contract["source_record_audit_sha256"] = fixture_sha256("stale receipt")

        findings = self._run_fixture_gate(contract_mutator=stale)

        self.assertEqual(len(findings), 1)
        self.assertIn("source-model record has no current exact source provenance", findings[0].message)

    def test_incomplete_model_field_mapping_does_not_suppress_a_dependency(self) -> None:
        def incomplete(contract: dict[str, object]) -> None:
            contract["model_field_mappings"] = []

        findings = self._run_fixture_gate(contract_mutator=incomplete)

        self.assertEqual(len(findings), 1)
        self.assertIn("source-model record has no current exact source provenance", findings[0].message)

    def test_omitted_transitively_reachable_nested_field_does_not_suppress(self) -> None:
        nested_record_field = "Fixture.CorrectedModel.nested_model"
        nested_field = "Fixture.NestedModel.strict_condition"

        def add_nested_graph(payload: dict[str, object]) -> None:
            fields = payload["recursive_field_items"]
            semantic_items = payload["semantic_model_items"]
            assert isinstance(fields, list)
            assert isinstance(semantic_items, list)
            parent = corrected_bridge_field(
                key=nested_record_field,
                model_spec=self.model_spec,
                declaration=self.declaration,
            )
            child = corrected_bridge_item(
                row="nested_source_row",
                declaration="Fixture.NestedModel.strict_condition",
                key=nested_field,
                digest_seed=nested_field,
            )
            child["path"] = f"Fixture.NestedModel -> {nested_field}"
            fields.extend([parent, child])
            target_item = semantic_items[0]
            assert isinstance(target_item, dict)
            surface = target_item["expanded_lean_surface"]
            assert isinstance(surface, dict)
            record_fields = surface["record_field_types"]
            assert isinstance(record_fields, list)
            record_fields.extend(
                [
                    {"path": f"{self.model_spec} -> {nested_record_field}"},
                    {
                        "path": (
                            f"{self.model_spec} -> {nested_record_field} -> {nested_field}"
                        )
                    },
                ]
            )

        def map_only_parent(contract: dict[str, object]) -> None:
            mappings = contract["model_field_mappings"]
            assert isinstance(mappings, list)
            mappings.append(
                {
                    "source_record_item_key": nested_record_field,
                    "source_record_item_sha256": fixture_sha256(
                        nested_record_field + " item"
                    ),
                }
            )

        findings = self._run_fixture_gate(
            payload_mutator=add_nested_graph,
            contract_mutator=map_only_parent,
        )

        self.assertEqual(len(findings), 1)
        self.assertIn("source-model record has no current exact source provenance", findings[0].message)

    def test_incomplete_assumption_mapping_does_not_suppress_a_dependency(self) -> None:
        def incomplete(contract: dict[str, object]) -> None:
            contract["assumption_mappings"] = []

        findings = self._run_fixture_gate(contract_mutator=incomplete)

        self.assertEqual(len(findings), 1)
        self.assertIn("source-model record has no current exact source provenance", findings[0].message)

    def test_incomplete_target_mapping_does_not_suppress_a_dependency(self) -> None:
        def incomplete(contract: dict[str, object]) -> None:
            contract["target_result_mappings"] = []

        findings = self._run_fixture_gate(contract_mutator=incomplete)

        self.assertEqual(len(findings), 1)
        self.assertIn("source-model record has no current exact source provenance", findings[0].message)

    def test_unrelated_recursive_field_does_not_inherit_governing_model_coverage(self) -> None:
        unrelated_key = "Fixture.UnrelatedModel.unreviewed_field"

        def add_unrelated_field(payload: dict[str, object]) -> None:
            fields = payload["recursive_field_items"]
            dependencies = payload["conclusion_dependency_items"]
            assert isinstance(fields, list)
            assert isinstance(dependencies, list)
            unrelated = corrected_bridge_item(
                row="unrelated_row",
                declaration="Fixture.PaperInterface.unrelated_row",
                key=unrelated_key,
                digest_seed="unrelated field",
            )
            unrelated["path"] = (
                "Fixture.UnrelatedModel -> Fixture.UnrelatedModel.unreviewed_field"
            )
            fields.append(unrelated)
            dependency = dependencies[0]
            assert isinstance(dependency, dict)
            conclusion_fields = dependency["conclusion_fields"]
            assert isinstance(conclusion_fields, list)
            conclusion_fields.append(
                {
                    "judgment_key": unrelated_key,
                    "source_antecedent_eligible": True,
                    "relation_to_row_result": "",
                }
            )

        findings = self._run_fixture_gate(payload_mutator=add_unrelated_field)

        self.assertEqual(len(findings), 1)
        self.assertIn("source-model record has no current exact source provenance", findings[0].message)

    def test_failed_currentness_and_unmapped_rows_do_not_receive_a_paper_wide_waiver(self) -> None:
        findings = self._run_fixture_gate(current_contract=False)
        self.assertEqual(len(findings), 1)

        def add_unmapped(payload: dict[str, object]) -> None:
            dependencies = payload["conclusion_dependency_items"]
            assert isinstance(dependencies, list)
            dependencies.append(
                {
                    "row": "unmapped_row",
                    "binder": "opaque_input",
                    "kind": "unexpanded_local_reducible_type_input",
                    "conclusion_fields": [],
                    "valid_constructors": [],
                    "conditional_constructors": [],
                    "rejected_constructors": [],
                }
            )

        findings = self._run_fixture_gate(payload_mutator=add_unmapped)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].row, "unmapped_row")


class TransparentSubtypeDomainProvenanceTests(unittest.TestCase):
    def test_exact_current_context_bound_subtype_domain_is_data(self) -> None:
        item = transparent_subtype_domain_item()

        self.assertTrue(
            GATE.conclusion_input_is_accepted_source_antecedent(
                item,
                set(),
                {str(item["judgment_key"])},
            )
        )
        # A restricted subtype is intentionally not accepted merely as an
        # exact proposition antecedent; the data classification is the only
        # route after its source-domain receipt has been checked.
        self.assertFalse(
            GATE.conclusion_input_is_exact_source_antecedent(
                item, {str(item["judgment_key"])}
            )
        )

    def test_context_with_mismatched_fully_qualified_declaration_fails_closed(
        self,
    ) -> None:
        item = transparent_subtype_domain_item(
            context_declaration="Fixture.PaperInterface.other_row"
        )

        self.assertFalse(
            GATE.conclusion_input_is_accepted_source_antecedent(
                item, set(), {str(item["judgment_key"])}
            )
        )

    def test_context_with_mismatched_elaborated_signature_fails_closed(self) -> None:
        item = transparent_subtype_domain_item(
            context_signature_seed="different elaborated signature"
        )

        self.assertFalse(
            GATE.conclusion_input_is_accepted_source_antecedent(
                item, set(), {str(item["judgment_key"])}
            )
        )

    def test_context_with_mismatched_source_item_sha_fails_closed(self) -> None:
        item = transparent_subtype_domain_item()
        context = item["subtype_domain_source_context"]
        assert isinstance(context, dict)
        association = context["association"]
        assert isinstance(association, dict)
        source_identities = association["source_item_identities"]
        assert isinstance(source_identities, list)
        source_identities[0] = {
            **source_identities[0],
            "source_map_item_sha256": fixture_sha256("different source-map item"),
        }

        self.assertFalse(
            GATE.conclusion_input_is_accepted_source_antecedent(
                item, set(), {str(item["judgment_key"])}
            )
        )

    def test_predicate_proof_dependency_bridge_is_not_data(self) -> None:
        item = transparent_subtype_domain_item(
            predicate_result_bridges=[
                {
                    "predicate_pattern": "Seeded _f0",
                    "row_result_pattern": "Delivered _f0",
                    "result_relation": "equivalent",
                    "steps": [
                        {
                            "declaration": "Fixture.step",
                            "input_index": 1,
                            "input_pattern": "Seeded _f0",
                            "result_pattern": "Delivered _f0",
                        }
                    ],
                }
            ]
        )

        self.assertFalse(
            GATE.conclusion_input_is_accepted_source_antecedent(
                item, set(), {str(item["judgment_key"])}
            )
        )

    def test_result_related_or_opaque_subtype_predicate_is_not_data(self) -> None:
        related = transparent_subtype_domain_item(predicate_relation="equivalent")
        opaque = transparent_subtype_domain_item(
            blocked_routes=[
                {
                    "reason": "nontransparent_local_proposition_route",
                    "declaration": "Fixture.hidden",
                }
            ]
        )

        for item in (related, opaque):
            with self.subTest(item=item["subtype_predicate_result_relation"]):
                self.assertFalse(
                    GATE.conclusion_input_is_accepted_source_antecedent(
                        item, set(), {str(item["judgment_key"])}
                    )
                )


class SourceModelDataRecordTests(unittest.TestCase):
    def test_complete_multi_surface_pin_accepts_current_source_antecedent(self) -> None:
        key = "reviewed_row.source_premise : TransparentAlias"
        audit_payload = multi_surface_audit_payload(key)
        judgment = multi_surface_judgment()

        with tempfile.TemporaryDirectory() as tmpdir:
            papers = Path(tmpdir)
            audit = papers / "Fixture" / "audit"
            audit.mkdir(parents=True)
            (audit / "source_record_match_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": "Fixture",
                        "items": {key: judgment},
                    }
                ),
                encoding="utf-8",
            )
            with patch.object(GATE, "PAPERS", papers):
                judgments = GATE.current_judgments("Fixture", audit_payload)

        self.assertIn(key, judgments)
        antecedents = GATE.exact_source_antecedents(judgments)
        self.assertIn(key, antecedents)
        self.assertTrue(
            GATE.conclusion_input_is_exact_source_antecedent(
                {
                    "kind": "aliased_conclusion_bridge_input",
                    "judgment_key": key,
                    "conclusion_fields": [],
                },
                antecedents,
            )
        )

    def test_partial_or_altered_multi_surface_pin_is_not_current(self) -> None:
        key = "reviewed_row.source_premise : TransparentAlias"
        audit_payload = multi_surface_audit_payload(key)
        partial = multi_surface_judgment()
        partial["source_record_item_sha256s"] = partial["source_record_item_sha256s"][:1]
        altered = multi_surface_judgment()
        altered_pins = altered["source_record_item_sha256s"]
        assert isinstance(altered_pins, list)
        altered_pins[1] = {
            **altered_pins[1],
            "kind": "different_generated_semantic_kind",
        }

        with tempfile.TemporaryDirectory() as tmpdir:
            papers = Path(tmpdir)
            audit = papers / "Fixture" / "audit"
            audit.mkdir(parents=True)
            sidecar = audit / "source_record_match_llm.json"
            with patch.object(GATE, "PAPERS", papers):
                for judgment in (partial, altered):
                    sidecar.write_text(
                        json.dumps(
                            {
                                "schema": 1,
                                "paper": "Fixture",
                                "items": {key: judgment},
                            }
                        ),
                        encoding="utf-8",
                    )
                    self.assertNotIn(
                        key,
                        GATE.current_judgments("Fixture", audit_payload),
                    )

    def test_semantic_model_item_reuse_requires_matching_digest_schema(self) -> None:
        key = "semantic-model::reviewed_row"
        digest_schema = GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
        audit_payload = {
            "prompt_version": "fixture-prompt",
            "source_record_audit_sha256": "current-aggregate-receipt",
            "semantic_model_items": [
                {
                    "judgment_key": key,
                    "kind": "semantic_model_comparison",
                    "source_record_item_digest_schema": digest_schema,
                    "source_record_item_semantic_id": "a" * 64,
                    "source_record_item_context_sha256": "b" * 64,
                    "source_record_item_sha256": "c" * 64,
                    "reviewed_elaborated_signature_identities": [
                        {
                            "qualified_declaration": "Fixture.PaperInterface.reviewed_row",
                            "elaborated_signature_sha256": "d" * 64,
                        }
                    ],
                    "source_record_item_reuse_eligibility": {
                        "eligible": True,
                        "blockers": [],
                    },
                }
            ],
        }
        judgment = {
            "classification": "semantic_model_review",
            "validator": "fixture semantic reviewer",
            "validated_at": "2026-07-26T12:00:00Z",
            "prompt_version": "fixture-prompt",
            "source_record_audit_sha256": "prior-aggregate-receipt",
            "source_record_item_digest_schema": digest_schema,
            "source_record_item_sha256": "c" * 64,
        }

        with tempfile.TemporaryDirectory() as tmpdir:
            papers = Path(tmpdir)
            audit = papers / "Fixture" / "audit"
            audit.mkdir(parents=True)
            sidecar = audit / "source_record_match_llm.json"
            with patch.object(GATE, "PAPERS", papers):
                sidecar.write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "paper": "Fixture",
                            "items": {key: judgment},
                        }
                    ),
                    encoding="utf-8",
                )
                self.assertIn(key, GATE.current_judgments("Fixture", audit_payload))

                judgment["source_record_item_digest_schema"] = digest_schema - 1
                sidecar.write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "paper": "Fixture",
                            "items": {key: judgment},
                        }
                    ),
                    encoding="utf-8",
                )
                self.assertNotIn(key, GATE.current_judgments("Fixture", audit_payload))

    def test_nonresult_model_record_is_invariant_under_identifier_renaming(self) -> None:
        original = model_record_item(
            record="Fixture.ModelCarrier", row="source_row", binder="carrier"
        )
        renamed = model_record_item(
            record="Different.Namespace.Unrelated", row="other", binder="payload"
        )

        self.assertTrue(GATE.record_input_is_nonresult_source_model_or_data(original))
        self.assertTrue(GATE.record_input_is_nonresult_source_model_or_data(renamed))

    def test_result_related_or_unclassified_record_field_remains_conclusion_debt(self) -> None:
        self.assertFalse(
            GATE.record_input_is_nonresult_source_model_or_data(
                model_record_item(relation="component_of_target")
            )
        )
        self.assertFalse(
            GATE.record_input_is_nonresult_source_model_or_data(
                model_record_item(source_antecedent_eligible=False)
            )
        )
        self.assertFalse(
            GATE.record_input_is_nonresult_source_model_or_data(
                {
                    "kind": "direct_conclusion_input",
                    "record": "Fixture.ModelCarrier",
                    "conclusion_fields": [],
                }
            )
        )

    def test_gate_requires_current_source_provenance_for_nonresult_model_record(self) -> None:
        payload = {
            "prompt_version": "fixture",
            "source_record_audit_sha256": "fixture-digest",
            "missing_configured_review_rows": [],
            "recursion_failures": [],
            "conclusion_dependency_items": [model_record_item()],
        }

        findings = self._run_gate(payload)

        self.assertEqual(len(findings), 1)
        self.assertIn("source-model record has no current exact source provenance", findings[0].message)

    def test_gate_accepts_nonresult_model_record_with_current_source_fields(self) -> None:
        payload = {
            "prompt_version": "fixture",
            "source_record_audit_sha256": "fixture-digest",
            "missing_configured_review_rows": [],
            "recursion_failures": [],
            "conclusion_dependency_items": [model_record_item()],
        }
        field_key = "Fixture.ModelCarrier.semantic_constraint"

        with patch.object(
            GATE,
            "current_judgments",
            return_value={
                field_key: {
                    "classification": "validated_source_assumption",
                    "source_location": "source.tex:10",
                }
            },
        ):
            findings = self._run_gate(payload)

        self.assertEqual(findings, [])

    def test_gate_still_rejects_record_that_contains_result_component(self) -> None:
        payload = {
            "prompt_version": "fixture",
            "source_record_audit_sha256": "fixture-digest",
            "missing_configured_review_rows": [],
            "recursion_failures": [],
            "conclusion_dependency_items": [
                model_record_item(relation="component_of_target")
            ],
        }

        findings = self._run_gate(payload)

        self.assertEqual(len(findings), 1)
        self.assertIn("no paper-local constructor", findings[0].message)

    def test_strict_occurrence_gate_does_not_repeat_legacy_record_heuristic(
        self,
    ) -> None:
        payload = {
            "prompt_version": "fixture",
            "source_record_audit_sha256": "fixture-digest",
            "missing_configured_review_rows": [],
            "recursion_failures": [],
            "conclusion_dependency_items": [
                {
                    **model_record_item(relation="component_of_target"),
                    "binder": "neutral_proof_premise",
                }
            ],
        }
        old_papers = GATE.PAPERS
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Fixture" / "audit").mkdir(parents=True)
            snapshot = issued_current_fixture_snapshot(payload)

            try:
                GATE.PAPERS = root
                with (
                    patch.object(
                        GATE.subprocess,
                        "run",
                        side_effect=AssertionError(
                            "the conclusion gate must not launch the source-record helper"
                        ),
                    ),
                    patch.object(
                        GATE,
                        "reachable_paper_interface_auxiliary_findings",
                        return_value=[],
                    ),
                    patch.object(
                        GATE,
                        "theorem_realization_contract_active",
                        return_value=True,
                    ),
                    patch.object(
                        GATE,
                        "theorem_realization_component_contract_findings",
                        return_value=[],
                    ),
                    patch.object(
                        GATE,
                        "current_complete_semantic_model_record_bindings",
                        side_effect=AssertionError(
                            "strict v11 must not recompute the v10 record heuristic"
                        ),
                    ),
                ):
                    findings = GATE.audit_paper(
                        "Fixture", source_record_snapshot=snapshot
                    )
            finally:
                GATE.PAPERS = old_papers

        self.assertEqual(findings, [])

    def test_full_closeout_rejects_elaborated_direct_false_route(self) -> None:
        payload = {
            "source_premise_consistency_schema": 1,
            "source_premise_consistency_items": [
                {
                    "reviewed_input_type": "Fixture.ModelCarrier",
                    "direct_eliminators": [
                        {
                            "candidate": "Fixture.any_spelling",
                            "direct_eliminator": True,
                        }
                    ],
                }
            ],
        }
        old_papers = GATE.PAPERS
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            paper_dir = root / "Fixture"
            paper_dir.mkdir()
            (paper_dir / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            try:
                GATE.PAPERS = root
                findings = GATE.source_premise_false_eliminator_findings(
                    "Fixture", payload
                )
            finally:
                GATE.PAPERS = old_papers

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].binder, "Fixture.ModelCarrier")
        self.assertIn("direct route", findings[0].message)

    def test_gate_consumes_explicit_full_surface_without_launching_helper(self) -> None:
        """Conclusion classification consumes caller-issued semantic evidence."""

        payload = {
            "prompt_version": "fixture",
            "source_record_audit_sha256": "fixture-digest",
            "missing_configured_review_rows": [],
            "recursion_failures": [],
            "conclusion_dependency_items": [],
        }
        old_papers = GATE.PAPERS
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Fixture" / "audit").mkdir(parents=True)
            snapshot = issued_current_fixture_snapshot(payload)

            try:
                GATE.PAPERS = root
                with (
                    patch.object(GATE.subprocess, "run") as helper,
                    patch.object(
                        GATE,
                        "reachable_paper_interface_auxiliary_findings",
                        return_value=[],
                    ),
                ):
                    self.assertEqual(
                        GATE.audit_paper(
                            "Fixture", source_record_snapshot=snapshot
                        ),
                        [],
                    )
            finally:
                GATE.PAPERS = old_papers

        helper.assert_not_called()

    def test_gate_rejects_diagnostic_evidence_without_launching_helper(self) -> None:
        """A noncanonical diagnostic JSON cannot stand in for a full audit."""

        diagnostic = {
            "prompt_version": GATE.SOURCE_RECORD_PROMPT_VERSION,
            "source_record_input_fingerprint": {"no_lean": False},
            "lean_check": {"returncode": 1, "output": "Lean failed"},
        }
        old_papers = GATE.PAPERS
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            audit = root / "Fixture" / "audit"
            audit.mkdir(parents=True)
            (root / "Fixture" / "status.json").write_text(
                "{}\n", encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                "{}\n", encoding="utf-8"
            )
            (audit / "source_record_audit.json").write_text(
                json.dumps(diagnostic), encoding="utf-8"
            )

            try:
                GATE.PAPERS = root
                with patch.object(GATE.subprocess, "run") as helper:
                    findings = GATE.audit_paper("Fixture")
            finally:
                GATE.PAPERS = old_papers

        self.assertEqual(len(findings), 1)
        self.assertIn("current immutable source-record evidence", findings[0].message)
        self.assertIn("source_record_audit_sha256", findings[0].message)
        helper.assert_not_called()

    def test_gate_rejects_explicit_no_lean_record_without_launching_helper(self) -> None:
        """An issued object cannot authenticate a diagnostic --no-lean record."""

        from scripts.source_record_integrity import stamp_source_record_audit_receipts

        payload: dict[str, object] = {
            "paper": "Fixture",
            "prompt_version": GATE.SOURCE_RECORD_PROMPT_VERSION,
            "source_record_policy_version": GATE.SOURCE_RECORD_PROMPT_VERSION,
            "source_record_input_fingerprint": {"max_depth": 4, "no_lean": True},
        }
        stamp_source_record_audit_receipts(payload)
        old_papers = GATE.PAPERS
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Fixture" / "audit").mkdir(parents=True)
            snapshot = GATE.source_record_audit_snapshot_from_bytes(
                "Fixture", json.dumps(payload).encode("utf-8")
            )
            assert snapshot is not None

            try:
                GATE.PAPERS = root
                with patch.object(GATE.subprocess, "run") as helper:
                    findings = GATE.audit_paper(
                        "Fixture", source_record_snapshot=snapshot
                    )
            finally:
                GATE.PAPERS = old_papers

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].binder, "<current source-record scan>")
        self.assertIn("no_lean=false", findings[0].message)
        helper.assert_not_called()

    @staticmethod
    def _run_gate(payload: dict[str, object]) -> list[object]:
        old_papers = GATE.PAPERS
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Fixture" / "audit").mkdir(parents=True)
            snapshot = issued_current_fixture_snapshot(payload)

            try:
                GATE.PAPERS = root
                with patch.object(
                    GATE,
                    "reachable_paper_interface_auxiliary_findings",
                    return_value=[],
                ):
                    return GATE.audit_paper(
                        "Fixture", source_record_snapshot=snapshot
                    )
            finally:
                GATE.PAPERS = old_papers


class SourceRecordSnapshotReuseTests(unittest.TestCase):
    """The conclusion gate reuses one exact raw parse and fails on drift."""

    @staticmethod
    def _payload() -> dict[str, object]:
        return {
            "paper": "Fixture",
            "prompt_version": GATE.SOURCE_RECORD_PROMPT_VERSION,
            "missing_configured_review_rows": [],
            "recursion_failures": [],
            "conclusion_dependency_items": [],
        }

    @staticmethod
    def _write_fixture(root: Path) -> Path:
        audit_dir = root / "Fixture" / "audit"
        audit_dir.mkdir(parents=True)
        (audit_dir / "paper_statement_map.json").write_text(
            "{}\n", encoding="utf-8"
        )
        (root / "Fixture" / "status.json").write_text("{}\n", encoding="utf-8")
        audit_path = audit_dir / "source_record_audit.json"
        audit_path.write_text(
            json.dumps(SourceRecordSnapshotReuseTests._payload()),
            encoding="utf-8",
        )
        return audit_path

    @staticmethod
    def _core_patches() -> list[object]:
        return [
            patch.object(GATE, "current_judgments", return_value={}),
            patch.object(
                GATE, "reachable_paper_interface_auxiliary_findings", return_value=[]
            ),
            patch.object(GATE, "omitted_direct_dependency_findings", return_value=[]),
            patch.object(
                GATE, "source_premise_false_eliminator_findings", return_value=[]
            ),
            patch.object(GATE, "theorem_realization_contract_active", return_value=True),
            patch.object(
                GATE,
                "current_approved_source_convention_antecedent_keys",
                return_value=(set(), set()),
            ),
            patch.object(GATE, "corrected_model_conclusion_bridge", return_value=None),
        ]

    def test_cached_audit_parses_raw_json_once_without_temporary_copy(self) -> None:
        old_papers = GATE.PAPERS
        self.addCleanup(setattr, GATE, "PAPERS", old_papers)
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            audit_path = self._write_fixture(root)
            GATE.PAPERS = root
            core = self._core_patches()

            raw_snapshot_loads = 0
            load_snapshot = EVIDENCE_CONTEXT.load_json_snapshot

            def counted_snapshot_load(path: Path) -> object:
                nonlocal raw_snapshot_loads
                if path == audit_path:
                    raw_snapshot_loads += 1
                return load_snapshot(path)

            with (
                patch.object(
                    EVIDENCE_CONTEXT,
                    "load_json_snapshot",
                    side_effect=counted_snapshot_load,
                ),
                patch.object(
                    EVIDENCE,
                    "_source_record_current_input_fingerprint_error",
                    return_value="",
                ),
                patch.object(
                    EVIDENCE, "_source_record_audit_identity_error", return_value=""
                ),
                patch.object(
                    EVIDENCE,
                    "_corrected_model_scope_contract_findings",
                    return_value=[],
                ),
                patch.object(
                    EVIDENCE,
                    "_current_source_record_judgment_items",
                    return_value={},
                ),
                patch.object(
                    EVIDENCE,
                    "_source_record_identity_process_watch_digest",
                    return_value="stable-watch",
                ),
                patch.object(GATE.subprocess, "run") as helper,
                patch.object(GATE.tempfile, "NamedTemporaryFile") as temporary,
                core[0], core[1], core[2], core[3], core[4], core[5], core[6],
            ):
                findings = GATE.audit_paper(
                    "Fixture", theorem_realization_component_prevalidated=True
                )

        self.assertEqual(findings, [])
        self.assertEqual(raw_snapshot_loads, 1)
        helper.assert_not_called()
        temporary.assert_not_called()

    def test_evidence_context_transfers_validated_payload_without_reparse(self) -> None:
        old_papers = GATE.PAPERS
        self.addCleanup(setattr, GATE, "PAPERS", old_papers)
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture(root)
            folder = root / "Fixture"
            (folder / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            GATE.PAPERS = root
            administrative_rebind = GATE.ValidatedAdministrativeProjectionRebind(
                association_rebinds={},
                association_bindings={},
                rebound_association_bindings={},
            )
            regularity_context = (
                GATE.ConfiguredAssumptionFormalizationRegularityContext(
                    raw_audit_sha256="a" * 64,
                    matches_by_structural_identity={},
                )
            )
            with (
                patch.object(
                    EVIDENCE,
                    "_source_record_current_input_fingerprint_error",
                    return_value="",
                ),
                patch.object(
                    EVIDENCE, "_source_record_audit_identity_error", return_value=""
                ),
                patch.object(
                    EVIDENCE,
                    "_corrected_model_scope_contract_findings",
                    return_value=[],
                ),
                patch.object(
                    EVIDENCE,
                    "_current_source_record_judgment_items",
                    return_value={},
                ),
                patch.object(
                    EVIDENCE,
                    "_source_record_identity_process_watch_digest",
                    return_value="stable-watch",
                ),
                patch.object(
                    EVIDENCE,
                    "source_record_administrative_projection_rebind_context",
                    return_value=(
                        administrative_rebind,
                        folder
                        / "audit"
                        / "source_record_administrative_projection_rebind.json",
                        "",
                    ),
                ),
                patch.object(
                    EVIDENCE,
                    "load_configured_assumption_formalization_regularity_context",
                    return_value=(regularity_context, ""),
                ),
            ):
                context = EVIDENCE.build_evidence_run_context(folder)
            with patch.object(
                GATE.json,
                "loads",
                side_effect=AssertionError("transfer must not parse JSON"),
            ):
                snapshot, error = (
                    GATE.source_record_audit_snapshot_from_evidence_context(
                        "Fixture", context
                    )
                )

        self.assertEqual(error, "")
        self.assertIsNotNone(snapshot)
        assert snapshot is not None
        state = context.require_legacy_source_record_state()
        self.assertIs(snapshot.payload, state.inputs.audit_snapshot.payload)
        self.assertIs(snapshot.status_payload_override, context.status_payload)
        self.assertIs(
            snapshot.paper_statement_map_override,
            context.statement_map,
        )
        transferred_rebind = snapshot.administrative_projection_rebind_override
        association_rebinds = getattr(transferred_rebind, "association_rebinds", None)
        self.assertIsInstance(association_rebinds, Mapping)
        assert isinstance(association_rebinds, Mapping)
        self.assertEqual(dict(association_rebinds), {})
        with self.assertRaises(TypeError):
            association_rebinds["changed"] = {}
        transferred_regularity = (
            snapshot.configured_assumption_regularity_context_override
        )
        self.assertIsInstance(
            transferred_regularity,
            GATE.ConfiguredAssumptionFormalizationRegularityContext,
        )
        assert isinstance(
            transferred_regularity,
            GATE.ConfiguredAssumptionFormalizationRegularityContext,
        )
        with self.assertRaises(TypeError):
            transferred_regularity.matches_by_structural_identity["changed"] = object()
        self.assertTrue(snapshot.content_bound)
        self.assertTrue(snapshot.identity_validated)
        assert snapshot.status_payload_override is not None
        assert snapshot.paper_statement_map_override is not None
        with self.assertRaises(TypeError):
            snapshot.status_payload_override["status"] = "partial"
        with self.assertRaises(TypeError):
            snapshot.paper_statement_map_override["changed"] = True
        assert snapshot.input_raw_bytes_override is not None
        self.assertEqual(
            snapshot.input_raw_bytes_override[
                context.status_snapshot.path.resolve()
            ],
            context.status_snapshot.raw_bytes,
        )
        with self.assertRaises(TypeError):
            snapshot.input_raw_bytes_override[
                context.status_snapshot.path.resolve()
            ] = b"replacement"

    def test_current_v11_transfers_stale_raw_only_as_structural_inventory(
        self,
    ) -> None:
        old_papers = GATE.PAPERS
        self.addCleanup(setattr, GATE, "PAPERS", old_papers)
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture(root)
            folder = root / "Fixture"
            (folder / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            GATE.PAPERS = root
            with (
                patch.object(
                    EVIDENCE,
                    "_source_record_current_input_fingerprint_error",
                    return_value="",
                ),
                patch.object(
                    EVIDENCE,
                    "_source_record_audit_identity_error",
                    return_value="stale historical paper-map identity",
                ),
                patch.object(
                    EVIDENCE,
                    "_source_record_identity_process_watch_digest",
                    return_value="stable-watch",
                ),
            ):
                context = EVIDENCE.build_evidence_run_context(folder)

            rejected, rejected_error = (
                GATE.source_record_audit_snapshot_from_evidence_context(
                    "Fixture", context
                )
            )
            with patch.object(
                EVIDENCE,
                "v11_direct_semantic_review_state",
                return_value=(True, ""),
            ):
                snapshot, error = (
                    GATE.source_record_audit_snapshot_from_evidence_context(
                        "Fixture",
                        context,
                        structural_v11_prevalidated=True,
                    )
                )

            self.assertIsNone(rejected)
            self.assertIn("stale historical paper-map identity", rejected_error)
            self.assertEqual(error, "")
            self.assertIsNotNone(snapshot)
            assert snapshot is not None
            self.assertTrue(snapshot.content_bound)
            self.assertTrue(snapshot.structural_v11_validated)
            self.assertFalse(snapshot.identity_validated)
            self.assertEqual(snapshot.current_judgments_override, {})

            core = self._core_patches()
            with (
                core[0], core[1], core[2], core[3], core[4], core[5], core[6]
            ):
                findings = GATE.audit_paper(
                    "Fixture",
                    theorem_realization_component_prevalidated=True,
                    source_record_snapshot=snapshot,
                )
            self.assertEqual(findings, [])

    def test_evidence_context_rejects_invalid_configured_input_paths(self) -> None:
        old_papers = GATE.PAPERS
        self.addCleanup(setattr, GATE, "PAPERS", old_papers)

        def build_context(folder: Path) -> object:
            with (
                patch.object(
                    EVIDENCE,
                    "_source_record_current_input_fingerprint_error",
                    return_value="",
                ),
                patch.object(
                    EVIDENCE, "_source_record_audit_identity_error", return_value=""
                ),
                patch.object(
                    EVIDENCE,
                    "_corrected_model_scope_contract_findings",
                    return_value=[],
                ),
                patch.object(
                    EVIDENCE,
                    "_current_source_record_judgment_items",
                    return_value={},
                ),
                patch.object(
                    EVIDENCE,
                    "_source_record_identity_process_watch_digest",
                    return_value="stable-watch",
                ),
            ):
                return EVIDENCE.build_evidence_run_context(folder)

        cases = (
            (
                "source-record audit",
                {
                    "review_surface": {
                        "llm_source_record_review": {
                            "source_record_audit_file": "../../outside.json"
                        }
                    }
                },
                "invalid configured source-record audit path",
            ),
            (
                "source-record judgment",
                {
                    "review_surface": {
                        "llm_source_record_review": {
                            "source_record_judgment_file": "../../outside.json"
                        }
                    }
                },
                "invalid configured source-record judgment path",
            ),
            (
                "source-proof fidelity ledger",
                {
                    "review_surface": {
                        "source_proof_fidelity_review": {
                            "ledger_file": "../../outside.json"
                        }
                    }
                },
                "invalid configured source-proof fidelity ledger path",
            ),
            (
                "administrative projection rebind",
                {
                    "review_surface": {
                        "llm_source_record_review": {
                            "source_record_administrative_projection_rebind_file": (
                                "../../outside.json"
                            )
                        }
                    }
                },
                "invalid administrative projection rebind",
            ),
        )
        for label, status_payload, expected_error in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmpdir:
                root = Path(tmpdir)
                self._write_fixture(root)
                folder = root / "Fixture"
                (folder / "status.json").write_text(
                    json.dumps({"status": "formalized", **status_payload}),
                    encoding="utf-8",
                )
                GATE.PAPERS = root
                context = build_context(folder)

                snapshot, error = (
                    GATE.source_record_audit_snapshot_from_evidence_context(
                        "Fixture", context
                    )
                )

                self.assertIsNone(snapshot)
                self.assertIn(expected_error, error)
                self.assertIn("escapes the paper folder", error)

    def test_configured_match_snapshot_transfers_empty_projection_without_fallback(
        self,
    ) -> None:
        old_gate_papers = GATE.PAPERS
        old_evidence_root = EVIDENCE.ROOT
        self.addCleanup(setattr, GATE, "PAPERS", old_gate_papers)
        self.addCleanup(setattr, EVIDENCE, "ROOT", old_evidence_root)
        with tempfile.TemporaryDirectory() as tmpdir:
            repository_root = Path(tmpdir)
            papers = repository_root / "papers"
            self._write_fixture(papers)
            folder = papers / "Fixture"
            match_path = folder / "audit" / "configured_match.json"
            match_bytes = b'{"schema": 1, "paper": "Fixture", "items": {}}\n'
            match_path.write_bytes(match_bytes)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "status": "formalized",
                        "review_surface": {
                            "llm_source_record_review": {
                                "source_record_judgment_file": (
                                    "papers/Fixture/audit/configured_match.json"
                                )
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            GATE.PAPERS = papers
            EVIDENCE.ROOT = repository_root
            with (
                patch.object(
                    EVIDENCE,
                    "_source_record_current_input_fingerprint_error",
                    return_value="",
                ),
                patch.object(
                    EVIDENCE, "_source_record_audit_identity_error", return_value=""
                ),
                patch.object(
                    EVIDENCE,
                    "_corrected_model_scope_contract_findings",
                    return_value=[],
                ),
                patch.object(
                    EVIDENCE,
                    "_current_source_record_judgment_items",
                    return_value={},
                ),
                patch.object(
                    EVIDENCE,
                    "_source_record_identity_process_watch_digest",
                    return_value="stable-watch",
                ),
            ):
                context = EVIDENCE.build_evidence_run_context(folder)
            snapshot, error = GATE.source_record_audit_snapshot_from_evidence_context(
                "Fixture", context
            )
            assert snapshot is not None

            with patch.object(
                GATE,
                "current_judgments",
                side_effect=AssertionError(
                    "an empty transferred projection must not trigger live fallback"
                ),
            ), patch.object(
                GATE,
                "reachable_paper_interface_auxiliary_findings",
                return_value=[],
            ):
                findings = GATE.audit_paper(
                    "Fixture",
                    theorem_realization_component_prevalidated=True,
                    source_record_snapshot=snapshot,
                )

        self.assertEqual(error, "")
        self.assertEqual(findings, [])
        self.assertEqual(snapshot.source_record_match_path, match_path)
        self.assertEqual(
            snapshot.source_record_match_sha256,
            hashlib.sha256(match_bytes).hexdigest(),
        )
        self.assertIs(
            snapshot.current_judgments_override,
            context.require_legacy_source_record_state().current_source_record_judgments,
        )

    def test_theorem_realization_uses_checked_auxiliary_absence_without_reload(
        self,
    ) -> None:
        payload = {
            "theorem_realization_contract_schema": 1,
            "source_proof_fidelity": {},
        }
        with (
            patch.object(
                GATE, "source_spec_correspondence_requested", return_value=True
            ),
            patch.object(
                GATE,
                "current_administrative_projection_rebind_context",
                side_effect=AssertionError("checked absence must not reload a receipt"),
            ),
            patch.object(
                GATE,
                "load_configured_assumption_formalization_regularity_context",
                side_effect=AssertionError("checked absence must not reload a ledger"),
            ),
        ):
            findings = GATE.theorem_realization_component_contract_findings(
                "Fixture",
                payload,
                {},
                status_payload_override={"status": "formalized"},
                paper_statement_map_override={},
                administrative_projection_rebind_override=None,
                configured_assumption_regularity_context_override=None,
                configured_assumption_regularity_context_error_override="",
            )

        self.assertEqual(findings, [])

    def test_regularity_context_error_blocks_only_regularity_credit(self) -> None:
        payload = {
            "theorem_realization_contract_schema": 1,
            "source_proof_fidelity": {},
            "theorem_facing_input_items": [
                {"row": "row", "binder": "input", "judgment_key": "regularity"}
            ],
        }
        with patch.object(
            GATE, "source_spec_correspondence_requested", return_value=True
        ):
            blocked = GATE.theorem_realization_component_contract_findings(
                "Fixture",
                payload,
                {
                    "regularity": {
                        "classification": GATE.FORMALIZATION_REGULARITY_CLASSIFICATION
                    }
                },
                status_payload_override={"status": "formalized"},
                paper_statement_map_override={},
                administrative_projection_rebind_override=None,
                configured_assumption_regularity_context_override=None,
                configured_assumption_regularity_context_error_override=(
                    "configured regularity receipt is stale"
                ),
            )
            ordinary = GATE.theorem_realization_component_contract_findings(
                "Fixture",
                {
                    "theorem_realization_contract_schema": 1,
                    "source_proof_fidelity": {},
                },
                {"ordinary": {"classification": "validated_source_assumption"}},
                status_payload_override={"status": "formalized"},
                paper_statement_map_override={},
                administrative_projection_rebind_override=None,
                configured_assumption_regularity_context_override=None,
                configured_assumption_regularity_context_error_override=(
                    "configured regularity receipt is stale"
                ),
            )

        self.assertEqual(len(blocked), 1)
        self.assertIn("configured regularity receipt is stale", blocked[0].message)
        self.assertEqual(ordinary, [])

    def test_transferred_snapshot_never_rereads_status_or_statement_map(self) -> None:
        old_papers = GATE.PAPERS
        self.addCleanup(setattr, GATE, "PAPERS", old_papers)
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture(root)
            folder = root / "Fixture"
            (folder / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            GATE.PAPERS = root
            with (
                patch.object(
                    EVIDENCE,
                    "_source_record_current_input_fingerprint_error",
                    return_value="",
                ),
                patch.object(
                    EVIDENCE, "_source_record_audit_identity_error", return_value=""
                ),
                patch.object(
                    EVIDENCE,
                    "_corrected_model_scope_contract_findings",
                    return_value=[],
                ),
                patch.object(
                    EVIDENCE,
                    "_current_source_record_judgment_items",
                    return_value={},
                ),
                patch.object(
                    EVIDENCE,
                    "_source_record_identity_process_watch_digest",
                    return_value="stable-watch",
                ),
            ):
                context = EVIDENCE.build_evidence_run_context(folder)
            snapshot, error = GATE.source_record_audit_snapshot_from_evidence_context(
                "Fixture", context
            )
            assert snapshot is not None
            with (
                patch.object(
                    GATE,
                    "load_payload",
                    side_effect=AssertionError(
                        "a transferred snapshot must not reopen status or statement map"
                    ),
                ),
                patch.object(
                    GATE,
                    "reachable_paper_interface_auxiliary_findings",
                    return_value=[],
                ),
            ):
                findings = GATE.audit_paper(
                    "Fixture", source_record_snapshot=snapshot
                )

        self.assertEqual(error, "")
        self.assertEqual(findings, [])

    def test_live_status_and_map_drift_only_invalidates_final_transaction(
        self,
    ) -> None:
        old_papers = GATE.PAPERS
        self.addCleanup(setattr, GATE, "PAPERS", old_papers)
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture(root)
            folder = root / "Fixture"
            status_path = folder / "status.json"
            map_path = folder / "audit" / "paper_statement_map.json"
            status_path.write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            GATE.PAPERS = root

            def mutate_live_inputs(*_args: object, **_kwargs: object) -> list[object]:
                status_path.write_text(
                    json.dumps(
                        {
                            "status": "formalized",
                            "theorem_realization_contract": {"required": True},
                        }
                    ),
                    encoding="utf-8",
                )
                map_path.write_text(
                    json.dumps({"source_claim_atoms_schema": 1}),
                    encoding="utf-8",
                )
                return []

            with (
                patch.object(
                    EVIDENCE,
                    "_source_record_current_input_fingerprint_error",
                    return_value="",
                ),
                patch.object(
                    EVIDENCE, "_source_record_audit_identity_error", return_value=""
                ),
                patch.object(
                    EVIDENCE,
                    "_corrected_model_scope_contract_findings",
                    return_value=[],
                ),
                patch.object(
                    EVIDENCE,
                    "_current_source_record_judgment_items",
                    return_value={},
                ),
                patch.object(
                    EVIDENCE,
                    "_source_record_identity_process_watch_digest",
                    return_value="stable-watch",
                ),
                patch.object(
                    GATE,
                    "missing_configured_row_findings",
                    side_effect=mutate_live_inputs,
                ),
                patch.object(
                    GATE,
                    "load_payload",
                    side_effect=AssertionError(
                        "classification must retain the transferred status and map"
                    ),
                ),
                patch.object(
                    GATE,
                    "reachable_paper_interface_auxiliary_findings",
                    return_value=[],
                ),
            ):
                findings = GATE.audit_paper("Fixture")

        messages = [finding.message for finding in findings]
        self.assertTrue(
            any("statement-map bytes changed during the audit" in message for message in messages)
        )
        self.assertTrue(
            any("evidence inputs changed" in message for message in messages)
        )
        self.assertTrue(
            all(
                "theorem-realization component contract ledger is missing" not in message
                for message in messages
            )
        )

    def test_canonical_raw_mutation_during_audit_fails_closed(self) -> None:
        old_papers = GATE.PAPERS
        self.addCleanup(setattr, GATE, "PAPERS", old_papers)
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            audit_path = self._write_fixture(root)
            GATE.PAPERS = root
            core = self._core_patches()
            snapshot = issued_current_fixture_snapshot(
                self._payload(), source_path=audit_path
            )

            def mutate_raw(*_args: object, **_kwargs: object) -> dict[str, object]:
                audit_path.write_text('{"changed": true}\n', encoding="utf-8")
                return {}

            core[0] = patch.object(GATE, "current_judgments", side_effect=mutate_raw)
            with (
                core[0], core[1], core[2], core[3], core[4], core[5], core[6],
            ):
                findings = GATE.audit_paper(
                    "Fixture",
                    theorem_realization_component_prevalidated=True,
                    source_record_snapshot=snapshot,
                )

        self.assertEqual(len(findings), 1)
        self.assertIn("snapshot bytes changed during the audit", findings[0].message)

    def test_caller_snapshot_is_revalidated_and_statement_map_drift_fails(self) -> None:
        old_papers = GATE.PAPERS
        self.addCleanup(setattr, GATE, "PAPERS", old_papers)
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            audit_path = self._write_fixture(root)
            map_path = root / "Fixture" / "audit" / "paper_statement_map.json"
            GATE.PAPERS = root
            snapshot = GATE.load_source_record_audit_snapshot("Fixture", audit_path)
            assert snapshot is not None
            core = self._core_patches()

            def mutate_map(*_args: object, **_kwargs: object) -> dict[str, object]:
                map_path.write_text('{"changed": true}\n', encoding="utf-8")
                return {}

            core[0] = patch.object(GATE, "current_judgments", side_effect=mutate_map)
            with (
                patch.object(GATE, "source_record_audit_identity_error", return_value="") as identity,
                core[0], core[1], core[2], core[3], core[4], core[5], core[6],
            ):
                findings = GATE.audit_paper(
                    "Fixture",
                    theorem_realization_component_prevalidated=True,
                    source_record_snapshot=snapshot,
                )

        identity.assert_called_once()
        self.assertEqual(len(findings), 1)
        self.assertIn("statement-map bytes changed during the audit", findings[0].message)

    def test_injected_old_prompt_snapshot_fails_closed(self) -> None:
        snapshot = GATE.source_record_audit_snapshot_from_bytes(
            "Fixture",
            b'{"paper":"Fixture","prompt_version":"old"}',
        )
        assert snapshot is not None

        findings = GATE.audit_paper(
            "Fixture",
            theorem_realization_component_prevalidated=True,
            source_record_snapshot=snapshot,
        )

        self.assertEqual(len(findings), 1)
        self.assertIn("not the current", findings[0].message)

    def test_snapshot_capability_does_not_survive_replace_or_payload_mutation(
        self,
    ) -> None:
        snapshot = GATE.source_record_audit_snapshot_from_bytes(
            "Fixture",
            json.dumps(self._payload()).encode("utf-8"),
        )
        assert snapshot is not None
        replaced = replace(snapshot, payload=dict(snapshot.payload))
        self.assertFalse(replaced.content_bound)

        with self.assertRaises(TypeError):
            snapshot.payload["paper"] = "Forged"


if __name__ == "__main__":
    unittest.main()
