#!/usr/bin/env python3
"""Focused source-record regressions for source-first claim atoms."""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    value = str(import_root)
    if value not in sys.path:
        sys.path.insert(0, value)

HELPER = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
SPEC = importlib.util.spec_from_file_location("source_record_claim_atoms_audit", HELPER)
assert SPEC is not None and SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = AUDIT
SPEC.loader.exec_module(AUDIT)


def digest(letter: str) -> str:
    return letter * 64


class SourceRecordClaimAtomTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper = self.root / "papers" / "FixturePaper"
        (self.paper / "audit").mkdir(parents=True)
        self.source = self.paper / "source.txt"
        self.original_source = (
            "Theorem 3. Every target-rate pair has a structured cutoff policy.\n"
            "The permitted cutoff endpoints include empty and accept-all policies.\n"
            "At a high target-rate ratio, accept-all is uniquely optimal.\n"
        )
        self.source.write_text(self.original_source, encoding="utf-8")
        (self.paper / "status.json").write_text(
            json.dumps({"status": "formalized"}), encoding="utf-8"
        )

    def source_digest(self) -> str:
        return hashlib.sha256(self.source.read_bytes()).hexdigest()

    def payload(self) -> dict[str, object]:
        return {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": self.source_digest(),
            "source_coverage_mode": "named_theoretical_statements",
            "source_claim_atoms_schema": 1,
            "items": {
                "source_theorem_three": {
                "source_kind": "theorem",
                "source_location": "source.txt:1-3",
                "statement": "Theorem 3 has a general structured-cutoff clause and a separate high-ratio uniqueness clause.",
                "source_anchor_evidence": [
                    {
                        "path": "source.txt",
                        "line_start": 1,
                        "line_end": 3,
                        "quoted_text": self.original_source.rstrip("\n"),
                        "quoted_text_sha256": hashlib.sha256(
                            self.original_source.rstrip("\n").encode("utf-8")
                        ).hexdigest(),
                    }
                ],
                # The atom routes are authoritative. Leaving the legacy
                    # parent route list absent verifies that no route is
                    # inferred from a name or map-key convention.
                    "source_claim_atoms": [
                        {
                            "id": "general-cutoff",
                            "source_locator": "source.txt:1-2",
                            "semantic_claim": "For every target-rate pair, a structured cutoff policy exists, including the empty and accept-all endpoints.",
                            "reviewed_lean_route": "Fixture.proof_alpha",
                        },
                        {
                            "id": "high-ratio-uniqueness",
                            "source_locator": "source.txt:3",
                            "semantic_claim": "At the stated high target-rate ratio, accept-all is uniquely optimal.",
                            "reviewed_lean_route": "Fixture.proof_beta",
                        },
                    ],
                }
            },
        }

    @staticmethod
    def row_qualified_names() -> dict[str, str]:
        return {
            "alpha": "Fixture.proof_alpha",
            "beta": "Fixture.proof_beta",
        }

    @staticmethod
    def row_qualified_names_with_spec() -> dict[str, str]:
        return {
            "alpha": "Fixture.proof_alpha",
            "alpha_spec": "Fixture.proof_alpha_spec",
            "beta": "Fixture.proof_beta",
        }

    @staticmethod
    def declarations() -> dict[str, str]:
        return {
            "alpha": "theorem proof_alpha : True := True.intro",
            "beta": "theorem proof_beta : True := True.intro",
        }

    @staticmethod
    def signatures() -> dict[str, str]:
        # Both opaque route spellings elaborate to the same proposition in
        # this fixture. The source atom, rather than a declaration name,
        # therefore determines whether an item can be reused.
        return {
            "Fixture.proof_alpha": digest("a"),
            "Fixture.proof_beta": digest("a"),
        }

    def semantic_items(self) -> list[dict[str, object]]:
        return [
            {
                "row": "alpha",
                "qualified_declaration": "Fixture.proof_alpha",
                "judgment_key": "semantic-model::alpha",
                "lean_source_declaration": self.declarations()["alpha"],
                "kind": "semantic_model_comparison",
                "dimensions": [{"id": "expanded_binders_and_domain"}],
            },
            {
                "row": "beta",
                "qualified_declaration": "Fixture.proof_beta",
                "judgment_key": "semantic-model::beta",
                "lean_source_declaration": self.declarations()["beta"],
                "kind": "semantic_model_comparison",
                "dimensions": [{"id": "expanded_binders_and_domain"}],
            },
        ]

    def attach(self, payload: dict[str, object]) -> list[dict[str, object]]:
        items = self.semantic_items()
        attached, errors, counts = AUDIT.attach_source_claim_atom_associations(
            items,
            paper_dir=self.paper,
            paper_statement_map=payload,
            declarations=self.declarations(),
            row_qualified_names=self.row_qualified_names(),
            elaborated_signature_sha256_by_qualified=self.signatures(),
        )
        self.assertEqual(errors, [], errors)
        self.assertEqual(counts["source_claim_atom_context_count"], 2)
        self.assertEqual(counts["source_claim_atom_association_count"], 2)
        return attached

    def item_semantic_ids(
        self, items: list[dict[str, object]], payload: dict[str, object]
    ) -> dict[str, str]:
        AUDIT.attach_source_record_item_digests(
            items,
            paper_statement_map=payload,
            row_qualified_names=self.row_qualified_names(),
            elaborated_signature_sha256_by_qualified=self.signatures(),
        )
        return {
            str(item["row"]): str(item["source_record_item_semantic_id"])
            for item in items
        }

    def write_map(self, payload: dict[str, object]) -> None:
        (self.paper / "audit" / "paper_statement_map.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )

    def single_evidence_atom_payload(
        self, *, with_semantic_contract: bool = False
    ) -> dict[str, object]:
        """Build one exact atom route, optionally with its direct/Spec pair."""

        payload = self.payload()
        item = payload["items"]["source_theorem_three"]
        assert isinstance(item, dict)
        atoms = item["source_claim_atoms"]
        assert isinstance(atoms, list) and isinstance(atoms[0], dict)
        item["source_claim_atoms"] = [copy.deepcopy(atoms[0])]
        if with_semantic_contract:
            payload["semantic_contract_schema"] = 1
            item["claim_bearing"] = True
            item["semantic_contract"] = {
                "spec_declaration": "Fixture.proof_alpha_spec",
                "evidence_declaration": "Fixture.proof_alpha",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            }
        return payload

    def test_atom_only_selection_uses_only_its_evidence_route(self) -> None:
        payload = self.single_evidence_atom_payload()
        self.write_map(payload)

        selected, _selected_map, selection = AUDIT.source_coverage_review_rows(
            self.paper,
            ["alpha", "alpha_spec", "beta"],
            self.row_qualified_names_with_spec(),
        )

        self.assertEqual(selected, ["alpha"])
        self.assertEqual(selection["source_coverage_atom_contract_companions"], [])
        self.assertEqual(selection["source_coverage_route_errors"], [])

    def test_support_only_theorem_is_retained_without_a_direct_atom_route(self) -> None:
        """A proof-support theorem is inventory-only, not a source endpoint."""

        payload = self.payload()
        item = payload["items"]["source_theorem_three"]
        assert isinstance(item, dict)
        item["source_status"] = "support_only"
        item.pop("source_claim_atoms")
        self.write_map(payload)

        selected, _selected_map, selection = AUDIT.source_coverage_review_rows(
            self.paper,
            ["alpha", "beta"],
            self.row_qualified_names(),
        )
        identities, errors = AUDIT.explicit_direct_source_route_identities(
            payload,
            row_qualified_names=self.row_qualified_names(),
        )

        self.assertIn(
            "source_theorem_three",
            selection["source_coverage_selected_source_items"],
        )
        self.assertEqual(selected, [])
        self.assertEqual(selection["source_coverage_unrouted_source_items"], [])
        self.assertEqual(selection["source_coverage_route_errors"], [])
        self.assertEqual(identities, {})
        self.assertEqual(errors, [])

    def test_quarantined_source_defect_is_retained_without_a_direct_atom_route(self) -> None:
        """A false printed theorem has defect support, not a proof endpoint."""

        payload = self.payload()
        item = payload["items"]["source_theorem_three"]
        assert isinstance(item, dict)
        item["source_status"] = "quarantined_source_defect"
        item["support_lean_declarations"] = ["Fixture.proof_alpha"]
        item.pop("source_claim_atoms")
        self.write_map(payload)

        selected, _selected_map, selection = AUDIT.source_coverage_review_rows(
            self.paper,
            ["alpha", "beta"],
            self.row_qualified_names(),
        )
        identities, errors = AUDIT.explicit_direct_source_route_identities(
            payload,
            row_qualified_names=self.row_qualified_names(),
        )

        self.assertIn(
            "source_theorem_three",
            selection["source_coverage_selected_source_items"],
        )
        self.assertEqual(selected, [])
        self.assertEqual(selection["source_coverage_unrouted_source_items"], [])
        self.assertEqual(selection["source_coverage_route_errors"], [])
        self.assertEqual(identities, {})
        self.assertEqual(errors, [])

    def test_source_declared_open_item_is_retained_without_a_proof_route(self) -> None:
        """A valid named open problem remains inventory, not proof debt."""

        payload = self.payload()
        item = payload["items"]["source_theorem_three"]
        assert isinstance(item, dict)
        item.update(
            {
                "source_kind": "open_problem",
                "claim_bearing": False,
                "source_scope_classification": (
                    "source_declared_open_nonresult_observation"
                ),
                "coverage_status": "source_declared_open",
                "protocol_role": "source_declared_open",
            }
        )
        item.pop("source_claim_atoms")
        self.write_map(payload)

        selected, _selected_map, selection = AUDIT.source_coverage_review_rows(
            self.paper,
            ["alpha", "beta"],
            self.row_qualified_names(),
        )
        identities, errors = AUDIT.explicit_direct_source_route_identities(
            payload,
            row_qualified_names=self.row_qualified_names(),
        )

        self.assertIn(
            "source_theorem_three",
            selection["source_coverage_selected_source_items"],
        )
        self.assertEqual(selected, [])
        self.assertEqual(selection["source_coverage_unrouted_source_items"], [])
        self.assertEqual(selection["source_coverage_route_errors"], [])
        self.assertEqual(identities, {})
        self.assertEqual(errors, [])

    def test_single_atom_direct_spec_contract_adds_only_a_spec_companion(self) -> None:
        payload = self.single_evidence_atom_payload(with_semantic_contract=True)
        self.write_map(payload)

        selected, _selected_map, selection = AUDIT.source_coverage_review_rows(
            self.paper,
            ["alpha", "alpha_spec", "beta"],
            self.row_qualified_names_with_spec(),
        )

        self.assertEqual(selected, ["alpha", "alpha_spec"])
        self.assertEqual(
            selection["source_coverage_atom_contract_companions"],
            [
                {
                    "source_item": "source_theorem_three",
                    "evidence_declaration": "Fixture.proof_alpha",
                    "spec_declaration": "Fixture.proof_alpha_spec",
                }
            ],
        )
        self.assertEqual(selection["source_coverage_route_errors"], [])

    def test_multiple_atom_routes_cannot_borrow_one_parent_spec_companion(self) -> None:
        payload = self.single_evidence_atom_payload(with_semantic_contract=True)
        item = payload["items"]["source_theorem_three"]
        assert isinstance(item, dict)
        original_atoms = self.payload()["items"]["source_theorem_three"]
        assert isinstance(original_atoms, dict)
        second_atom = original_atoms["source_claim_atoms"][1]
        assert isinstance(second_atom, dict)
        atoms = item["source_claim_atoms"]
        assert isinstance(atoms, list)
        atoms.append(copy.deepcopy(second_atom))
        self.write_map(payload)

        selected, _selected_map, selection = AUDIT.source_coverage_review_rows(
            self.paper,
            ["alpha", "alpha_spec", "beta"],
            self.row_qualified_names_with_spec(),
        )

        self.assertEqual(selected, ["alpha", "beta"])
        self.assertEqual(selection["source_coverage_atom_contract_companions"], [])
        self.assertTrue(
            any(
                "requires every source-claim atom to route to its one exact evidence declaration"
                in error
                for error in selection["source_coverage_route_errors"]
            ),
            selection["source_coverage_route_errors"],
        )

    def test_malformed_or_boolean_atom_schema_cannot_fall_back_to_parent_contract(self) -> None:
        for malformed_schema in ("1", True):
            with self.subTest(schema=repr(malformed_schema)):
                payload = self.single_evidence_atom_payload(with_semantic_contract=True)
                payload["source_claim_atoms_schema"] = malformed_schema
                self.write_map(payload)

                selected, _selected_map, selection = AUDIT.source_coverage_review_rows(
                    self.paper,
                    ["alpha", "alpha_spec", "beta"],
                    self.row_qualified_names_with_spec(),
                )

                self.assertEqual(selected, [])
                self.assertEqual(
                    selection["source_coverage_atom_contract_companions"], []
                )
                self.assertTrue(
                    any(
                        "source-claim atom contract requires top-level "
                        "source_claim_atoms_schema: 1" in error
                        for error in selection["source_coverage_route_errors"]
                    ),
                    selection["source_coverage_route_errors"],
                )

    def test_compound_atoms_select_both_routes_and_emit_current_quote_context(self) -> None:
        payload = self.payload()
        self.write_map(payload)

        selected, _selected_map, selection = AUDIT.source_coverage_review_rows(
            self.paper, ["alpha", "beta"], self.row_qualified_names()
        )
        self.assertEqual(selected, ["alpha", "beta"])
        self.assertEqual(selection["source_coverage_route_errors"], [])

        items = self.attach(payload)
        by_row = {str(item["row"]): item for item in items}
        alpha_contexts = by_row["alpha"]["source_claim_atom_contexts"]
        beta_contexts = by_row["beta"]["source_claim_atom_contexts"]
        assert isinstance(alpha_contexts, list) and isinstance(beta_contexts, list)
        self.assertEqual(alpha_contexts[0]["id"], "general-cutoff")
        self.assertIn("Every target-rate pair", alpha_contexts[0]["source_quote"])
        self.assertEqual(beta_contexts[0]["id"], "high-ratio-uniqueness")
        self.assertIn("uniquely optimal", beta_contexts[0]["source_quote"])

        association = by_row["alpha"]["source_claim_atom_association"]
        assert isinstance(association, dict)
        self.assertEqual(
            association["source_item_identities"][0]["source_key"],
            "source_theorem_three",
        )
        self.assertEqual(
            association["source_claim_atom_routes"][0]["reviewed_lean_route"],
            "Fixture.proof_alpha",
        )
        self.assertTrue(
            AUDIT.SHA256_RE.fullmatch(
                str(association["source_claim_atom_semantic_association_sha256"])
            )
        )

    def test_atom_semantics_and_current_quote_invalidate_item_reuse(self) -> None:
        payload = self.payload()
        baseline_items = self.attach(payload)
        baseline_ids = self.item_semantic_ids(baseline_items, payload)

        claim_changed = copy.deepcopy(payload)
        claim_item = claim_changed["items"]["source_theorem_three"]
        assert isinstance(claim_item, dict)
        claim_atoms = claim_item["source_claim_atoms"]
        assert isinstance(claim_atoms, list) and isinstance(claim_atoms[0], dict)
        claim_atoms[0]["semantic_claim"] = (
            "For every target-rate pair, a nonempty finite cutoff policy exists."
        )
        claim_items = self.attach(claim_changed)
        claim_ids = self.item_semantic_ids(claim_items, claim_changed)
        self.assertNotEqual(baseline_ids["alpha"], claim_ids["alpha"])
        self.assertEqual(baseline_ids["beta"], claim_ids["beta"])

        quote_changed = copy.deepcopy(payload)
        original_parent_item = copy.deepcopy(quote_changed["items"])
        self.source.write_text(
            self.original_source.replace("structured cutoff", "repaired structured cutoff"),
            encoding="utf-8",
        )
        quote_changed["source_artifact_sha256"] = self.source_digest()
        self.assertEqual(quote_changed["items"], original_parent_item)
        quote_items = self.attach(quote_changed)
        quote_ids = self.item_semantic_ids(quote_items, quote_changed)
        self.assertNotEqual(baseline_ids["alpha"], quote_ids["alpha"])
        self.assertEqual(baseline_ids["beta"], quote_ids["beta"])

    def test_route_rename_preserves_atom_semantic_reuse_identity(self) -> None:
        payload = self.payload()
        baseline_items = self.attach(payload)
        baseline_ids = self.item_semantic_ids(baseline_items, payload)
        baseline_association = baseline_items[0]["source_claim_atom_association"]
        assert isinstance(baseline_association, dict)

        renamed = copy.deepcopy(payload)
        renamed_item = renamed["items"]["source_theorem_three"]
        assert isinstance(renamed_item, dict)
        renamed_atoms = renamed_item["source_claim_atoms"]
        assert isinstance(renamed_atoms, list) and isinstance(renamed_atoms[0], dict)
        renamed_atoms[0]["reviewed_lean_route"] = "Fixture.renamed_alpha"
        baseline_parent_item = payload["items"]["source_theorem_three"]
        assert isinstance(baseline_parent_item, dict)
        self.assertEqual(
            AUDIT.source_record_source_item_semantic_sha256(
                baseline_parent_item, ""
            ),
            AUDIT.source_record_source_item_semantic_sha256(renamed_item, ""),
        )
        renamed_rows = {
            "renamed": "Fixture.renamed_alpha",
            "beta": "Fixture.proof_beta",
        }
        renamed_declarations = {
            "renamed": "theorem renamed_alpha : True := True.intro",
            "beta": self.declarations()["beta"],
        }
        renamed_signatures = {
            "Fixture.renamed_alpha": digest("a"),
            "Fixture.proof_beta": digest("a"),
        }
        renamed_items: list[dict[str, object]] = [
            {
                "row": "renamed",
                "qualified_declaration": "Fixture.renamed_alpha",
                "judgment_key": "semantic-model::renamed",
                "lean_source_declaration": renamed_declarations["renamed"],
                "kind": "semantic_model_comparison",
                "dimensions": [{"id": "expanded_binders_and_domain"}],
            },
            self.semantic_items()[1],
        ]
        attached, errors, _counts = AUDIT.attach_source_claim_atom_associations(
            renamed_items,
            paper_dir=self.paper,
            paper_statement_map=renamed,
            declarations=renamed_declarations,
            row_qualified_names=renamed_rows,
            elaborated_signature_sha256_by_qualified=renamed_signatures,
        )
        self.assertEqual(errors, [], errors)
        AUDIT.attach_source_record_item_digests(
            attached,
            paper_statement_map=renamed,
            row_qualified_names=renamed_rows,
            elaborated_signature_sha256_by_qualified=renamed_signatures,
        )
        renamed_association = attached[0]["source_claim_atom_association"]
        assert isinstance(renamed_association, dict)
        self.assertEqual(
            baseline_association["source_claim_atom_semantic_association_sha256"],
            renamed_association["source_claim_atom_semantic_association_sha256"],
        )
        self.assertEqual(
            baseline_ids["alpha"], attached[0]["source_record_item_semantic_id"]
        )

    def test_missing_or_mismatched_atom_route_fails_closed(self) -> None:
        payload = self.payload()
        item = payload["items"]["source_theorem_three"]
        assert isinstance(item, dict)
        atoms = item["source_claim_atoms"]
        assert isinstance(atoms, list) and isinstance(atoms[0], dict)
        atoms[0]["reviewed_lean_route"] = "Fixture.not_configured"

        self.write_map(payload)
        _selected, _selected_map, selection = AUDIT.source_coverage_review_rows(
            self.paper, ["alpha", "beta"], self.row_qualified_names()
        )
        self.assertTrue(
            any("not an exact configured PaperInterface review declaration" in error for error in selection["source_coverage_route_errors"]),
            selection["source_coverage_route_errors"],
        )

        items = self.semantic_items()
        _attached, errors, _counts = AUDIT.attach_source_claim_atom_associations(
            items,
            paper_dir=self.paper,
            paper_statement_map=payload,
            declarations=self.declarations(),
            row_qualified_names=self.row_qualified_names(),
            elaborated_signature_sha256_by_qualified=self.signatures(),
        )
        self.assertTrue(
            any("is not an exact configured review declaration" in error for error in errors),
            errors,
        )


if __name__ == "__main__":
    unittest.main()
