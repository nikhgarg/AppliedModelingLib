#!/usr/bin/env python3
"""Regressions for proof-endpoint to transparent-Spec closeout projection."""

from __future__ import annotations

import hashlib
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

from scripts import audit_repository, review_surface_structure  # noqa: E402
from scripts import source_record_integrity  # noqa: E402


class CrossFileSemanticReviewSurfaceTests(unittest.TestCase):
    def write_fixture(
        self, folder: Path
    ) -> tuple[
        dict[str, object],
        dict[str, list[audit_repository.LeanDeclaration]],
        dict[str, audit_repository.LeanDeclaration],
        dict[str, object],
    ]:
        audit = folder / "audit"
        audit.mkdir(parents=True)
        interface = folder / "PaperInterface.lean"
        proof_interface = folder / "ProofInterface.lean"
        interface.write_text(
            "namespace Fixture\n"
            "namespace PaperInterface\n"
            "abbrev sourceSpec : Prop := True\n"
            "theorem unreviewed (h : True) : True := h\n"
            "end PaperInterface\n"
            "end Fixture\n",
            encoding="utf-8",
        )
        proof_interface.write_text(
            "namespace Fixture\n"
            "namespace ProofInterface\n"
            "theorem sourceSpec_proof : True := by trivial\n"
            "end ProofInterface\n"
            "end Fixture\n",
            encoding="utf-8",
        )
        direct = "Fixture.ProofInterface.sourceSpec_proof"
        spec = "Fixture.PaperInterface.sourceSpec"
        unreviewed = "Fixture.PaperInterface.unreviewed"
        declaration_index = audit_repository.paper_lean_declaration_index(folder)
        declarations = {
            qualified: declaration_index[qualified][0]
            for qualified in (direct, spec, unreviewed)
        }
        direct_source = review_surface_structure.review_declaration_blocks(
            proof_interface.read_text(encoding="utf-8")
        )["sourceSpec_proof"][2]
        spec_source = review_surface_structure.review_declaration_blocks(
            interface.read_text(encoding="utf-8")
        )["sourceSpec"][2]
        direct_declaration_sha = hashlib.sha256(
            direct_source.encode("utf-8")
        ).hexdigest()
        spec_declaration_sha = hashlib.sha256(spec_source.encode("utf-8")).hexdigest()
        direct_signature_sha = hashlib.sha256(b"direct signature").hexdigest()
        spec_signature_sha = hashlib.sha256(b"spec signature").hexdigest()
        direct_identity = {
            "qualified_declaration": direct,
            "declaration_sha256": direct_declaration_sha,
        }
        spec_identity = {
            "qualified_declaration": spec,
            "declaration_sha256": spec_declaration_sha,
        }
        direct_signature_identity = {
            "qualified_declaration": direct,
            "elaborated_signature_sha256": direct_signature_sha,
        }
        source_identity = {
            "source_key": "theorem_one",
            "source_kind": "theorem",
            "source_location": "source.tex:10-12",
            "source_map_item_sha256": hashlib.sha256(b"source item").hexdigest(),
            "source_semantic_sha256": hashlib.sha256(b"source semantics").hexdigest(),
            "semantic_contract": {
                "evidence_declaration": direct,
                "spec_declaration": spec,
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }
        structural_surface = {
            "binder_domains": [],
            "alpha_normalized_result": "True",
        }
        semantic_item = {
            "judgment_key": "semantic-model::theorem-one",
            "qualified_declaration": direct,
            "reviewed_declaration_identity": direct_identity,
            "reviewed_elaborated_signature_identities": [direct_signature_identity],
            "semantic_surface_origin": {
                "kind": "transparent_spec_body",
                "qualified_declaration": spec,
            },
            "semantic_contract_group": {
                "schema": 1,
                "structural_alpha_normalized_equal": True,
                "source_item_identities": [source_identity],
                "member_rows": [
                    {
                        "role": "direct_evidence",
                        "qualified_declaration": direct,
                        "reviewed_declaration_identity": direct_identity,
                    },
                    {
                        "role": "transparent_spec",
                        "qualified_declaration": spec,
                        "reviewed_declaration_identity": spec_identity,
                    },
                ],
                "direct_evidence_type": {
                    "qualified_declaration": direct,
                    "structural_alpha_normalized_surface": structural_surface,
                },
                "surface_root": {
                    "kind": "transparent_spec_body",
                    "qualified_declaration": spec,
                    "structural_alpha_normalized_surface": structural_surface,
                },
            },
            "semantic_contract_source_association": {
                "schema": 2,
                "role": "direct_evidence",
                "paired_qualified_declaration": spec,
                "review_scope": "individual_row_only",
                "structural_pairing": "not_asserted_by_source_association",
                "reviewed_declaration_identity": direct_identity,
                "reviewed_elaborated_signature_identity": direct_signature_identity,
                "semantic_association_sha256": hashlib.sha256(
                    b"direct spec association"
                ).hexdigest(),
                "source_item_identities": [source_identity],
            },
        }
        receipt: dict[str, object] = {
            "prompt_version": audit_repository.REQUIRED_SOURCE_RECORD_PROMPT_VERSION,
            "source_coverage_mode": audit_repository.NAMED_THEORETICAL_STATEMENTS,
            "configured_review_rows": [
                {
                    "qualified_declaration": spec,
                    "source_file": str(interface.resolve()),
                    "source_sha256": hashlib.sha256(interface.read_bytes()).hexdigest(),
                    "elaborated_signature_sha256": spec_signature_sha,
                    "lean_source_declaration": spec_source,
                },
                {
                    "qualified_declaration": direct,
                    "source_file": str(proof_interface.resolve()),
                    "source_sha256": hashlib.sha256(
                        proof_interface.read_bytes()
                    ).hexdigest(),
                    "elaborated_signature_sha256": direct_signature_sha,
                    "lean_source_declaration": direct_source,
                },
            ],
            "expected_semantic_model_judgment_keys": [
                "semantic-model::theorem-one"
            ],
            "semantic_model_items": [semantic_item],
        }
        source_record_integrity.stamp_source_record_audit_receipts(receipt)
        (audit / "source_record_audit.json").write_text(
            json.dumps(receipt), encoding="utf-8"
        )
        status: dict[str, object] = {
            "review_surface": {"semantic_model_review": {"schema": 2}},
            "formalization_scope": {"target_result_declarations": [direct]},
        }
        return status, declaration_index, declarations, receipt

    @staticmethod
    def persist(folder: Path, receipt: dict[str, object]) -> None:
        source_record_integrity.stamp_source_record_audit_receipts(receipt)
        (folder / "audit" / "source_record_audit.json").write_text(
            json.dumps(receipt), encoding="utf-8"
        )

    def test_exact_proof_endpoint_projects_to_transparent_spec(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "FixturePaper"
            status, declaration_index, declarations, _receipt = self.write_fixture(folder)
            direct = "Fixture.ProofInterface.sourceSpec_proof"
            spec = "Fixture.PaperInterface.sourceSpec"
            unreviewed = "Fixture.PaperInterface.unreviewed"
            surface, error = audit_repository.current_named_theory_semantic_review_surface(
                folder, status, declaration_index
            )
            direct_matches = (
                audit_repository.declaration_is_on_current_named_theory_semantic_review_surface(
                    declarations[direct], surface
                )
            )
            spec_matches = (
                audit_repository.declaration_is_on_current_named_theory_semantic_review_surface(
                    declarations[spec], surface
                )
            )
            unreviewed_matches = (
                audit_repository.declaration_is_on_current_named_theory_semantic_review_surface(
                    declarations[unreviewed], surface
                )
            )

        self.assertEqual(error, "")
        self.assertIsNotNone(surface)
        assert surface is not None
        self.assertEqual(set(surface.rows), {spec})
        self.assertFalse(direct_matches)
        self.assertTrue(spec_matches)
        self.assertFalse(unreviewed_matches)

    def test_spec_declaration_hash_mismatch_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "FixturePaper"
            status, declaration_index, _declarations, receipt = self.write_fixture(folder)
            item = receipt["semantic_model_items"][0]  # type: ignore[index]
            members = item["semantic_contract_group"]["member_rows"]  # type: ignore[index]
            spec_member = next(
                member for member in members if member["role"] == "transparent_spec"
            )
            spec_member["reviewed_declaration_identity"]["declaration_sha256"] = "0" * 64
            self.persist(folder, receipt)
            surface, error = audit_repository.current_named_theory_semantic_review_surface(
                folder, status, declaration_index
            )

        self.assertIsNone(surface)
        self.assertIn("transparent Spec lacks a complete", error)

    def test_spec_source_byte_drift_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "FixturePaper"
            status, declaration_index, _declarations, _receipt = self.write_fixture(folder)
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                interface.read_text(encoding="utf-8") + "\n-- later edit\n",
                encoding="utf-8",
            )
            surface, error = audit_repository.current_named_theory_semantic_review_surface(
                folder, status, declaration_index
            )

        self.assertIsNone(surface)
        self.assertIn("transparent Spec receipt source bytes are stale", error)


if __name__ == "__main__":
    unittest.main()
