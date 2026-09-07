from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import audit_evidence_integrity as integrity
from scripts import audit_repository as repository
from scripts import issue_source_spec_correspondence as issuer
from scripts import refresh_source_spec_correspondence as refresh


class SourceSpecCorrespondenceScreeningTests(unittest.TestCase):
    def setUp(self) -> None:
        self.specification = "Fixture.PaperInterface.claimSpec"
        self.source_map = {
            "paper": "Fixture",
            "items": {
                "claim": {
                    "source_kind": "theorem",
                    "coverage_status": "corrected_source_statement",
                    "semantic_contract": {
                        "spec_declaration": self.specification,
                        "evidence_declaration": "Fixture.claim",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                    "corrected_target": {
                        "archival_equivalence_claimed": False,
                        "corrected_target_sha256": "a" * 64,
                    },
                }
            }
        }

    def test_issuer_uses_one_canonical_audit_module_identity(self) -> None:
        self.assertIs(issuer.integrity, integrity)
        self.assertIs(issuer.repository, repository)
        self.assertIs(issuer.refresh, refresh)

    def test_atomic_write_preserves_unicode_source_text(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "paper_statement_map.json"
            issuer.atomic_write(path, {"quoted_text": "∀ x ∈ X, ‖x‖ ≤ 1"})
            encoded = path.read_text(encoding="utf-8")
            self.assertIn("∀ x ∈ X, ‖x‖ ≤ 1", encoded)
            self.assertNotIn("\\u2200", encoded)

    def test_corrected_target_screening_can_issue_a_realization_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            with mock.patch.object(
                issuer.review_surface,
                "load_current_v11_review_graph_projection",
                return_value=SimpleNamespace(
                    semantic_targets={self.specification: {"display": "True"}}
                ),
            ), mock.patch.object(
                issuer.review_surface,
                "current_v11_screening_rows",
                return_value={
                    self.specification: {
                        "current": True,
                        "judgment": "matches_approved_corrected_target",
                    }
                },
            ), mock.patch.object(
                issuer.integrity,
                "corrected_source_statement_map_findings",
                return_value=[],
            ):
                self.assertEqual(
                    issuer.current_matching_screening(
                        folder, self.source_map, self.specification
                    ),
                    "",
                )

    def test_ordinary_matches_is_rejected_for_a_corrected_target(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            with mock.patch.object(
                issuer.review_surface,
                "load_current_v11_review_graph_projection",
                return_value=SimpleNamespace(
                    semantic_targets={self.specification: {"display": "True"}}
                ),
            ), mock.patch.object(
                issuer.review_surface,
                "current_v11_screening_rows",
                return_value={
                    self.specification: {"current": True, "judgment": "matches"}
                },
            ):
                # The issuer repeats this fail-closed check rather than
                # trusting a caller to have used the packet helper correctly.
                self.assertIn(
                    "requires approved-corrected-target",
                    issuer.current_matching_screening(
                        folder, self.source_map, self.specification
                    ),
                )

    def test_shared_semantic_target_avoids_per_item_lean_rebuild(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            target = {self.specification: {"display": "True"}}
            with mock.patch.object(
                issuer.review_surface,
                "load_current_v11_review_graph_projection",
                side_effect=AssertionError("graph loader ignored shared target"),
            ), mock.patch.object(
                issuer.review_surface,
                "current_v11_screening_rows",
                return_value={
                    self.specification: {
                        "current": True,
                        "judgment": "matches_approved_corrected_target",
                    }
                },
            ) as screening_rows, mock.patch.object(
                issuer.integrity,
                "corrected_source_statement_map_findings",
                return_value=[],
            ):
                self.assertEqual(
                    issuer.current_matching_screening(
                        folder,
                        self.source_map,
                        self.specification,
                        semantic_targets_override=target,
                    ),
                    "",
                )
            screening_rows.assert_called_once_with(
                folder, self.source_map, target
            )

    def test_current_graph_uses_selected_routes_not_every_interface_spec(
        self,
    ) -> None:
        """Definition cards outside the result surface cannot defeat graph reuse."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            route_by_specification = {
                self.specification: SimpleNamespace(source_item_id="claim")
            }
            graph_target = {"display": "True"}
            with (
                mock.patch.object(
                    issuer.review_surface,
                    "load_current_v11_review_graph_projection",
                    return_value=SimpleNamespace(
                        semantic_targets={self.specification: graph_target}
                    ),
                ) as load_graph,
                mock.patch.object(
                    issuer.review_surface,
                    "current_v11_screening_rows",
                    return_value={
                        self.specification: {
                            "current": True,
                            "judgment": "matches_approved_corrected_target",
                        }
                    },
                ),
                mock.patch.object(
                    issuer.integrity,
                    "corrected_source_statement_map_findings",
                    return_value=[],
                ),
            ):
                self.assertEqual(
                    issuer.current_matching_screening(
                        folder,
                        self.source_map,
                        self.specification,
                        route_by_specification=route_by_specification,
                    ),
                    "",
                )

        load_graph.assert_called_once_with(issuer.ROOT, folder)

    def test_missing_current_graph_fails_closed_without_packet_or_lean_fallback(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            with mock.patch.object(
                issuer.review_surface,
                "load_current_v11_review_graph_projection",
                return_value=None,
            ):
                error = issuer.current_matching_screening(
                    folder, self.source_map, self.specification
                )

        self.assertIn("current Lean review graph checkpoint is unavailable", error)

    def test_multi_atom_review_requires_and_preserves_overlap_justification(
        self,
    ) -> None:
        atom_ids = {"source.atom.one", "source.atom.two"}
        ledger = {
            "schema": issuer.REVIEW_SCHEMA,
            "paper": "Fixture",
            "audit_kind": "direct_source_to_expanded_spec_reissue",
            "validator": "fixture reviewer",
            "validated_at": "2026-08-25T00:00:00Z",
            "items": {
                "claim": {
                    "spec_declaration": self.specification,
                    "source_atom_bindings": [
                        {
                            "source_atom_id": atom_id,
                            "semantic_bridge": (
                                "The exact source atom is present in the complete "
                                "expanded proposition with the same conditions and result."
                            ),
                        }
                        for atom_id in sorted(atom_ids)
                    ],
                    "closure_terminal_disposition": {
                        "source_atom_id": "source.atom.one",
                        "semantic_basis": {
                            "artifact_path": "source.txt",
                            "artifact_sha256": "a" * 64,
                            "source_locator": "source.txt:1-2",
                            "semantic_statement": "The exact source supplies the checked terminal.",
                        },
                    },
                }
            },
        }
        _review, missing = issuer.checked_review(
            ledger,
            paper="Fixture",
            key="claim",
            specification=self.specification,
            atom_ids=atom_ids,
        )
        self.assertTrue(any("overlap_justification" in error for error in missing))

        for binding in ledger["items"]["claim"]["source_atom_bindings"]:
            binding["overlap_justification"] = (
                "Both independently identified source clauses occur in one "
                "conjunctive expanded Spec; the complete surface is intentionally "
                "shared, while each semantic bridge identifies its distinct clause."
            )
        review, errors = issuer.checked_review(
            ledger,
            paper="Fixture",
            key="claim",
            specification=self.specification,
            atom_ids=atom_ids,
        )
        self.assertEqual(errors, [])
        assert review is not None

        item = {
            "semantic_contract": {
                "spec_declaration": self.specification,
                "evidence_declaration": "Fixture.claim",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
            "source_claim_atoms": [
                {"id": atom_id} for atom_id in sorted(atom_ids)
            ],
        }
        closure = {
            "surface_sha256": "b" * 64,
            "sha256": "c" * 64,
            "nodes": [],
        }
        with (
            mock.patch.object(
                issuer.integrity,
                "source_claim_atoms_validation_errors",
                return_value=[],
            ),
            mock.patch.object(
                issuer.integrity,
                "source_claim_atom_semantic_sha256",
                side_effect=lambda atom: (
                    "d" * 64 if atom["id"].endswith("one") else "e" * 64
                ),
            ),
            mock.patch.object(
                issuer.integrity,
                "source_claim_atoms_semantic_sha256",
                return_value="f" * 64,
            ),
            mock.patch.object(
                issuer.integrity,
                "source_spec_correspondence_item_identity_sha256",
                return_value="1" * 64,
            ),
            mock.patch.object(
                issuer.integrity,
                "source_spec_correspondence_validation_errors",
                return_value=[],
            ),
            mock.patch.object(
                issuer.repository,
                "semantic_contract_closure_environment_sha256",
                return_value="2" * 64,
            ),
            mock.patch.object(
                issuer.repository,
                "_realization_required_node_components",
                return_value=(set(), []),
            ),
            mock.patch.object(
                issuer.repository,
                "source_spec_correspondence_runtime_errors",
                return_value=[],
            ),
        ):
            record, record_errors = issuer.correspondence(item, review, closure)
        self.assertEqual(record_errors, [])
        assert record is not None
        self.assertEqual(
            [
                binding.get("overlap_justification")
                for binding in record["source_atom_bindings"]
            ],
            [
                ledger["items"]["claim"]["source_atom_bindings"][0][
                    "overlap_justification"
                ],
                ledger["items"]["claim"]["source_atom_bindings"][1][
                    "overlap_justification"
                ],
            ],
        )


if __name__ == "__main__":
    unittest.main()
