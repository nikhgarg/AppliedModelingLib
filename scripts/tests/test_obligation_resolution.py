from __future__ import annotations

import copy
import hashlib
import unittest
from unittest import mock

from scripts.obligation_evidence_projection import (
    project_semantic_prerequisite_leaves_from_validated_inputs,
)
from scripts.obligation_evidence_issuance import (
    LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256,
)
from scripts.obligation_resolution import (
    accepted_review_targets_bound_to_current_lean_leaves,
    bind_current_semantic_prerequisite_judgments,
    plan_semantic_prerequisite_resolution,
    semantic_prerequisite_coordinates,
)
from scripts.corrected_target_identity import CORRECTED_TARGET_REVIEW_PROTOCOL
from scripts.tests.test_obligation_evidence_projection import (
    load_prerequisite_inputs,
)

class ObligationResolutionTests(unittest.TestCase):
    def current_plan(self):
        source, paper, library, manifests, transaction = load_prerequisite_inputs()
        projection = project_semantic_prerequisite_leaves_from_validated_inputs(
            source_map=source,
            paper_prerequisites=paper,
            library_semantic_review=library,
            manifest_authority=manifests,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
            ),
        )
        resolved = {
            declaration: route["lean_declaration_leaf_sha256"]
            for declaration, route in projection.navigation.items()
        }
        return paper, library, resolved

    def one_row_rebind_inputs(self):
        paper, library, _resolved = self.current_plan()
        paper = copy.deepcopy(paper)
        library = copy.deepcopy(library)
        declaration, row = next(iter(paper["items"].items()))
        paper["items"] = {declaration: row}
        library["items"] = {}
        source = {
            row["source_item"]: {
                "source_input_bundle_sha256": row[
                    "source_input_bundle_sha256"
                ],
                "source_atom_leaf_sha256s": [
                    hashlib.sha256(row["source_item"].encode()).hexdigest()
                ],
            }
        }
        lean = {
            declaration: {
                "reviewed_semantic_target_sha256": row[
                    "paper_semantic_target_sha256"
                ],
                "current_declaration_content_sha256": row[
                    "paper_declaration_sha256"
                ],
                "current_lean_declaration_leaf_sha256": hashlib.sha256(
                    declaration.encode()
                ).hexdigest(),
            }
        }
        return paper, library, source, lean, declaration

    def test_current_im05_reuses_all_reviewed_prerequisite_identities(self) -> None:
        paper, library, resolved = self.current_plan()
        with mock.patch("subprocess.run", side_effect=AssertionError("producer invoked")):
            plan = plan_semantic_prerequisite_resolution(
                paper_prerequisites=paper,
                library_semantic_review=library,
                resolved_leaf_sha256_by_declaration=resolved,
            )
        self.assertEqual(len(plan.items), 45)
        self.assertEqual(len(plan.resolved), 45)
        self.assertEqual(len(plan.unresolved), 0)
        self.assertTrue(all(item.action == "reuse_leaf" for item in plan.resolved))

    def test_prompt_reason_path_and_line_changes_do_not_change_coordinates(self) -> None:
        paper, library, resolved = self.current_plan()
        baseline = plan_semantic_prerequisite_resolution(
            paper_prerequisites=paper,
            library_semantic_review=library,
            resolved_leaf_sha256_by_declaration=resolved,
        )
        changed_paper = copy.deepcopy(paper)
        changed_library = copy.deepcopy(library)
        for ledger in (changed_paper, changed_library):
            ledger["prompt_version"] = "new prompt prose"
            ledger["comment"] = "new explanation"
            for row in ledger["items"].values():
                row["reason"] = "rewritten reason"
                row["validator"] = "different reviewer label"
                for field in (
                    "paper_source_path",
                    "library_source_path",
                ):
                    if field in row:
                        row[field] = "Moved/File.lean"
                for field in (
                    "paper_line_start",
                    "library_line_start",
                    "library_line_end",
                ):
                    if field in row:
                        row[field] = 999
        changed = plan_semantic_prerequisite_resolution(
            paper_prerequisites=changed_paper,
            library_semantic_review=changed_library,
            resolved_leaf_sha256_by_declaration=resolved,
        )
        self.assertEqual(
            [item.coordinate.coordinate_sha256 for item in changed.items],
            [item.coordinate.coordinate_sha256 for item in baseline.items],
        )

    def test_changed_exact_target_changes_only_its_coordinate(self) -> None:
        paper, library, resolved = self.current_plan()
        baseline = plan_semantic_prerequisite_resolution(
            paper_prerequisites=paper,
            library_semantic_review=library,
            resolved_leaf_sha256_by_declaration=resolved,
        )
        changed_library = copy.deepcopy(library)
        changed_name = next(iter(changed_library["items"]))
        changed_library["items"][changed_name][
            "library_semantic_target_sha256"
        ] = "f" * 64
        changed = plan_semantic_prerequisite_resolution(
            paper_prerequisites=paper,
            library_semantic_review=changed_library,
            resolved_leaf_sha256_by_declaration=resolved,
        )
        baseline_by_name = {
            item.coordinate.declaration: item.coordinate.coordinate_sha256
            for item in baseline.items
        }
        changed_by_name = {
            item.coordinate.declaration: item.coordinate.coordinate_sha256
            for item in changed.items
        }
        self.assertEqual(
            [
                name
                for name in baseline_by_name
                if baseline_by_name[name] != changed_by_name[name]
            ],
            [changed_name],
        )

    def test_lean_private_name_is_an_opaque_graph_coordinate(self) -> None:
        paper, library, _resolved = self.current_plan()
        paper = copy.deepcopy(paper)
        _original_name, row = next(iter(paper["items"].items()))
        private_name = "_private.Fixture.Module.0.Fixture.privateValue"
        row["paper_declaration"] = private_name
        paper["items"] = {private_name: row}
        library["items"] = {}

        coordinates = semantic_prerequisite_coordinates(
            paper_prerequisites=paper,
            library_semantic_review=library,
        )

        self.assertEqual(set(coordinates), {private_name})
        self.assertEqual(coordinates[private_name].declaration, private_name)

    def test_lean_coordinate_rejects_transport_control_characters(self) -> None:
        paper, library, _resolved = self.current_plan()
        paper = copy.deepcopy(paper)
        _original_name, row = next(iter(paper["items"].items()))
        invalid_name = "Fixture.bad\nname"
        row["paper_declaration"] = invalid_name
        paper["items"] = {invalid_name: row}
        library["items"] = {}

        with self.assertRaisesRegex(
            ValueError, "transport control character"
        ):
            semantic_prerequisite_coordinates(
                paper_prerequisites=paper,
                library_semantic_review=library,
            )

    def test_exact_current_material_rebinds_accepted_judgment_without_producer(self) -> None:
        paper, library, source, lean, declaration = self.one_row_rebind_inputs()
        with mock.patch("subprocess.run", side_effect=AssertionError("producer invoked")):
            plan = bind_current_semantic_prerequisite_judgments(
                paper_prerequisites=paper,
                library_semantic_review=library,
                current_source_material_by_item=source,
                current_lean_material_by_declaration=lean,
                issuance_authority_sha256="a" * 64,
            )
        self.assertTrue(plan.projection()["complete"])
        self.assertEqual(len(plan.reused), 1)
        item = plan.reused[0]
        self.assertEqual(item.coordinate.declaration, declaration)
        self.assertIsNotNone(item.judgment_leaf)
        self.assertIsNotNone(item.issuance)
        self.assertEqual(
            item.judgment_leaf.semantic_payload["lean_declaration_sha256"],
            lean[declaration]["current_lean_declaration_leaf_sha256"],
        )

    def test_accepted_target_binds_to_current_leaf_without_display_renderer(self) -> None:
        paper, library, _source, lean, declaration = self.one_row_rebind_inputs()
        coordinates = semantic_prerequisite_coordinates(
            paper_prerequisites=paper,
            library_semantic_review=library,
        )
        with mock.patch("subprocess.run", side_effect=AssertionError("renderer invoked")):
            bindings = accepted_review_targets_bound_to_current_lean_leaves(
                coordinates=coordinates,
                declaration_content_sha256_by_declaration={
                    declaration: lean[declaration][
                        "current_declaration_content_sha256"
                    ]
                },
                lean_declaration_leaf_sha256_by_declaration={
                    declaration: lean[declaration][
                        "current_lean_declaration_leaf_sha256"
                    ]
                },
            )
        self.assertEqual(
            bindings[declaration].reviewed_semantic_target_sha256,
            coordinates[declaration].expected_display_sha256,
        )

    def test_approved_corrected_target_is_a_distinct_accepted_leaf(self) -> None:
        paper, library, source, lean, declaration = self.one_row_rebind_inputs()
        row = paper["items"][declaration]
        row.update(
            {
                "judgment": "matches_approved_corrected_target",
                "corrected_target_protocol": CORRECTED_TARGET_REVIEW_PROTOCOL,
                "corrected_target_review_sha256": "c" * 64,
            }
        )
        plan = bind_current_semantic_prerequisite_judgments(
            paper_prerequisites=paper,
            library_semantic_review=library,
            current_source_material_by_item=source,
            current_lean_material_by_declaration=lean,
            issuance_authority_sha256="a" * 64,
        )
        self.assertEqual(len(plan.reused), 1)
        self.assertEqual(
            plan.reused[0].judgment_leaf.semantic_payload["verdict"],
            "matches_approved_corrected_target",
        )

    def test_navigation_and_explanation_edit_changes_only_rebind_issuance(self) -> None:
        paper, library, source, lean, declaration = self.one_row_rebind_inputs()
        baseline = bind_current_semantic_prerequisite_judgments(
            paper_prerequisites=paper,
            library_semantic_review=library,
            current_source_material_by_item=source,
            current_lean_material_by_declaration=lean,
            issuance_authority_sha256="a" * 64,
        ).reused[0]
        changed = copy.deepcopy(paper)
        row = changed["items"][declaration]
        row["reason"] = "rewritten reviewer explanation"
        row["paper_source_path"] = "Moved/File.lean"
        row["paper_line_start"] = 999
        rebound = bind_current_semantic_prerequisite_judgments(
            paper_prerequisites=changed,
            library_semantic_review=library,
            current_source_material_by_item=source,
            current_lean_material_by_declaration=lean,
            issuance_authority_sha256="a" * 64,
        ).reused[0]
        self.assertEqual(
            rebound.judgment_leaf.leaf_sha256,
            baseline.judgment_leaf.leaf_sha256,
        )
        self.assertNotEqual(
            rebound.issuance.issuance_sha256,
            baseline.issuance.issuance_sha256,
        )

    def test_missing_current_lean_material_schedules_only_materialization(self) -> None:
        paper, library, source, _lean, declaration = self.one_row_rebind_inputs()
        item = bind_current_semantic_prerequisite_judgments(
            paper_prerequisites=paper,
            library_semantic_review=library,
            current_source_material_by_item=source,
            current_lean_material_by_declaration={},
            issuance_authority_sha256="a" * 64,
        ).unresolved[0]
        self.assertEqual(item.coordinate.declaration, declaration)
        self.assertEqual(item.action, "materialize_current_review_material")

    def test_changed_exact_comparison_schedules_only_that_semantic_review(self) -> None:
        paper, library, source, lean, declaration = self.one_row_rebind_inputs()
        changed_lean = copy.deepcopy(lean)
        changed_lean[declaration]["reviewed_semantic_target_sha256"] = "f" * 64
        item = bind_current_semantic_prerequisite_judgments(
            paper_prerequisites=paper,
            library_semantic_review=library,
            current_source_material_by_item=source,
            current_lean_material_by_declaration=changed_lean,
            issuance_authority_sha256="a" * 64,
        ).unresolved[0]
        self.assertEqual(item.action, "run_semantic_review")
        self.assertIn("reviewed Lean semantic target", item.reason)


if __name__ == "__main__":
    unittest.main()
