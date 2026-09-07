#!/usr/bin/env python3
"""Regressions for one content-pinned appendix-aware review scope."""

from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path

from scripts.source_coverage_scope import (
    source_prose_definition_presentation_sha256,
)
from scripts.source_review_input import canonical_source_anchor_evidence
from scripts.source_review_scope import (
    current_closeout_review_policy_errors,
    current_source_region_partition_errors,
    materialize_source_region_partition,
    primary_source_region_projection,
    source_region_partition_projection,
)


class SourceReviewScopeTests(unittest.TestCase):
    def materialized_fixture(
        self,
        root: Path,
        *,
        main_definition: str = "Definition. A model is a set.",
        appendix_result: str = "Lemma A. The auxiliary claim holds.",
        promote_appendix: bool = False,
    ) -> tuple[Path, dict[str, object]]:
        folder = root / "papers" / "FixturePaper"
        folder.mkdir(parents=True)
        source_text = "\n".join(
            (
                "Fixture paper",
                main_definition,
                "Theorem 1. The main claim holds.",
                "Appendix A",
                appendix_result,
            )
        ) + "\n"
        source_path = folder / "source.txt"
        source_path.write_text(source_text, encoding="utf-8")

        def one_anchor(line: int) -> dict[str, object]:
            return canonical_source_anchor_evidence(
                folder, f"source.txt:{line}"
            )[0]

        prose = {
            "presentation_kind": "definition",
            "defined_entity_kind": "model",
            "defined_object": "fixture model",
            "definitional_clause": main_definition,
            "scope_disposition": "normal_theory",
            "source_anchor": one_anchor(2),
        }
        candidates = [
            {
                "id": "main_result",
                "source_anchor": one_anchor(3),
            },
            {
                "id": "appendix_result",
                "source_anchor": one_anchor(5),
            },
        ]
        source_map: dict[str, object] = {
            "paper": "FixturePaper",
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": hashlib.sha256(
                source_text.encode("utf-8")
            ).hexdigest(),
            "items": {
                "model": {"source_anchor_evidence": [one_anchor(2)]},
                "main": {"source_anchor_evidence": [one_anchor(3)]},
                "appendix": {"source_anchor_evidence": [one_anchor(5)]},
            },
            "source_named_result_inventory_review": {
                "complete": True,
                "candidate_presentations": candidates,
                "prose_definition_presentations": [prose],
            },
        }
        prose_digest = source_prose_definition_presentation_sha256(prose)
        approval = {
            "schema": 1,
            "approval_kind": "explicit_user_instruction",
            "approval_reference": "User explicitly promoted the appendix lemma.",
            "approved_at": "2026-09-05T12:00:00Z",
        }
        plan = {
            "complete": True,
            "validator": "fixture curator",
            "method": "complete source partition",
            "validated_at": "2026-09-05T12:00:00Z",
            "regions": [
                {"id": "main", "kind": "main_text", "source_locator": "source.txt:1-3"},
                {"id": "appendix", "kind": "appendix", "source_locator": "source.txt:4-5"},
            ],
            "source_item_regions": {
                "model": "main",
                "main": "main",
                "appendix": "appendix",
            },
            "candidate_presentation_regions": {
                "main_result": "main",
                "appendix_result": "appendix",
            },
            "prose_definition_presentation_regions": {"model_definition": "main"},
            "promoted_source_items": (
                [
                    {
                        "source_item": "appendix",
                        "reason": "This appendix lemma governs the main result.",
                        "approval": approval,
                    }
                ]
                if promote_appendix
                else []
            ),
        }
        partition = materialize_source_region_partition(
            folder,
            source_map,
            plan,
            candidate_presentations=candidates,
            prose_presentations=[prose],
            prose_presentation_sha256_by_id={
                "model_definition": prose_digest,
            },
        )
        source_map["source_named_result_inventory_review"][
            "source_region_partition"
        ] = partition
        return folder, source_map

    def test_materialized_partition_is_complete_and_current(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, source_map = self.materialized_fixture(Path(tmp))
            self.assertEqual(
                current_source_region_partition_errors(folder, source_map), []
            )
            projection = source_region_partition_projection(source_map)
            self.assertEqual(
                [row["id"] for row in projection["regions"]],
                ["main", "appendix"],
            )

    def test_gap_or_ambiguous_assignment_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, source_map = self.materialized_fixture(Path(tmp))
            review = source_map["source_named_result_inventory_review"]
            partition = review["source_region_partition"]
            partition["regions"][1]["source_anchor"]["line_start"] = 5
            self.assertIn(
                "source regions overlap or leave an ambiguous boundary",
                current_source_region_partition_errors(folder, source_map),
            )

        with tempfile.TemporaryDirectory() as tmp:
            folder, source_map = self.materialized_fixture(Path(tmp))
            partition = source_map["source_named_result_inventory_review"][
                "source_region_partition"
            ]
            partition["source_item_regions"]["appendix"] = "main"
            self.assertTrue(
                any(
                    "appendix" in error and "assigned region" in error
                    for error in current_source_region_partition_errors(
                        folder, source_map
                    )
                )
            )

    def test_appendix_bytes_do_not_change_primary_review_material(self) -> None:
        with tempfile.TemporaryDirectory() as first_tmp, tempfile.TemporaryDirectory() as second_tmp:
            _first_folder, first = self.materialized_fixture(Path(first_tmp))
            _second_folder, second = self.materialized_fixture(
                Path(second_tmp),
                appendix_result="Lemma A. A materially changed auxiliary claim holds.",
            )
            self.assertNotEqual(
                source_region_partition_projection(first),
                source_region_partition_projection(second),
            )
            self.assertEqual(
                primary_source_region_projection(first),
                primary_source_region_projection(second),
            )

    def test_main_bytes_and_explicit_promotion_change_primary_material(self) -> None:
        with tempfile.TemporaryDirectory() as first_tmp, tempfile.TemporaryDirectory() as second_tmp, tempfile.TemporaryDirectory() as third_tmp:
            _first_folder, first = self.materialized_fixture(Path(first_tmp))
            _second_folder, changed_main = self.materialized_fixture(
                Path(second_tmp),
                main_definition="Definition. A model is a nonempty set.",
            )
            _third_folder, promoted = self.materialized_fixture(
                Path(third_tmp), promote_appendix=True
            )
            primary = primary_source_region_projection(first)
            self.assertNotEqual(
                primary, primary_source_region_projection(changed_main)
            )
            self.assertNotEqual(primary, primary_source_region_projection(promoted))

    def test_wrong_prose_region_is_rejected_at_materialization(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, source_map = self.materialized_fixture(Path(tmp))
            review = source_map["source_named_result_inventory_review"]
            partition = review["source_region_partition"]
            partition["prose_definition_presentation_regions"] = {
                next(iter(partition["prose_definition_presentation_regions"])): "appendix"
            }
            self.assertTrue(
                any(
                    "prose-definition" in error and "assigned region" in error
                    for error in current_source_region_partition_errors(
                        folder, source_map
                    )
                )
            )

    def test_one_policy_controls_appendix_exclusions_and_coverage_mode(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, source_map = self.materialized_fixture(Path(tmp))
            source_map["items"]["appendix"].update(
                source_kind="lemma",
                statement="The auxiliary claim holds.",
                claim_bearing=True,
            )
            default_policy = {
                "schema": 1,
                "source_scope": "all_named_theory",
                "repeat_final_scope": "main_primary",
                "required_final_adversary_count": 1,
                "scheduling": {
                    "initial_semantic_review": [],
                    "final_adversarial_review": [],
                },
            }
            source_map["source_coverage_mode"] = "named_theoretical_statements"
            source_map["closeout_review_policy"] = default_policy
            self.assertEqual(
                current_closeout_review_policy_errors(folder, source_map), []
            )

            approval = {
                "schema": 1,
                "approval_kind": "explicit_user_instruction",
                "approval_reference": "User explicitly approved main named theory only.",
                "approved_at": "2026-09-05T12:00:00Z",
            }
            limited = {**default_policy}
            limited.update(
                source_scope="main_named_theory",
                repeat_final_scope="all_selected",
                scope_approval=approval,
            )
            source_map["closeout_review_policy"] = limited
            self.assertTrue(
                any(
                    "requires an exact user-approved appendix exclusion" in error
                    for error in current_closeout_review_policy_errors(
                        folder, source_map
                    )
                )
            )
            source_map["items"]["appendix"]["user_approved_scope_exclusion"] = {
                **approval,
                "reason": "The approved scope excludes appendix named theory.",
                "source_locator": "source.txt:5",
                "source_evidence": "The appendix lemma is outside the approved scope.",
                "source_anchor_quote_sha256": source_map["items"]["appendix"][
                    "source_anchor_evidence"
                ][0]["quoted_text_sha256"],
            }
            self.assertEqual(
                current_closeout_review_policy_errors(folder, source_map), []
            )

            all_prose = {**default_policy}
            all_prose.update(
                source_scope="all_prose", repeat_final_scope="all_selected"
            )
            source_map["closeout_review_policy"] = all_prose
            self.assertTrue(
                any(
                    "requires deep_paper_with_all_prose_claims" in error
                    for error in current_closeout_review_policy_errors(
                        folder, source_map
                    )
                )
            )


if __name__ == "__main__":
    unittest.main()
