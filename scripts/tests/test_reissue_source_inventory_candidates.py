from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import reissue_source_inventory_candidates as reissue
from scripts.current_closeout import planner


class SourceInventoryCandidateReissueTests(unittest.TestCase):
    def _fixture(self, root: Path) -> tuple[Path, dict[str, object]]:
        folder = root / "papers" / "Fixture"
        audit = folder / "audit"
        audit.mkdir(parents=True)
        source = (
            "Remark 1. This observation is explanatory only.\n"
            "Theorem 1. Every admissible run terminates.\n"
        )
        (folder / "source.txt").write_text(source, encoding="utf-8")
        source_sha = hashlib.sha256(source.encode("utf-8")).hexdigest()
        source_map: dict[str, object] = {
            "paper": "Fixture",
            "source_artifact_path": "papers/Fixture/source.txt",
            "source_artifact_sha256": source_sha,
            "source_coverage_mode": "named_theoretical_statements",
            "items": {
                "theorem1": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:2",
                    "claim_bearing": True,
                    "source_anchor_evidence": [
                        {
                            "path": "source.txt",
                            "line_start": 2,
                            "line_end": 2,
                            "quoted_text": "Theorem 1. Every admissible run terminates.",
                            "quoted_text_sha256": hashlib.sha256(
                                b"Theorem 1. Every admissible run terminates."
                            ).hexdigest(),
                        }
                    ],
                }
            },
            "source_named_result_inventory_review": {
                "schema": 1,
                "complete": True,
                "validator": "legacy source reviewer",
                "method": "Read the complete source for ordinary named results.",
                "validated_at": "2026-08-20T00:00:00Z",
                "source_artifact_sha256": source_sha,
                "prose_definition_presentations": [],
                "discovered_prose_definition_sha256": hashlib.sha256(b"[]").hexdigest(),
                "discovered_named_result_sha256": "0" * 64,
            },
        }
        (audit / "paper_statement_map.json").write_text(
            json.dumps(source_map), encoding="utf-8"
        )
        (folder / "status.json").write_text(
            json.dumps({"schema": 1, "status": "formalized"}),
            encoding="utf-8",
        )
        return folder, source_map

    def test_template_discovers_candidates_but_issues_no_judgment(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder, source_map = self._fixture(Path(temporary))
            template = reissue.decision_template(folder, source_map)

        self.assertFalse(template["acceptance_credential"])
        self.assertFalse(template["holistic_source_review_complete"])
        self.assertEqual(len(template["items"]), 1)
        self.assertEqual(
            template["items"][0]["discovery_basis"],
            "mechanical_labelled_heading",
        )
        self.assertEqual(template["items"][0]["scope_disposition"], "")

    def test_complete_queue_migrates_only_the_candidate_inventory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder, source_map = self._fixture(Path(temporary))
            decisions = reissue.decision_template(folder, source_map)
            decisions["holistic_source_review_complete"] = True
            decisions["method"] = "Read the complete pinned source without Lean names."
            decisions["items"][0]["scope_disposition"] = "deep_audit_material"
            decisions["items"][0]["semantic_basis"] = (
                "The remark is explanatory and adds no theorem conclusion."
            )
            migrated, config = reissue.apply_decisions(
                folder,
                decisions,
                validator="fixture source reviewer",
            )

        review = migrated["source_named_result_inventory_review"]
        self.assertIsNone(config)
        self.assertEqual(review["prose_definition_presentations"], [])
        self.assertEqual(len(review["candidate_presentations"]), 1)
        self.assertEqual(
            review["candidate_presentations"][0]["scope_disposition"],
            "deep_audit_material",
        )

    def test_holistic_candidate_normalizes_an_equivalent_source_path(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder, source_map = self._fixture(root)
            decisions = reissue.decision_template(folder, source_map)
            decisions["holistic_source_review_complete"] = True
            decisions["method"] = "Read the complete pinned source without Lean names."
            decisions["items"][0]["scope_disposition"] = "deep_audit_material"
            decisions["items"][0]["semantic_basis"] = (
                "The labelled remark is explanatory and adds no theorem conclusion."
            )
            decisions["items"].append(
                {
                    "id": "holistic_001",
                    "discovery_basis": "holistic_full_text_review",
                    "source_locator": "papers/Fixture/source.txt:2",
                    "presentation_label": "An unnumbered explanatory observation",
                    "visible_kind": "holistic",
                    "scope_disposition": "deep_audit_material",
                    "semantic_basis": "It is unnumbered discussion rather than a selected result.",
                }
            )
            migrated, _config = reissue.apply_decisions(
                folder,
                decisions,
                validator="fixture source reviewer",
            )

        candidates = migrated["source_named_result_inventory_review"][
            "candidate_presentations"
        ]
        self.assertEqual(
            candidates[1]["source_anchor"]["path"],
            "papers/Fixture/source.txt",
        )

    def test_empty_or_partial_queue_cannot_fake_holistic_completion(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder, source_map = self._fixture(Path(temporary))
            decisions = reissue.decision_template(folder, source_map)
            with self.assertRaisesRegex(
                reissue.SourceInventoryCandidateReissueError,
                "reviewed disposition|holistic full-source review",
            ):
                reissue.apply_decisions(
                    folder,
                    decisions,
                    validator="fixture source reviewer",
                )

    def test_planner_schedules_candidate_review_before_lean_graph_work(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder, source_map = self._fixture(root)
            with mock.patch.object(planner, "ROOT", root):
                action = planner.current_source_inventory_candidate_review_action(
                    folder,
                    source_map,
                )

        self.assertIsNotNone(action)
        self.assertEqual(action["id"], "emit_source_inventory_candidate_review_queue")
        self.assertIn("before any Lean graph acquisition", action["reason"])


if __name__ == "__main__":
    unittest.main()
