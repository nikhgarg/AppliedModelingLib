#!/usr/bin/env python3
"""Tests for acceptance-neutral generated paper-status metadata."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.closeout_status_projection import (
    CloseoutStatusProjectionError,
    graph_native_human_review_total,
    graph_native_human_review_total_from_payload,
    paper_status_acceptance_projection,
    paper_status_assurance_control_projection_from_payload,
    refresh_derived_paper_status_metadata,
)


class CloseoutStatusProjectionTests(unittest.TestCase):
    def test_terminal_status_controls_exclude_prose_and_visibility(self) -> None:
        payload = {
            "id": "Fixture",
            "status": "formalized",
            "main_caveat": "old reader prose",
            "human_summary": "old summary",
            "repository_visibility": "private",
            "review_surface": {"assumption_policy": "strict"},
        }
        expected = paper_status_assurance_control_projection_from_payload(
            "Fixture", payload
        )
        changed = dict(payload)
        changed.update(
            main_caveat="new reader prose",
            human_summary="new summary",
            repository_visibility="public",
        )
        self.assertEqual(
            paper_status_assurance_control_projection_from_payload(
                "Fixture", changed
            ),
            expected,
        )
        for field, value in (
            ("status", "partially_formalized"),
            ("review_surface", {"assumption_policy": "permissive"}),
        ):
            with self.subTest(field=field):
                semantic_change = dict(payload)
                semantic_change[field] = value
                self.assertNotEqual(
                    paper_status_assurance_control_projection_from_payload(
                        "Fixture", semantic_change
                    ),
                    expected,
                )

    def test_every_current_opt_in_uses_typed_human_denominator(self) -> None:
        cases = (
            ({"require_source_spec_correspondence": True}, {}),
            ({"require_v11_raw_source_spec_screening": True}, {}),
            ({"llm_statement_review": {"require_theorem_realization_contract_schema": 1}}, {}),
            ({}, {"source_spec_correspondence_schema": 1}),
        )
        for opt_in, source_map in cases:
            with self.subTest(opt_in=opt_in, source_map=source_map):
                payload = {"review_surface": {**opt_in, "include_names": ["claimSpec"]}}
                with mock.patch(
                    "scripts.closeout_status_projection.EvidenceRouteSet.from_source_map"
                ) as routes:
                    routes.return_value.human_review_source_items.return_value = ("claim",)
                    self.assertEqual(graph_native_human_review_total_from_payload(source_map, payload), 1)
                    routes.assert_called_once_with(source_map)

    def test_correspondence_only_missing_source_map_is_not_legacy(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            payload = {"review_surface": {"require_source_spec_correspondence": True}}
            with self.assertRaisesRegex(CloseoutStatusProjectionError, "could not read graph-native"):
                graph_native_human_review_total(Path(temp_dir), "Fixture", payload)

    @staticmethod
    def make_paper(root: Path) -> Path:
        folder = root / "papers" / "Fixture"
        folder.mkdir(parents=True)
        (folder / "PaperInterface.lean").write_text(
            "def modelSpec : Prop := True\n\n"
            "theorem model : modelSpec := by trivial\n",
            encoding="utf-8",
        )
        (folder / "status.json").write_text(
            json.dumps(
                {
                    "id": "Fixture",
                    "status": "formalized",
                    "paper_interface": {
                        "line_count": 999,
                        "declaration_rows": 999,
                        "review_rows": 999,
                        "file": "papers/Fixture/PaperInterface.lean",
                    },
                    "review_surface": {"include_names": ["modelSpec"]},
                    "human_review": {
                        "reviewed_rows": 0,
                        "total_rows": 999,
                        "stale_rows": 0,
                    },
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
        return folder

    def test_derived_counts_are_not_acceptance_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            before = paper_status_acceptance_projection(root, "Fixture")
            payload = json.loads((folder / "status.json").read_text(encoding="utf-8"))
            payload["paper_interface"]["line_count"] = 1
            payload["paper_interface"]["declaration_rows"] = 2
            payload["paper_interface"]["review_rows"] = 1
            payload["paper_interface"]["maintainability_issue"] = "display only"
            payload["human_review"]["reviewed_rows"] = 1
            payload["human_review"]["total_rows"] = 10_000
            (folder / "status.json").write_text(
                json.dumps(payload, indent=2) + "\n", encoding="utf-8"
            )
            self.assertEqual(
                paper_status_acceptance_projection(root, "Fixture"), before
            )

            payload["review_surface"]["include_names"] = ["modelSpec", "model"]
            (folder / "status.json").write_text(
                json.dumps(payload, indent=2) + "\n", encoding="utf-8"
            )
            self.assertNotEqual(
                paper_status_acceptance_projection(root, "Fixture"), before
            )

    def test_final_refresh_updates_counts_without_changing_projection(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            before = paper_status_acceptance_projection(root, "Fixture")
            self.assertTrue(refresh_derived_paper_status_metadata(root, "Fixture"))
            payload = json.loads((folder / "status.json").read_text(encoding="utf-8"))
            self.assertEqual(payload["paper_interface"]["line_count"], 3)
            self.assertEqual(payload["paper_interface"]["declaration_rows"], 999)
            self.assertEqual(payload["paper_interface"]["review_rows"], 1)
            self.assertEqual(payload["human_review"]["total_rows"], 999)
            self.assertEqual(
                paper_status_acceptance_projection(root, "Fixture"), before
            )
            self.assertFalse(refresh_derived_paper_status_metadata(root, "Fixture"))

    def test_graph_native_refresh_counts_exact_source_items_and_conditions(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            payload = json.loads((folder / "status.json").read_text(encoding="utf-8"))
            payload["review_surface"].update(
                {
                    "require_v11_raw_source_spec_screening": True,
                    "source_condition_items": ["condition"],
                }
            )
            (folder / "status.json").write_text(
                json.dumps(payload, indent=2) + "\n", encoding="utf-8"
            )
            audit = folder / "audit"
            audit.mkdir()
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "claim": {
                                "source_kind": "theorem",
                                "semantic_contract": {
                                    "spec_declaration": "Fixture.modelSpec",
                                    "evidence_declaration": "Fixture.model",
                                    "evidence_mode": "proves",
                                    "semantic_shape": "plain",
                                },
                            },
                            "condition": {
                                "source_kind": "condition",
                                "inventory_role": "source_semantic_declaration",
                                "lean_declarations": ["Fixture.ModelCondition"],
                            },
                        }
                    },
                    indent=2,
                )
                + "\n",
                encoding="utf-8",
            )

            self.assertEqual(
                graph_native_human_review_total(root, "Fixture", payload), 2
            )
            self.assertTrue(refresh_derived_paper_status_metadata(root, "Fixture"))
            refreshed = json.loads(
                (folder / "status.json").read_text(encoding="utf-8")
            )
            self.assertEqual(refreshed["human_review"]["total_rows"], 2)

    def test_projection_rejects_a_status_owned_by_another_paper(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            payload = json.loads((folder / "status.json").read_text(encoding="utf-8"))
            payload["id"] = "Other"
            (folder / "status.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            with self.assertRaisesRegex(CloseoutStatusProjectionError, "another paper"):
                paper_status_acceptance_projection(root, "Fixture")


if __name__ == "__main__":
    unittest.main()
