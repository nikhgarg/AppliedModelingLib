from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import review_dashboard
from scripts.current_closeout import review_surface


class ReviewDashboardInteractiveCacheTests(unittest.TestCase):
    def test_missing_spec_checkpoint_stays_visible_without_lean_discovery(self) -> None:
        specification = "Fixture.claimSpec"
        item = review_dashboard.ReviewItem(
            name="claimSpec",
            kind="def",
            lean_statement="def claimSpec : Prop := True",
            paper_statement="",
            agent_statement="",
            full_name=specification,
            interface_source="def claimSpec : Prop := True",
        )
        source_map = {
            "items": {
                "claim": {
                    "semantic_contract": {
                        "spec_declaration": specification,
                        "evidence_declaration": "Fixture.claim",
                        "evidence_mode": "proves",
                    }
                }
            }
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            with (
                mock.patch.object(
                    review_dashboard,
                    "paper_statement_map_payload",
                    return_value=source_map,
                ),
                mock.patch.object(
                    review_dashboard,
                    "typed_route_validation_required",
                    return_value=False,
                ),
                mock.patch.object(
                    review_surface, "_current_packet_lean_cache", return_value=None
                ),
            ):
                rows = review_dashboard.human_review_claim_items(folder, [item])

        self.assertEqual(len(rows), 1)
        self.assertIn(
            "retained Lean-expanded Spec targets are unavailable",
            rows[0]["semantic_expansion_error"],
        )

    def test_interactive_cache_skips_full_lean_closure_walk(self) -> None:
        """The browser can reuse already-elaborated closeout-era review rows."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "CachedPaper"
            folder.mkdir()
            (folder / "PaperInterface.lean").write_text(
                "theorem endpoint : True := by trivial\n", encoding="utf-8"
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "status": "formalized",
                        "review_surface": {"include_names": ["endpoint"]},
                    }
                ),
                encoding="utf-8",
            )
            cache_path = folder / ".review_traces" / "paper_interface_cache.json"
            cache_path.parent.mkdir()
            hashes = review_dashboard._cache_nonlean_source_hashes(folder)
            hashes["lean_source_closure_sha256"] = "a" * 64
            row = review_dashboard.ReviewItem(
                name="endpoint",
                kind="theorem",
                lean_statement="True",
                paper_statement="",
                agent_statement="",
                full_name="CachedPaper.endpoint",
                interface_source="theorem endpoint : True := by trivial",
            )
            cache_path.write_text(
                json.dumps(
                    {
                        "schema": review_dashboard.PAPER_INTERFACE_CACHE_SCHEMA,
                        "paper": folder.name,
                        "hashes": hashes,
                        "rows": [row.__dict__],
                    }
                ),
                encoding="utf-8",
            )

            with (
                mock.patch.object(
                    review_dashboard,
                    "paper_interface_cache_file",
                    return_value=cache_path,
                ),
                mock.patch.object(
                    review_dashboard,
                    "repository_build_input_snapshot",
                    side_effect=AssertionError("interactive cache must not walk Lean imports"),
                ),
            ):
                rows = review_dashboard.review_items_for_paper(
                    folder, render_images=False
                )

        self.assertEqual([item.name for item in rows], ["endpoint"])

    def test_complete_accepted_display_graph_skips_legacy_authority(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            audit = folder / review_dashboard.PAPER_AUDIT_DIR
            audit.mkdir(parents=True)
            (audit / "source_record_audit.json").write_text(
                json.dumps({"paper": "Fixture"}), encoding="utf-8"
            )
            with (
                mock.patch.object(
                    review_surface,
                    "_recorded_graph_packet_projection",
                    return_value=(
                        True,
                        SimpleNamespace(reviewed_display_surface_complete=True),
                    ),
                ),
                mock.patch(
                    "scripts.source_record_semantic_reuse."
                    "load_current_semantic_reuse_authority",
                    side_effect=AssertionError("loaded legacy authority"),
                ),
            ):
                authority = (
                    review_dashboard.current_dashboard_semantic_reuse_authority(
                        folder
                    )
                )

        self.assertIsNone(authority)

    def test_historical_display_graph_retains_strict_recorded_reader(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            audit = folder / review_dashboard.PAPER_AUDIT_DIR
            audit.mkdir(parents=True)
            raw_path = audit / "source_record_audit.json"
            raw_path.write_text(json.dumps({"paper": "Fixture"}), encoding="utf-8")
            expected = SimpleNamespace(result={"current": True})
            with (
                mock.patch.object(
                    review_surface,
                    "_recorded_graph_packet_projection",
                    return_value=(
                        True,
                        SimpleNamespace(reviewed_display_surface_complete=False),
                    ),
                ),
                mock.patch(
                    "scripts.source_record_semantic_reuse."
                    "load_current_semantic_reuse_authority",
                    return_value=expected,
                ) as load,
            ):
                authority = (
                    review_dashboard.current_dashboard_semantic_reuse_authority(
                        folder
                    )
                )

        self.assertIs(authority, expected)
        load.assert_called_once()

    def test_invalid_selected_graph_cannot_fall_back_to_legacy_authority(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            audit = folder / review_dashboard.PAPER_AUDIT_DIR
            audit.mkdir(parents=True)
            (audit / "source_record_audit.json").write_text(
                json.dumps({"paper": "Fixture"}), encoding="utf-8"
            )
            with (
                mock.patch.object(
                    review_surface,
                    "_recorded_graph_packet_projection",
                    return_value=(True, None),
                ),
                mock.patch(
                    "scripts.source_record_semantic_reuse."
                    "load_current_semantic_reuse_authority",
                    side_effect=AssertionError("invalid graph fell back"),
                ),
            ):
                authority = (
                    review_dashboard.current_dashboard_semantic_reuse_authority(
                        folder
                    )
                )

        self.assertIsNone(authority)
