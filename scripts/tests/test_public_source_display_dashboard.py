from __future__ import annotations

from scripts import source_display_projection as source_display

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import public_source_display_projection as projection
from scripts import review_dashboard
from scripts import review_dashboard_html
from scripts import human_review_packet_renderer as renderer
from scripts.current_closeout import review_surface as surface
from scripts.public_release_projection import project_bytes
from scripts.semantic_prerequisite_projection import (
    PAPER_PREREQUISITE_PROMPT_VERSION,
    PAPER_PREREQUISITE_SCHEMA,
)


def _sha256(value: str | bytes) -> str:
    raw = value.encode("utf-8") if isinstance(value, str) else value
    return hashlib.sha256(raw).hexdigest()


class PublicSourceDisplayDashboardTests(unittest.TestCase):
    """Public excerpts are display-only and cannot satisfy strict audit checks."""

    def setUp(self) -> None:
        self.temporary_directory = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary_directory.name)
        self.folder = self.root / "papers" / "Fixture"
        (self.folder / "audit").mkdir(parents=True)
        self.source_text = (
            "Definition 1. A fixture object has one named property.\n"
            "Theorem 1. Every fixture object has that property.\n"
        )
        (self.folder / "source.txt").write_text(self.source_text, encoding="utf-8")
        self._write_private_map()
        self._project_fixture_map()

    def tearDown(self) -> None:
        self.temporary_directory.cleanup()

    @property
    def map_path(self) -> Path:
        return self.folder / "audit" / "paper_statement_map.json"

    def _anchor(self, line_start: int, line_end: int) -> dict[str, object]:
        quote = "\n".join(self.source_text.splitlines()[line_start - 1 : line_end])
        return {
            "path": "source.txt",
            "line_start": line_start,
            "line_end": line_end,
            "quoted_text": quote,
            "quoted_text_sha256": _sha256(quote),
        }

    def _write_private_map(self) -> None:
        payload = {
            "paper": "Fixture",
            "source_url": "https://arxiv.org/abs/2601.00001",
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": _sha256(self.source_text),
            "source_coverage_mode": "named_theoretical_statements",
            "items": {
                "fixture_definition": {
                    "source_kind": "definition",
                    "claim_bearing": True,
                    "statement": "Definition 1 defines the fixture object.",
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [self._anchor(1, 1)],
                },
                "fixture_theorem": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "statement": "Theorem 1 gives the fixture property.",
                    "source_location": "source.txt:2",
                    "source_anchor_evidence": [self._anchor(2, 2)],
                    "semantic_context_requirements": [
                        {
                            "semantic_role": "definition",
                            "source_anchor_evidence": [self._anchor(1, 1)],
                        }
                    ],
                },
            },
        }
        self.map_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    def _project_fixture_map(self) -> None:
        private_bytes = self.map_path.read_bytes()
        with mock.patch.object(projection, "ROOT", self.root), mock.patch.object(
            review_dashboard, "ROOT", self.root
        ):
            manifest = projection.build_public_source_display_projection(self.folder)
        public_map = project_bytes(
            "papers/Fixture/audit/paper_statement_map.json",
            private_bytes,
            include_source_display_marker=True,
        )
        self.map_path.write_bytes(public_map)
        (self.folder / "audit" / "public_source_display_projection.json").write_text(
            json.dumps(manifest, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    def _public_map(self) -> dict[str, object]:
        return json.loads(self.map_path.read_text(encoding="utf-8"))

    def test_frozen_public_surface_is_available_only_to_browser_display(self) -> None:
        state = source_display.public_source_display_projection_state(self.folder)
        self.assertTrue(state["active"])
        self.assertTrue(state["valid"])
        self.assertEqual(
            state["selected_source_item_ids"],
            ("fixture_definition", "fixture_theorem"),
        )
        surface = review_dashboard.public_source_display_coverage_surface(self.folder)
        self.assertTrue(surface["available"])
        self.assertTrue(surface["display_only"])
        self.assertFalse(surface["raw_source_locally_revalidated"])
        self.assertFalse(surface["audit_current"])
        self.assertEqual(surface["source_item_count"], 2)
        self.assertIn("public_source_display_surface", review_dashboard_html.HTML_PAGE)
        self.assertIn("Source-coverage denominator", review_dashboard_html.HTML_PAGE)

        source_record = self._public_map()["items"]["fixture_theorem"]
        self.assertTrue(
            review_dashboard.source_anchor_file_error(self.folder, source_record)
        )
        connection_state, error = source_display.source_anchor_display_state(
            self.folder,
            source_record,
            source_item_key="fixture_theorem",
        )
        self.assertEqual(connection_state, "release_projected_excerpt")
        self.assertEqual(error, "")

        # The ordinary selector must remain independent of the display helper.
        with mock.patch.object(
            source_display,
            "public_source_display_projection_state",
            side_effect=AssertionError("strict inventory consulted a display manifest"),
        ):
            review_dashboard.paper_coverage_inventory(self.folder)

    def test_tampered_public_anchor_cannot_use_the_display_path(self) -> None:
        payload = self._public_map()
        payload["items"]["fixture_theorem"]["source_anchor_evidence"][0][
            "line_end"
        ] = 1
        self.map_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        source_record = payload["items"]["fixture_theorem"]
        connection_state, error = source_display.source_anchor_display_state(
            self.folder,
            source_record,
            source_item_key="fixture_theorem",
        )
        self.assertEqual(connection_state, "")
        self.assertIn("lacks a valid path", error)

    def test_prerequisite_cards_expose_display_only_source_state(self) -> None:
        (self.root / "AppliedModelingLib").mkdir()
        library_source = self.root / "AppliedModelingLib" / "Fixture.lean"
        library_source.write_text("def Fixture.Model := Nat\n", encoding="utf-8")
        ledger = {
            "schema": review_dashboard.LIBRARY_SEMANTIC_REVIEW_SCHEMA,
            "paper": "Fixture",
            "prompt_version": review_dashboard.REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,
            "target_protocol": review_dashboard.LIBRARY_SEMANTIC_TARGET_PROTOCOL,
            "items": {
                "AppliedModelingLib.Fixture.Model": {
                    "library_declaration": "AppliedModelingLib.Fixture.Model",
                    "source_item": "fixture_definition",
                    "judgment": "matches",
                    "validator": "fixture reviewer",
                    "validated_at": "2026-08-19",
                }
            },
        }
        (self.folder / "audit" / "library_semantic_review.json").write_text(
            json.dumps(ledger, indent=2) + "\n", encoding="utf-8"
        )
        name = "AppliedModelingLib.Fixture.Model"
        target = {
            "display": "def AppliedModelingLib.Fixture.Model := Nat",
            "display_sha256": _sha256("def AppliedModelingLib.Fixture.Model := Nat"),
            "declaration_kind": "definition",
            "direct_library_declarations": (),
        }
        with mock.patch.object(review_dashboard, "ROOT", self.root), mock.patch.object(
            surface, "ROOT", self.root
        ):
            entries = review_dashboard.human_review_library_prerequisites(
                self.folder,
                [{"library_review_owner_declarations": [name]}],
                semantic_targets_override={name: target},
                declaration_sources_override={
                    name: {
                        "library_definition": "def Fixture.Model := Nat",
                        "library_definition_sha256": _sha256(
                            "def Fixture.Model := Nat"
                        ),
                        "library_definition_error": "",
                        "library_source_path": "AppliedModelingLib/Fixture.lean",
                        "library_line_start": 1,
                        "library_line_end": 1,
                    }
                },
            )
        self.assertEqual(len(entries), 1)
        self.assertEqual(entries[0]["source_connection_state"], "release_projected_excerpt")
        self.assertTrue(entries[0]["source_connection_display_only"])
        self.assertFalse(entries[0]["semantic_current"])
        self.assertEqual(entries[0]["semantic_status"], "release-projected excerpt (display only)")
        rendered = renderer._prerequisites_tex(
            self.folder,
            entries,
        )
        self.assertIn(r"release\_projected\_excerpt", rendered)

    def test_packet_paper_prerequisite_uses_only_the_explicit_display_validator(self) -> None:
        ledger = {
            "schema": PAPER_PREREQUISITE_SCHEMA,
            "paper": "Fixture",
            "prompt_version": PAPER_PREREQUISITE_PROMPT_VERSION,
            "target_protocol": surface.PAPER_PREREQUISITE_TARGET_PROTOCOL,
            "items": {
                "Fixture.Model": {
                    "paper_declaration": "Fixture.Model",
                    "source_item": "fixture_definition",
                    "judgment": "matches",
                    "validator": "fixture reviewer",
                    "validated_at": "2026-08-19",
                }
            },
        }
        (self.folder / "audit" / "paper_semantic_prerequisites.json").write_text(
            json.dumps(ledger, indent=2) + "\n", encoding="utf-8"
        )
        declaration = {
            "paper_source_path": "PaperInterface.lean",
            "paper_line_start": 1,
            "paper_declaration_sha256": _sha256("def Fixture.Model := Nat"),
        }
        target = {
            "display": "def Fixture.Model := Nat",
            "display_sha256": _sha256("def Fixture.Model := Nat"),
            "declaration_kind": "definition",
            "direct_paper_declarations": (),
            "direct_library_declarations": (),
        }
        with mock.patch.object(surface, "ROOT", self.root):
            entries = surface._prepared_paper_prerequisites(
                self.folder,
                {"Fixture.ClaimSpec": {"prerequisite_declarations": ["Fixture.Model"]}},
                semantic_targets_by_name_override={"Fixture.Model": target},
                declaration_sources_override={"Fixture.Model": declaration},
            )
        self.assertEqual(len(entries), 1)
        self.assertEqual(entries[0]["source_connection_state"], "release_projected_excerpt")
        self.assertTrue(entries[0]["source_connection_display_only"])
        self.assertFalse(entries[0]["semantic_current"])
        self.assertEqual(entries[0]["semantic_status"], "release-projected excerpt (display only)")
        rendered = renderer._paper_prerequisites_tex(entries)
        self.assertIn(r"release\_projected\_excerpt", rendered)

    def test_packet_locator_and_final_presentation_hide_private_paths(self) -> None:
        rendered_locator = renderer._tex_locator(
            ".audit_source/Fixture/source.txt:19-21"
        )
        self.assertIn("cited publication, lines 19", rendered_locator)
        self.assertIn("21", rendered_locator)
        self.assertNotIn("audit", rendered_locator.lower())
        metadata = renderer._tex_escape("private text extraction from /tmp/fixture")
        self.assertNotIn("private", metadata.lower())
        self.assertNotIn("tmp", metadata.lower())
        rendered = renderer._public_packet_presentation_tex(
            "Visible /tmp/fixture workflow.\\n"
            "\\begin{ReviewVerbatim}\\n"
            "The source quote stays exact.\\n"
            "\\end{ReviewVerbatim}\\n",
            paper="Fixture",
        )
        self.assertNotIn("/tmp/fixture", rendered)
        self.assertIn("The source quote stays exact.", rendered)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
