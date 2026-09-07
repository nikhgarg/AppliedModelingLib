from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from scripts import public_source_display_projection as projection
from scripts.public_release_projection import project_bytes


def _sha256(value: str | bytes) -> str:
    raw = value.encode("utf-8") if isinstance(value, str) else value
    return hashlib.sha256(raw).hexdigest()


class PublicSourceDisplayProjectionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary_directory = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary_directory.name)
        self.papers = self.root / "papers"
        self.folder = self.papers / "Fixture"
        (self.folder / "audit").mkdir(parents=True)
        self.source_text = (
            "Definition 1. A fixture object has one named property.\n"
            "Theorem 1. Every fixture object has that property.\n"
            "Equation (1). This standalone formula is not a named theorem.\n"
        )
        (self.folder / "source.txt").write_text(self.source_text, encoding="utf-8")
        self.original_root = projection.ROOT
        projection.ROOT = self.root
        self._write_map()

    def tearDown(self) -> None:
        projection.ROOT = self.original_root
        self.temporary_directory.cleanup()

    @property
    def map_path(self) -> Path:
        return self.folder / "audit" / "paper_statement_map.json"

    def _anchor(
        self,
        line_start: int,
        line_end: int,
        *,
        path: str = "source.txt",
        source_text: str | None = None,
    ) -> dict[str, object]:
        text = self.source_text if source_text is None else source_text
        quote = "\n".join(text.splitlines()[line_start - 1 : line_end])
        return {
            "path": path,
            "line_start": line_start,
            "line_end": line_end,
            "quoted_text": quote,
            "quoted_text_sha256": _sha256(quote),
        }

    def _write_map(self, *, stale_anchor_hash: bool = False) -> None:
        theorem_anchor = self._anchor(2, 2)
        if stale_anchor_hash:
            theorem_anchor["quoted_text_sha256"] = "0" * 64
        payload = {
            "paper": "Fixture",
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": _sha256(self.source_text),
            "source_coverage_mode": "named_theoretical_statements",
            "items": {
                "fixture_definition": {
                    "source_kind": "definition",
                    "statement": "Definition 1 defines the fixture object.",
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [self._anchor(1, 1)],
                },
                "fixture_theorem": {
                    "source_kind": "theorem",
                    "statement": "Theorem 1 gives the fixture property.",
                    "source_location": "source.txt:2",
                    "source_anchor_evidence": [theorem_anchor],
                    "semantic_context_requirements": [
                        {
                            "semantic_role": "definition",
                            "source_anchor_evidence": [self._anchor(1, 1)],
                        }
                    ],
                },
                "standalone_formula": {
                    "source_kind": "formula",
                    "statement": "Equation (1) is a standalone formula.",
                    "source_location": "source.txt:3",
                    "source_anchor_evidence": [self._anchor(3, 3)],
                },
            },
        }
        self.map_path.write_text(
            json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )

    def _add_semantic_transcription(self) -> str:
        semantic_text = (
            "Theorem 1. Every fixture object has that property.\n"
            "The visual transcript includes its complete selected semantic surface.\n"
        )
        semantic_path = self.folder / "semantic-review.md"
        semantic_path.write_text(semantic_text, encoding="utf-8")
        pdf_bytes = b"%PDF-1.4\nfixture visual source\n"
        (self.folder / "source.pdf").write_bytes(pdf_bytes)
        payload = json.loads(self.map_path.read_text(encoding="utf-8"))
        visual = {"path": "source.pdf", "sha256": _sha256(pdf_bytes)}
        payload["source_text_companion"] = {
            "schema": 1,
            "canonical_text": {
                "path": "source.txt",
                "sha256": _sha256(self.source_text),
            },
            "visual_primary_scan": visual,
            "transcript_input_scan": visual,
            "extraction": {"tool": "pdftotext", "options": []},
            "page_map": [
                {"line_start": 1, "line_end": 3, "pdf_page": 1, "printed_page": 1}
            ],
            "visual_comparison_attestation": {
                "complete": True,
                "method": "Fixture visual comparison.",
            },
            "semantic_review_transcription": {
                "schema": 1,
                "path": "semantic-review.md",
                "sha256": _sha256(semantic_text),
                "controlling_visual_source": visual,
                "complete_for_selected_semantic_surface": True,
                "method": "Fixture visual transcription.",
            },
        }
        payload["items"]["fixture_theorem"]["source_anchor_evidence"] = [
            self._anchor(
                1,
                1,
                path="semantic-review.md",
                source_text=semantic_text,
            )
        ]
        self.map_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        return semantic_text

    def _add_cited_context(self) -> str:
        cited_text = "Prior Result. Every cited fixture has a stable property.\n"
        cited_path = self.folder / "cited.txt"
        cited_path.write_text(cited_text, encoding="utf-8")
        provenance = {
            "schema": 1,
            "source_url": "https://example.test/cited-fixture",
            "source_artifact_sha256": _sha256(cited_text),
            "paper_local_copy_path": "cited.txt",
            "source_version": "fixture source record",
        }
        provenance_bytes = (
            json.dumps(provenance, ensure_ascii=False, indent=2) + "\n"
        ).encode("utf-8")
        (self.folder / "cited.provenance.json").write_bytes(provenance_bytes)
        payload = json.loads(self.map_path.read_text(encoding="utf-8"))
        payload["cited_source_artifacts_schema"] = 1
        payload["cited_source_artifacts"] = [
            {
                "id": "fixture_prior_result",
                "path": "cited.txt",
                "sha256": _sha256(cited_text),
                "provenance_path": "cited.provenance.json",
                "provenance_sha256": _sha256(provenance_bytes),
                "source_url": "https://example.test/cited-fixture",
                "semantic_roles": ["prior_result"],
            }
        ]
        payload["items"]["fixture_theorem"]["semantic_context_requirements"].append(
            {
                "semantic_role": "prior_result",
                "cited_source_artifact_id": "fixture_prior_result",
                "source_anchor_evidence": [
                    self._anchor(1, 1, path="cited.txt", source_text=cited_text)
                ],
            }
        )
        self.map_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        return cited_text

    def test_build_freezes_current_coverage_surface_without_full_raw_source(self) -> None:
        first = projection.build_public_source_display_projection(self.folder)
        second = projection.build_public_source_display_projection(self.folder)
        self.assertEqual(first, second)
        self.assertEqual(
            first["selected_source_item_ids"],
            ["fixture_definition", "fixture_theorem"],
        )
        self.assertEqual(first["source_coverage_mode"], "named_theoretical_statements")
        self.assertEqual(
            first["private_source_map_sha256"], _sha256(self.map_path.read_bytes())
        )
        self.assertEqual(
            first["public_source_map_sha256"],
            _sha256(
                project_bytes(
                    "papers/Fixture/audit/paper_statement_map.json",
                    self.map_path.read_bytes(),
                    include_source_display_marker=True,
                )
            ),
        )
        self.assertEqual(first["source_artifact_sha256"], _sha256(self.source_text))
        self.assertEqual(
            first["public_manifest_path"],
            "papers/Fixture/audit/public_source_display_projection.json",
        )
        self.assertFalse(first["raw_source_artifact_included"])
        self.assertEqual(
            first["raw_source_display_material"],
            "selected_byte_pinned_source_anchor_quotes",
        )
        serialized = projection.public_source_display_projection_bytes(self.folder)
        self.assertNotIn(b"This standalone formula", serialized)
        self.assertNotIn(b'"path"', serialized)
        theorem = first["selected_source_items"]["fixture_theorem"]
        self.assertEqual(
            theorem["source_anchors"][0]["quoted_text_sha256"],
            _sha256("Theorem 1. Every fixture object has that property."),
        )
        self.assertEqual(
            theorem["semantic_context"][0]["semantic_role"], "definition"
        )

    def test_write_and_validation_detect_a_changed_displayed_anchor(self) -> None:
        output = projection.write_public_source_display_projection(self.folder)
        self.assertEqual(output, self.folder / "audit/public_source_display_projection.json")
        self.assertEqual(projection.validate_public_source_display_projection(self.folder), [])

        payload = json.loads(output.read_text(encoding="utf-8"))
        payload["selected_source_items"]["fixture_theorem"]["source_anchors"][0][
            "quoted_text_sha256"
        ] = "f" * 64
        output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        issues = projection.validate_public_source_display_projection(self.folder)
        self.assertTrue(any("quoted_text_sha256" in issue for issue in issues))
        self.assertTrue(any("deterministic serialization" in issue for issue in issues))

    def test_generation_fails_closed_on_stale_private_anchor_or_source_pin(self) -> None:
        payload = json.loads(self.map_path.read_text(encoding="utf-8"))
        second_anchor = dict(
            payload["items"]["fixture_theorem"]["source_anchor_evidence"][0]
        )
        second_anchor["quoted_text_sha256"] = "0" * 64
        # The first anchor retains the existing selector's theorem presentation;
        # the second proves that every anchor on a selected item is checked.
        payload["items"]["fixture_theorem"]["source_anchor_evidence"].append(
            second_anchor
        )
        self.map_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        with self.assertRaisesRegex(
            projection.PublicSourceDisplayProjectionError, "bound source record"
        ):
            projection.build_public_source_display_projection(self.folder)

        self._write_map()
        payload = json.loads(self.map_path.read_text(encoding="utf-8"))
        payload["source_artifact_sha256"] = "1" * 64
        self.map_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        with self.assertRaisesRegex(
            projection.PublicSourceDisplayProjectionError,
            "current byte-pinned canonical source artifact",
        ):
            projection.build_public_source_display_projection(self.folder)

    def test_paper_and_repository_relative_aliases_resolve_to_the_same_source(
        self,
    ) -> None:
        payload = json.loads(self.map_path.read_text(encoding="utf-8"))
        payload["items"]["fixture_theorem"]["source_anchor_evidence"][0]["path"] = (
            "papers/Fixture/source.txt"
        )
        self.map_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")

        built = projection.build_public_source_display_projection(self.folder)
        self.assertEqual(
            built["selected_source_items"]["fixture_theorem"]["source_anchors"][0][
                "quoted_text"
            ],
            "Theorem 1. Every fixture object has that property.",
        )

    def test_selected_semantic_transcription_is_pinned_and_stale_bytes_fail_closed(
        self,
    ) -> None:
        semantic_text = self._add_semantic_transcription()
        built = projection.build_public_source_display_projection(self.folder)
        self.assertEqual(
            built["selected_source_items"]["fixture_theorem"]["source_anchors"][0][
                "quoted_text"
            ],
            semantic_text.splitlines()[0],
        )

        (self.folder / "semantic-review.md").write_text(
            semantic_text + "changed bytes\n", encoding="utf-8"
        )
        with self.assertRaises(projection.PublicSourceDisplayProjectionError):
            projection.build_public_source_display_projection(self.folder)

    def test_unregistered_source_path_is_rejected_even_when_its_quote_matches(self) -> None:
        (self.folder / "unregistered.txt").write_text(
            self.source_text, encoding="utf-8"
        )
        payload = json.loads(self.map_path.read_text(encoding="utf-8"))
        payload["items"]["fixture_theorem"]["source_anchor_evidence"][0]["path"] = (
            "unregistered.txt"
        )
        self.map_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")

        with self.assertRaisesRegex(
            projection.PublicSourceDisplayProjectionError,
            "canonical source artifact or its selected semantic transcription",
        ):
            projection.build_public_source_display_projection(self.folder)

    def test_cited_source_requires_registered_id_role_path_and_current_bytes(self) -> None:
        cited_text = self._add_cited_context()
        built = projection.build_public_source_display_projection(self.folder)
        cited_context = built["selected_source_items"]["fixture_theorem"][
            "semantic_context"
        ][1]
        self.assertEqual(cited_context["semantic_role"], "prior_result")
        self.assertEqual(cited_context["source_anchors"][0]["quoted_text"], cited_text.rstrip())

        payload = json.loads(self.map_path.read_text(encoding="utf-8"))
        cited_record = payload["items"]["fixture_theorem"][
            "semantic_context_requirements"
        ][1]
        cited_record.pop("cited_source_artifact_id")
        self.map_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        with self.assertRaisesRegex(
            projection.PublicSourceDisplayProjectionError,
            "canonical source artifact or its selected semantic transcription",
        ):
            projection.build_public_source_display_projection(self.folder)

        cited_record["cited_source_artifact_id"] = "fixture_prior_result"
        cited_record["semantic_role"] = "definition"
        self.map_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        with self.assertRaisesRegex(
            projection.PublicSourceDisplayProjectionError,
            "unregistered semantic role",
        ):
            projection.build_public_source_display_projection(self.folder)

        cited_record["semantic_role"] = "prior_result"
        cited_record["source_anchor_evidence"][0]["path"] = "source.txt"
        self.map_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        with self.assertRaisesRegex(
            projection.PublicSourceDisplayProjectionError,
            "pinned cited source artifact",
        ):
            projection.build_public_source_display_projection(self.folder)

        cited_record["source_anchor_evidence"][0]["path"] = "cited.txt"
        self.map_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        (self.folder / "cited.txt").write_text(
            cited_text + "changed bytes\n", encoding="utf-8"
        )
        with self.assertRaisesRegex(
            projection.PublicSourceDisplayProjectionError,
            "cited source artifact registry is invalid",
        ):
            projection.build_public_source_display_projection(self.folder)

    def test_cli_write_and_check_use_the_fixed_paper_local_target(self) -> None:
        original_papers_dir = projection.PAPERS_DIR
        projection.PAPERS_DIR = self.papers
        try:
            self.assertEqual(projection.main(["--paper", "Fixture", "--write"]), 0)
            self.assertEqual(projection.main(["--paper", "Fixture", "--check"]), 0)
            output = projection.public_source_display_projection_path(self.folder)
            payload = json.loads(output.read_text(encoding="utf-8"))
            payload["selected_source_item_ids"] = ["fixture_definition"]
            output.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            self.assertEqual(projection.main(["--paper", "Fixture", "--check"]), 1)
        finally:
            projection.PAPERS_DIR = original_papers_dir


if __name__ == "__main__":
    unittest.main()
