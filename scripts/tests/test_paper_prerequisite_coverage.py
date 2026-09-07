#!/usr/bin/env python3
"""Tests for compositional source-definition coverage identities."""

from __future__ import annotations


import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import issue_paper_coverage_review as issuer  # noqa: E402
from scripts import review_dashboard as dashboard  # noqa: E402


class PaperPrerequisiteCoverageTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp_dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp_dir.cleanup)
        self.folder = Path(self.temp_dir.name) / "FixturePaper"
        (self.folder / "audit").mkdir(parents=True)
        quote = "Definition 1. A choice frame consists of a finite family of offers."
        quote_sha256 = hashlib.sha256(quote.encode("utf-8")).hexdigest()
        self.source_item = {
            "source_kind": "definition",
            "source_location": "source.tex:1-1",
            "statement": "Definition of a choice frame.",
            "lean_declarations": ["FixturePaper.ChoiceFrame"],
            "source_anchor_evidence": [
                {
                    "path": "source.tex",
                    "line_start": 1,
                    "line_end": 1,
                    "quoted_text": quote,
                    "quoted_text_sha256": quote_sha256,
                }
            ],
        }
        self.inventory = {"choice_frame_model": self.source_item}
        _source_input, source_digest, source_error = (
            dashboard.source_semantic_input_bundle(
                self.source_item,
                require_context_roles=True,
            )
        )
        self.assertEqual(source_error, "")
        self.target_digest = "a" * 64
        self.ledger = {
            "schema": dashboard.PAPER_PREREQUISITE_LEDGER_SCHEMA,
            "paper": self.folder.name,
            "prompt_version": dashboard.PAPER_PREREQUISITE_LEDGER_PROMPT_VERSION,
            "target_protocol": dashboard.PAPER_PREREQUISITE_LEDGER_TARGET_PROTOCOL,
            "items": {
                "FixturePaper.ChoiceFrame": {
                    "judgment": "matches",
                    "paper_declaration": "FixturePaper.ChoiceFrame",
                    "paper_semantic_target_protocol": (
                        dashboard.PAPER_PREREQUISITE_LEDGER_TARGET_PROTOCOL
                    ),
                    "paper_semantic_target_sha256": self.target_digest,
                    "reason": (
                        "The exact Lean structure has precisely the finite offer "
                        "family stated in the byte-pinned source definition."
                    ),
                    "source_input_bundle_sha256": source_digest,
                    "source_item": "choice_frame_model",
                    "validated_at": "2026-08-27T12:00:00Z",
                    "validator": "Independent semantic reviewer",
                    "validator_type": "llm_as_judge",
                }
            },
        }
        self._write_ledger(self.ledger)

    def _write_ledger(self, payload: dict[str, object]) -> None:
        (self.folder / "audit" / "paper_semantic_prerequisites.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )

    def _semantic_targets(self) -> dict[str, dict[str, str]]:
        return {
            "FixturePaper.ChoiceFrame": {
                "display_sha256": self.target_digest,
            }
        }

    def test_current_prerequisite_projects_as_typed_coverage_target(self) -> None:
        projected = dashboard.paper_semantic_prerequisite_coverage_review_items(
            self.folder,
            self.inventory,
            [],
            semantic_targets_by_name_override=self._semantic_targets(),
        )

        self.assertEqual(set(projected), {"FixturePaper.ChoiceFrame"})
        row = projected["FixturePaper.ChoiceFrame"]
        self.assertFalse(row.llm_match_stale)
        self.assertEqual(
            row.coverage_target_kind,
            dashboard.PAPER_PREREQUISITE_COVERAGE_TARGET_KIND,
        )
        identity = dashboard._current_row_signature_digest(row)
        self.assertRegex(identity, r"^[0-9a-f]{64}$")
        self.assertEqual(
            dashboard._coverage_review_row_signature_errors(
                "choice_frame_model",
                [row.name],
                {row.name: identity},
                projected,
                current_signature_by_row={row.name: identity},
            ),
            [],
        )

    def test_changed_source_bundle_fails_closed_without_new_review(self) -> None:
        stale = copy.deepcopy(self.ledger)
        stale["items"]["FixturePaper.ChoiceFrame"][  # type: ignore[index]
            "source_input_bundle_sha256"
        ] = "b" * 64
        self._write_ledger(stale)

        row = dashboard.paper_semantic_prerequisite_coverage_review_items(
            self.folder,
            self.inventory,
            [],
            semantic_targets_by_name_override=self._semantic_targets(),
        )["FixturePaper.ChoiceFrame"]

        self.assertTrue(row.llm_match_stale)
        self.assertEqual(dashboard._current_row_signature_digest(row), "")
        errors = dashboard._coverage_review_row_signature_errors(
            "choice_frame_model",
            [row.name],
            {row.name: row.coverage_target_identity_sha256},
            {row.name: row},
            current_signature_by_row={row.name: ""},
        )
        self.assertEqual(len(errors), 1)
        self.assertIn("current typed semantic-review target identity", errors[0])

    def test_changed_current_lean_target_fails_closed_without_new_review(self) -> None:
        row = dashboard.paper_semantic_prerequisite_coverage_review_items(
            self.folder,
            self.inventory,
            [],
            semantic_targets_by_name_override={
                "FixturePaper.ChoiceFrame": {"display_sha256": "c" * 64}
            },
        )["FixturePaper.ChoiceFrame"]

        self.assertTrue(row.llm_match_stale)
        self.assertEqual(dashboard._current_row_signature_digest(row), "")

    def test_issuer_references_prerequisite_identity_without_second_judgment(self) -> None:
        seed_payload = {
            "schema": 1,
            "paper": self.folder.name,
            "items": {"choice_frame_model": {}},
        }
        decisions = {
            "validator": "Coverage routing reviewer",
            "validator_type": "agent",
            "items": {
                "choice_frame_model": {
                    "coverage": "covered",
                    "review_rows": ["FixturePaper.ChoiceFrame"],
                    "support_declarations": [],
                    "reason": (
                        "The source definition is directly represented by the "
                        "already-reviewed paper semantic prerequisite."
                    ),
                    "dashboard_evidence": (
                        "The exact prerequisite card displays the byte-pinned "
                        "source bundle and the current transparent Lean body."
                    ),
                }
            },
        }
        with (
            mock.patch.object(dashboard, "_cache_source_hashes", return_value={}),
            mock.patch.object(dashboard, "load_cached_review_rows", return_value=[]),
            mock.patch.object(
                dashboard,
                "paper_coverage_inventory",
                return_value=(self.inventory, self.inventory, "named", ""),
            ),
            mock.patch.object(issuer.seed, "seed_payload", return_value=seed_payload),
            mock.patch(
                "scripts.current_closeout.review_surface._current_packet_lean_cache",
                return_value={
                    "paper_prerequisite_targets": self._semantic_targets(),
                },
            ),
        ):
            payload = issuer.issue(self.folder, decisions)

        projected = dashboard.paper_semantic_prerequisite_coverage_review_items(
            self.folder,
            self.inventory,
            [],
            semantic_targets_by_name_override=self._semantic_targets(),
        )["FixturePaper.ChoiceFrame"]
        output = payload["items"]["choice_frame_model"]
        self.assertEqual(
            output["review_row_signature_sha256"],
            {
                "FixturePaper.ChoiceFrame": (
                    projected.coverage_target_identity_sha256
                )
            },
        )
        self.assertNotIn("judgment", output)


if __name__ == "__main__":
    unittest.main()
