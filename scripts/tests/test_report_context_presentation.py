"""Tests for display-only settled-context wording."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from scripts.approved_review_context_report import (
    replace_approved_review_context_block,
)
from scripts.human_review_packet_renderer import _row_tex
from scripts.current_closeout.review_surface import (
    model_convention_contexts_from_source_map,
)
from scripts.report_context_presentation import (
    report_context_presentation,
    row_context_presentation,
)
from scripts.source_proof_fidelity_semantics import (
    source_proof_fidelity_semantic_sha256,
)
from scripts.source_record_target_disposition import (
    model_convention_semantic_digest,
)
from scripts.source_review_input import (
    materialize_approved_review_contexts,
    source_semantic_input_bundle,
)


CONVENTION_ID = "FIXTURE-CALENDAR-01"


def _convention() -> dict[str, str]:
    return {
        "id": CONVENTION_ID,
        "source_locator": "source.txt:1",
        "classification": "source_text_model_convention",
        "formal_meaning": "Count first reports in calendar time.",
        "why_needed": "Birth and first-report windows differ.",
        "checked_scope": "The process lemma and its prerequisites.",
        "report_summary": "The established report wording.",
    }


def _fidelity(convention: dict[str, str]) -> dict[str, object]:
    return {
        "schema": 2,
        "paper": "Fixture",
        "source_artifact_path": "source.txt",
        "source_artifact_sha256": "a" * 64,
        "review_status": "complete",
        "reviewed_proof_scopes": [],
        "model_conventions": [convention],
        "defects": [],
    }


def _source_item(fidelity: dict[str, object]) -> dict[str, object]:
    quote = "The source claim."
    item: dict[str, object] = {
        "source_anchor_evidence": [
            {
                "path": "source.txt",
                "line_start": 1,
                "line_end": 1,
                "quoted_text": quote,
                "quoted_text_sha256": hashlib.sha256(quote.encode()).hexdigest(),
            }
        ],
        "model_convention_ids": [CONVENTION_ID],
        "approved_review_context_schema": 1,
    }
    contexts, error = materialize_approved_review_contexts(
        item, source_proof_fidelity=fidelity
    )
    if error:  # pragma: no cover - fixture construction should stay valid.
        raise AssertionError(error)
    item["approved_review_contexts"] = contexts
    return item


def _write_presentation(folder: Path, summary: str) -> None:
    path = folder / "docs" / "REPORT_CONTEXT_SUMMARIES.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "schema": 1,
                "paper": folder.name,
                "summaries": {CONVENTION_ID: summary},
            }
        ),
        encoding="utf-8",
    )


def _write_nonmaterial_coverage(
    folder: Path, *, disposition: str = "not_material", reason: str = ""
) -> None:
    item: dict[str, str] = {"disposition": disposition}
    if reason:
        item["reason"] = reason
    path = folder / "docs" / "REPORT_MEMO_COVERAGE.json"
    path.write_text(
        json.dumps({"items": {f"convention/{CONVENTION_ID}": item}}),
        encoding="utf-8",
    )


class ReportContextPresentationTests(unittest.TestCase):
    def test_nonmaterial_convention_omission_is_display_only(self) -> None:
        convention = _convention()
        source_item = _source_item(_fidelity(convention))
        contexts = source_item["approved_review_contexts"]
        assert isinstance(contexts, list)
        _source, source_digest, error = source_semantic_input_bundle(source_item)
        self.assertEqual(error, "")

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "docs").mkdir(parents=True)
            _write_nonmaterial_coverage(
                folder,
                reason="The unchanged calendar encoding adds no premise or deviation.",
            )
            (folder / "docs" / "REPORT_CONTEXT_SUMMARIES.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": "Fixture",
                        "summaries": {},
                        "omitted_conventions": [CONVENTION_ID],
                    }
                ),
                encoding="utf-8",
            )
            presentation, presentation_error = report_context_presentation(
                folder, contexts
            )
            self.assertEqual(presentation_error, "")
            assert presentation is not None
            self.assertEqual(
                presentation.omitted_convention_ids, frozenset({CONVENTION_ID})
            )
            self.assertNotIn(CONVENTION_ID, presentation.summaries_by_id)

            report = replace_approved_review_context_block(
                "# Report\n\n## 10. Source Clarifications and Exact Readings\n\n"
                "## 11. Paper Issues or Caveats\n\nNone.\n",
                contexts=contexts,
                path=folder / "FINAL_VALIDATION_REPORT.md",
            )
            row = _row_tex(
                {
                    "verbatim_source_input": "The source claim.",
                    "semantic_expanded_statement": "def claimSpec : Prop := True",
                    "approved_review_contexts": contexts,
                    "approved_review_context_presentation": row_context_presentation(
                        contexts, presentation
                    ),
                },
                [{"source_location": "source.txt:1"}],
                "Fixture.claim",
                1,
            )

        self.assertNotIn("BEGIN GENERATED SETTLED REVIEW CONTEXT", report)
        self.assertNotIn("Settled source reading", row)
        self.assertEqual(source_semantic_input_bundle(source_item)[1], source_digest)

    def test_omission_requires_existing_nonmaterial_coverage(self) -> None:
        contexts = _source_item(_fidelity(_convention()))[
            "approved_review_contexts"
        ]
        assert isinstance(contexts, list)
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "docs").mkdir(parents=True)
            presentation_path = folder / "docs" / "REPORT_CONTEXT_SUMMARIES.json"
            presentation_path.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": "Fixture",
                        "summaries": {},
                        "omitted_conventions": [CONVENTION_ID],
                    }
                ),
                encoding="utf-8",
            )

            self.assertIn(
                "without a report-coverage assessment",
                report_context_presentation(folder, contexts)[1],
            )
            _write_nonmaterial_coverage(folder, disposition="memo")
            self.assertIn(
                "only when its report-coverage assessment is not_material",
                report_context_presentation(folder, contexts)[1],
            )
            _write_nonmaterial_coverage(folder)
            self.assertIn(
                "without the required non-material reason",
                report_context_presentation(folder, contexts)[1],
            )
            _write_nonmaterial_coverage(folder, reason="No new premise.")
            payload = json.loads(presentation_path.read_text(encoding="utf-8"))
            payload["summaries"] = {CONVENTION_ID: "Reader wording."}
            presentation_path.write_text(json.dumps(payload), encoding="utf-8")
            self.assertIn(
                "both summarizes and omits",
                report_context_presentation(folder, contexts)[1],
            )

    def test_assumption_records_share_one_explanation_without_semantic_edits(self) -> None:
        contexts = []
        for condition in ("Positive moments.", "Positive moments and a strict witness."):
            materialized, error = materialize_approved_review_contexts(
                {"accepted_additional_assumptions": {
                    "approval_reference": "fixture decision",
                    "approved_at": "2026-09-05",
                    "conditions": [condition],
                }},
                source_proof_fidelity=None,
            )
            self.assertEqual(error, "")
            contexts.extend(materialized)
        before = json.dumps(contexts, sort_keys=True)
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "docs").mkdir(parents=True)
            path = folder / "docs/REPORT_CONTEXT_SUMMARIES.json"
            payload = {
                "schema": 1, "paper": "Fixture", "summaries": {},
                "assumption_summaries": {
                    context["record_sha256"]: "Moments and strictness: see the memo."
                    for context in contexts
                },
            }
            path.write_text(json.dumps(payload))
            source_map = {
                "approved_review_context_schema": 1,
                "items": {
                    str(index): {
                        "approved_review_context_schema": 1,
                        "approved_review_contexts": [context],
                    }
                    for index, context in enumerate(contexts)
                },
            }
            packet_contexts, error = model_convention_contexts_from_source_map(
                source_map, include_additional_assumptions=True
            )
            self.assertEqual(error, "")
            self.assertEqual(len(packet_contexts), 2)
            self.assertEqual(report_context_presentation(folder, packet_contexts)[1], "")
            self.assertEqual(model_convention_contexts_from_source_map(source_map), ([], ""))
            rendered = replace_approved_review_context_block(
                "# Report\n\n## 10. Source Clarifications and Exact Readings\n\n## 11. Paper Issues or Caveats\nNone.\n", contexts=contexts,
                path=folder / "FINAL_VALIDATION_REPORT.md",
            )
            self.assertNotIn("Moments and strictness: see the memo.", rendered)
            self.assertNotIn("Positive moments and a strict witness.", rendered)
            first, error = report_context_presentation(folder, contexts)
            self.assertEqual(error, "")
            assert first is not None
            # A record not explicitly grouped retains its full condition.
            payload["assumption_summaries"].pop(contexts[1]["record_sha256"])
            path.write_text(json.dumps(payload))
            partial = replace_approved_review_context_block(
                "# Report\n\n## 10. Source Clarifications and Exact Readings\n\n## 11. Paper Issues or Caveats\nNone.\n", contexts=contexts,
                path=folder / "FINAL_VALIDATION_REPORT.md",
            )
            self.assertNotIn("Positive moments and a strict witness.", partial)
            second, error = report_context_presentation(folder, contexts)
            self.assertEqual(error, "")
            assert second is not None
            self.assertNotEqual(first.presentation_sha256, second.presentation_sha256)
            payload["assumption_summaries"]["f" * 64] = "Unknown record."
            path.write_text(json.dumps(payload))
            self.assertIn("unknown additional-assumption", report_context_presentation(folder, contexts)[1])
            payload["assumption_summaries"].pop("f" * 64)
            payload["assumption_summaries"][contexts[0]["record_sha256"]] = " "
            path.write_text(json.dumps(payload))
            self.assertIn("must be nonempty", report_context_presentation(folder, contexts)[1])
        self.assertEqual(before, json.dumps(contexts, sort_keys=True))

    def test_directory_and_ambiguous_whitespace_ids_fail_closed(self) -> None:
        contexts = _source_item(_fidelity(_convention()))["approved_review_contexts"]
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            path = folder / "docs/REPORT_CONTEXT_SUMMARIES.json"
            path.mkdir(parents=True)
            self.assertIn("unreadable", report_context_presentation(folder, contexts)[1])
            path.rmdir()
            path.write_text(json.dumps({
                "schema": 1, "paper": "Fixture",
                "summaries": {CONVENTION_ID: "A.", " " + CONVENTION_ID: "B."},
            }))
            self.assertIn("whitespace", report_context_presentation(folder, contexts)[1])

    def test_wording_changes_documents_without_changing_semantic_identities(
        self,
    ) -> None:
        convention = _convention()
        fidelity = _fidelity(convention)
        source_item = _source_item(fidelity)
        contexts = source_item["approved_review_contexts"]
        assert isinstance(contexts, list)

        _source, source_digest, error = source_semantic_input_bundle(source_item)
        self.assertEqual(error, "")
        convention_digest = model_convention_semantic_digest(convention)
        fidelity_digest = source_proof_fidelity_semantic_sha256(fidelity)
        report_shell = (
            "# Report\n\n## 10. Source Clarifications and Exact Readings\n\n"
            "## 11. Paper Issues or Caveats\n\nNone.\n"
        )

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            report_path = folder / "FINAL_VALIDATION_REPORT.md"
            _write_presentation(folder, "Reader wording A.")
            first, first_error = report_context_presentation(folder, contexts)
            self.assertEqual(first_error, "")
            assert first is not None
            first_report = replace_approved_review_context_block(
                report_shell, contexts=contexts, path=report_path
            )
            first_packet = _row_tex(
                {
                    "verbatim_source_input": "The source claim.",
                    "semantic_expanded_statement": "def claimSpec : Prop := True",
                    "approved_review_contexts": contexts,
                    "approved_review_context_presentation": row_context_presentation(
                        contexts, first
                    ),
                },
                [{"source_location": "source.txt:1"}],
                "Fixture.claim",
                1,
            )

            _write_presentation(folder, "Reader wording B.")
            second, second_error = report_context_presentation(folder, contexts)
            self.assertEqual(second_error, "")
            assert second is not None
            second_report = replace_approved_review_context_block(
                report_shell, contexts=contexts, path=report_path
            )
            refreshed_first_report = replace_approved_review_context_block(
                first_report, contexts=contexts, path=report_path
            )
            second_packet = _row_tex(
                {
                    "verbatim_source_input": "The source claim.",
                    "semantic_expanded_statement": "def claimSpec : Prop := True",
                    "approved_review_contexts": contexts,
                    "approved_review_context_presentation": row_context_presentation(
                        contexts, second
                    ),
                },
                [{"source_location": "source.txt:1"}],
                "Fixture.claim",
                1,
            )

        self.assertNotIn("Reader wording A.", first_report)
        self.assertNotIn("Reader wording B.", second_report)
        self.assertEqual(refreshed_first_report, second_report)
        self.assertEqual(first_report, second_report)
        self.assertNotEqual(first_packet, second_packet)
        self.assertNotEqual(first.presentation_sha256, second.presentation_sha256)
        self.assertEqual(source_semantic_input_bundle(source_item)[1], source_digest)
        self.assertEqual(model_convention_semantic_digest(convention), convention_digest)
        self.assertEqual(
            source_proof_fidelity_semantic_sha256(fidelity), fidelity_digest
        )

        changed_convention = {
            **convention,
            "formal_meaning": "Count reports by birth cohort instead.",
        }
        changed_fidelity = _fidelity(changed_convention)
        changed_source_item = _source_item(changed_fidelity)
        self.assertNotEqual(
            source_semantic_input_bundle(changed_source_item)[1], source_digest
        )
        self.assertNotEqual(
            model_convention_semantic_digest(changed_convention), convention_digest
        )
        self.assertNotEqual(
            source_proof_fidelity_semantic_sha256(changed_fidelity), fidelity_digest
        )

    def test_unknown_and_malformed_overrides_fail_closed(self) -> None:
        contexts = _source_item(_fidelity(_convention()))[
            "approved_review_contexts"
        ]
        assert isinstance(contexts, list)
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            path = folder / "docs" / "REPORT_CONTEXT_SUMMARIES.json"
            path.parent.mkdir(parents=True)
            path.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": "Fixture",
                        "summaries": {"UNKNOWN-ID": "Unused wording."},
                    }
                ),
                encoding="utf-8",
            )
            projection, error = report_context_presentation(folder, contexts)
            self.assertIsNone(projection)
            self.assertIn("unknown model convention", error)

            path.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": "Fixture",
                        "summaries": {CONVENTION_ID: ""},
                    }
                ),
                encoding="utf-8",
            )
            projection, error = report_context_presentation(folder, contexts)
            self.assertIsNone(projection)
            self.assertIn("must be a nonempty string", error)


if __name__ == "__main__":
    unittest.main()
