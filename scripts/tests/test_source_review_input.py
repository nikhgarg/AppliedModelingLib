from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path

from scripts.source_review_input import (
    APPROVED_REVIEW_CONTEXTS_FIELD,
    SourceReviewInputError,
    canonical_source_anchor_evidence,
    materialize_approved_review_contexts,
    source_anchor_file_error,
    source_semantic_input_bundle,
    statement_digest,
)


def anchor(path: str, quote: str, *, line: int = 1) -> dict[str, object]:
    return {
        "path": path,
        "line_start": line,
        "line_end": line,
        "quoted_text": quote,
        "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
    }


class SourceReviewInputTests(unittest.TestCase):
    def test_canonical_anchor_accepts_repository_relative_historical_path(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "papers" / "Fixture"
            source = paper / "source" / "main.tex"
            source.parent.mkdir(parents=True)
            source.write_text("First\nClaim\n", encoding="utf-8")

            anchors = canonical_source_anchor_evidence(
                paper,
                "papers/Fixture/source/main.tex:2",
            )

            self.assertEqual(len(anchors), 1)
            self.assertEqual(
                anchors[0]["path"], "papers/Fixture/source/main.tex"
            )
            self.assertEqual(anchors[0]["quoted_text"], "Claim")

    def test_canonical_anchor_rejects_repository_relative_other_paper(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            outside = root / "papers" / "Other" / "source.tex"
            outside.parent.mkdir(parents=True)
            outside.write_text("Claim\n", encoding="utf-8")

            with self.assertRaisesRegex(
                SourceReviewInputError, "not a readable paper-local file"
            ):
                canonical_source_anchor_evidence(
                    paper,
                    "papers/Other/source.tex:1",
                )

    def test_bundle_contains_only_ordered_verbatim_source_quotes(self) -> None:
        record = {
            "source_anchor_evidence": [anchor("source.txt", "Claim")],
            "semantic_context_requirements": [
                {
                    "semantic_role": "definition",
                    "explanation": "curator paraphrase must not enter the bundle",
                    "source_anchor_evidence": [anchor("source.txt", "Definition", line=2)],
                }
            ],
        }
        text, identity, error = source_semantic_input_bundle(
            record, require_context_roles=True
        )
        self.assertEqual(error, "")
        self.assertEqual(
            text,
            "Claim\n\n[Next verbatim source excerpt]\n\nDefinition",
        )
        self.assertNotIn("curator paraphrase", text)
        self.assertRegex(identity, r"^[0-9a-f]{64}$")

    def test_semantic_source_anchor_narrows_review_not_coverage(self) -> None:
        record = {
            "source_anchor_evidence": [
                anchor("source.txt", "Theorem. Claim. Explanation.")
            ],
            "semantic_source_anchor_evidence": [
                anchor("source.txt", "Theorem. Claim.")
            ],
        }
        text, identity, error = source_semantic_input_bundle(record)
        self.assertEqual(error, "")
        self.assertEqual(text, "Theorem. Claim.")
        self.assertRegex(identity, r"^[0-9a-f]{64}$")

    def test_semantic_source_anchor_is_checked_against_source_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "source.txt").write_text(
                "Theorem. Claim.\nExplanation.\n", encoding="utf-8"
            )
            record = {
                "source_anchor_evidence": [
                    {
                        **anchor("source.txt", "Theorem. Claim.\nExplanation."),
                        "line_end": 2,
                    }
                ],
                "semantic_source_anchor_evidence": [
                    anchor("source.txt", "Theorem. Claim.")
                ],
            }
            self.assertEqual(source_anchor_file_error(paper, record), "")

    def test_semantic_source_anchor_must_be_contained_in_coverage(self) -> None:
        record = {
            "source_anchor_evidence": [anchor("source.txt", "Claim", line=2)],
            "semantic_source_anchor_evidence": [
                anchor("source.txt", "Other claim", line=1)
            ],
        }
        text, identity, error = source_semantic_input_bundle(record)
        self.assertEqual(text, "")
        self.assertEqual(identity, "")
        self.assertIn("must be contained", error)

    def test_approved_context_is_visible_and_changes_only_bundle_identity(self) -> None:
        record = {
            "source_anchor_evidence": [anchor("source.txt", "Claim")],
            "model_convention_ids": ["FIXTURE-CALENDAR-01"],
            "approved_review_context_schema": 1,
        }
        ledger = {
            "model_conventions": [
                {
                    "id": "FIXTURE-CALENDAR-01",
                    "source_locator": "source.txt:1",
                    "classification": "source_text_model_convention",
                    "formal_meaning": "Counts are indexed by calendar event time.",
                    "why_needed": "Events can begin before the observation window.",
                    "checked_scope": "The direct claim and its process prerequisites.",
                }
            ]
        }
        contexts, error = materialize_approved_review_contexts(
            record, source_proof_fidelity=ledger
        )
        self.assertEqual(error, "")
        record[APPROVED_REVIEW_CONTEXTS_FIELD] = contexts

        text, identity, error = source_semantic_input_bundle(record)

        self.assertEqual(error, "")
        self.assertEqual(text, "Claim")
        self.assertRegex(identity, r"^[0-9a-f]{64}$")
        self.assertEqual(
            contexts[0]["formal_meaning"],
            "Counts are indexed by calendar event time.",
        )
        changed_ledger = {
            "model_conventions": [
                {
                    **ledger["model_conventions"][0],
                    "formal_meaning": "Counts are indexed by birth cohort.",
                }
            ]
        }
        changed, error = materialize_approved_review_contexts(
            record, source_proof_fidelity=changed_ledger
        )
        self.assertEqual(error, "")
        changed_record = {**record, APPROVED_REVIEW_CONTEXTS_FIELD: changed}
        changed_text, changed_identity, changed_error = source_semantic_input_bundle(
            changed_record
        )
        self.assertEqual(changed_error, "")
        self.assertEqual(changed_text, text)
        self.assertNotEqual(changed_identity, identity)

    def test_cited_approval_context_must_be_prepared(self) -> None:
        record = {
            "source_anchor_evidence": [anchor("source.txt", "Claim")],
            "model_convention_ids": ["FIXTURE-CALENDAR-01"],
            "approved_review_context_schema": 1,
        }
        text, identity, error = source_semantic_input_bundle(record)
        self.assertEqual(text, "")
        self.assertEqual(identity, "")
        self.assertIn("no prepared approved_review_contexts", error)

    def test_unknown_context_role_fails_closed(self) -> None:
        record = {
            "source_anchor_evidence": [anchor("source.txt", "Claim")],
            "semantic_context_requirements": [
                {
                    "semantic_role": "invented_proof",
                    "source_anchor_evidence": [anchor("source.txt", "Context", line=2)],
                }
            ],
        }
        _text, _identity, error = source_semantic_input_bundle(
            record, require_context_roles=True
        )
        self.assertIn("no permitted semantic_role", error)

    def test_semantic_bundle_preserves_byte_pinned_extraction_control_character(self) -> None:
        record = {
            "source_anchor_evidence": [
                anchor("source.txt", "The algorithm uses \x0f accuracy.")
            ]
        }
        text, identity, error = source_semantic_input_bundle(record)
        self.assertEqual(error, "")
        self.assertIn("\x0f", text)
        self.assertRegex(identity, r"^[0-9a-f]{64}$")

    def test_semantic_bundle_allows_layout_controls(self) -> None:
        record = {
            "source_anchor_evidence": [
                anchor("source.txt", "First page\fSecond page\n\tIndented")
            ]
        }
        text, identity, error = source_semantic_input_bundle(record)
        self.assertEqual(error, "")
        self.assertIn("\f", text)
        self.assertRegex(identity, r"^[0-9a-f]{64}$")

    def test_frozen_bytes_are_authoritative_and_never_fall_through(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            source = paper / "source.txt"
            source.write_text("Claim\n", encoding="utf-8")
            record = {"source_anchor_evidence": [anchor("source.txt", "Claim")]}
            frozen = {source.resolve(): b"Claim\n"}
            source.write_text("Changed after freeze\n", encoding="utf-8")

            self.assertEqual(
                source_anchor_file_error(
                    paper,
                    record,
                    repository_root=root,
                    file_bytes_override=frozen,
                ),
                "",
            )
            error = source_anchor_file_error(
                paper,
                record,
                repository_root=root,
                file_bytes_override={},
            )
            self.assertIn("absent from the frozen transaction", error)

    def test_source_path_cannot_escape_paper_folder(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            outside = root / "outside.txt"
            outside.write_text("Claim\n", encoding="utf-8")
            error = source_anchor_file_error(
                paper,
                {"source_anchor_evidence": [anchor("../../outside.txt", "Claim")]},
                repository_root=root,
            )
            self.assertIn("cannot read the declared source path", error)

    def test_statement_digest_is_whitespace_stable(self) -> None:
        self.assertEqual(statement_digest(" A\n B "), statement_digest("A B"))


if __name__ == "__main__":
    unittest.main()
