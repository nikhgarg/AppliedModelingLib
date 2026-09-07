#!/usr/bin/env python3
"""Focused regressions for scanned-PDF/text source companions."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import audit_evidence_integrity as integrity  # noqa: E402
from scripts import review_dashboard  # noqa: E402
from scripts import source_artifact_companion as companion  # noqa: E402
from scripts import source_coverage_scope as coverage  # noqa: E402
from scripts import source_named_result_index as source_index  # noqa: E402


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class SourceTextCompanionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper = self.root / "papers" / "FixturePaper"
        (self.paper / "audit").mkdir(parents=True)
        self.text = self.paper / "source.txt"
        self.primary = self.paper / "visual-source.pdf"
        self.transcript_input = self.paper / "ocr-input.pdf"
        self.semantic_transcription = self.paper / "visual-review.md"
        self.text.write_text(
            "Theorem 1. Every admissible input has a witness.\n"
            "Definition 2. A witness is designated.\n",
            encoding="utf-8",
        )
        # File identity rather than PDF parsing is the companion's concern:
        # pdftotext invocation and visual comparison are separately recorded.
        self.primary.write_bytes(b"%PDF-fixture-visual\n")
        self.transcript_input.write_bytes(b"%PDF-fixture-transcript-input\n")
        self.semantic_transcription.write_text(
            "Theorem 1. Every admissible input has a witness.\n"
            "Definition 2. A witness is designated.\n",
            encoding="utf-8",
        )

    def payload(self) -> dict[str, object]:
        theorem_quote = self.text.read_text(encoding="utf-8").splitlines()[0]
        return {
            "source_coverage_mode": "named_theoretical_statements",
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": sha256(self.text),
            "source_text_companion": {
                "schema": 1,
                "canonical_text": {"path": "source.txt", "sha256": sha256(self.text)},
                "visual_primary_scan": {
                    "path": "visual-source.pdf",
                    "sha256": sha256(self.primary),
                },
                "transcript_input_scan": {
                    "path": "ocr-input.pdf",
                    "sha256": sha256(self.transcript_input),
                },
                "extraction": {"tool": "pdftotext", "options": ["-layout"]},
                "page_map": [
                    {
                        "line_start": 1,
                        "line_end": 1,
                        "pdf_page": 1,
                        "printed_page": 9,
                    },
                    {
                        "line_start": 2,
                        "line_end": 2,
                        "pdf_page": 2,
                        "printed_page": 10,
                    },
                ],
                "visual_comparison_attestation": {
                    "complete": True,
                    "method": "Compared each mapped transcript page against the primary scan.",
                },
            },
            "items": {
                # The opaque map key and deliberately unrelated Lean route do
                # not participate in source-only presentation discovery.
                "opaque_source_record": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [
                        {
                            "path": "source.txt",
                            "line_start": 1,
                            "line_end": 1,
                            "quoted_text": theorem_quote,
                            "quoted_text_sha256": hashlib.sha256(
                                theorem_quote.encode("utf-8")
                            ).hexdigest(),
                        }
                    ],
                    "lean_declarations": ["Fixture.unrelated_name"],
                }
            },
        }

    def test_valid_companion_binds_visual_provenance_to_canonical_text(self) -> None:
        payload = self.payload()
        self.assertEqual(
            companion.source_text_companion_validation_issues(
                self.paper, payload, repository_root=self.root
            ),
            [],
        )

        previous_root = integrity.ROOT
        integrity.ROOT = self.root
        self.addCleanup(setattr, integrity, "ROOT", previous_root)
        findings = integrity.source_artifact_pin_findings(
            self.paper,
            "formalized",
            self.paper / "audit" / "paper_statement_map.json",
            payload,
        )
        self.assertEqual(findings, [])

        selected = coverage.source_index_byte_pinned_anchor_item_ids(
            self.paper,
            payload,
            "named_theoretical_statements",
            repository_root=self.root,
        )
        self.assertEqual(selected, {"opaque_source_record"})

    def test_frozen_byte_map_prevents_live_companion_rereads(self) -> None:
        payload = self.payload()
        frozen = {
            path.resolve(): path.read_bytes()
            for path in (self.text, self.primary, self.transcript_input)
        }
        self.text.write_text("replacement\n", encoding="utf-8")
        self.primary.write_bytes(b"replacement visual")
        self.transcript_input.write_bytes(b"replacement input")

        self.assertEqual(
            companion.source_text_companion_validation_issues(
                self.paper,
                payload,
                repository_root=self.root,
                file_bytes_override=frozen,
            ),
            [],
        )
        self.assertEqual(
            coverage.source_index_byte_pinned_anchor_item_ids(
                self.paper,
                payload,
                "named_theoretical_statements",
                repository_root=self.root,
                file_bytes_override=frozen,
            ),
            {"opaque_source_record"},
        )
        self.assertTrue(
            companion.source_text_companion_validation_issues(
                self.paper, payload, repository_root=self.root
            )
        )

        omitted = dict(frozen)
        omitted.pop(self.primary.resolve())
        messages = [
            issue.message
            for issue in companion.source_text_companion_validation_issues(
                self.paper,
                payload,
                repository_root=self.root,
                file_bytes_override=omitted,
            )
        ]
        self.assertTrue(any("frozen input bundle omits" in message for message in messages))

    def test_top_level_source_pin_must_equal_canonical_transcript_pin(self) -> None:
        payload = self.payload()
        payload["source_artifact_path"] = "other.txt"
        messages = [
            issue.message
            for issue in companion.source_text_companion_validation_issues(
                self.paper, payload, repository_root=self.root
            )
        ]
        self.assertTrue(
            any("must exactly equal" in message for message in messages), messages
        )

    def test_visual_semantic_transcription_is_pinned_and_bound_to_primary_scan(self) -> None:
        payload = self.payload()
        companion_payload = payload["source_text_companion"]
        assert isinstance(companion_payload, dict)
        companion_payload["semantic_review_transcription"] = {
            "schema": 1,
            "path": "visual-review.md",
            "sha256": sha256(self.semantic_transcription),
            "controlling_visual_source": {
                "path": "visual-source.pdf",
                "sha256": sha256(self.primary),
            },
            "complete_for_selected_semantic_surface": True,
            "method": "Visually transcribed selected mathematical passages.",
        }
        self.assertEqual(
            companion.source_text_companion_validation_issues(
                self.paper, payload, repository_root=self.root
            ),
            [],
        )
        self.assertEqual(
            companion.semantic_review_source_identity(payload),
            ("visual-review.md", sha256(self.semantic_transcription)),
        )

        transcription = companion_payload["semantic_review_transcription"]
        assert isinstance(transcription, dict)
        transcription["controlling_visual_source"] = {
            "path": "other.pdf",
            "sha256": "0" * 64,
        }
        messages = [
            issue.message
            for issue in companion.source_text_companion_validation_issues(
                self.paper, payload, repository_root=self.root
            )
        ]
        self.assertTrue(
            any("controlling_visual_source must exactly equal" in message for message in messages),
            messages,
        )
        self.assertEqual(
            companion.semantic_review_source_identity(payload),
            ("source.txt", sha256(self.text)),
        )

    def test_scan_hashes_and_path_safety_are_checked_independently(self) -> None:
        payload = self.payload()
        companion_payload = payload["source_text_companion"]
        assert isinstance(companion_payload, dict)
        primary = companion_payload["visual_primary_scan"]
        assert isinstance(primary, dict)
        primary["sha256"] = "0" * 64
        transcript_input = companion_payload["transcript_input_scan"]
        assert isinstance(transcript_input, dict)
        transcript_input["path"] = "../outside.pdf"
        messages = [
            issue.message
            for issue in companion.source_text_companion_validation_issues(
                self.paper, payload, repository_root=self.root
            )
        ]
        self.assertTrue(any("visual_primary_scan.sha256 does not match" in message for message in messages), messages)
        self.assertTrue(any("transcript_input_scan.path path escapes" in message for message in messages), messages)

    def test_extraction_attestation_and_page_map_fail_closed(self) -> None:
        payload = self.payload()
        companion_payload = payload["source_text_companion"]
        assert isinstance(companion_payload, dict)
        extraction = companion_payload["extraction"]
        assert isinstance(extraction, dict)
        extraction["tool"] = "ocr"
        extraction["options"] = "-layout"
        attestation = companion_payload["visual_comparison_attestation"]
        assert isinstance(attestation, dict)
        attestation["complete"] = False
        attestation["method"] = ""
        page_map = companion_payload["page_map"]
        assert isinstance(page_map, list)
        page_map[1] = {
            "line_start": 3,
            "line_end": 3,
            "pdf_page": 2,
            "printed_page": 10,
        }
        messages = [
            issue.message
            for issue in companion.source_text_companion_validation_issues(
                self.paper, payload, repository_root=self.root
            )
        ]
        self.assertTrue(any("extraction.tool" in message for message in messages), messages)
        self.assertTrue(any("extraction.options" in message for message in messages), messages)
        self.assertTrue(any("attestation.complete" in message for message in messages), messages)
        self.assertTrue(any("attestation.method" in message for message in messages), messages)
        self.assertTrue(any("not contiguous" in message for message in messages), messages)
        self.assertTrue(any("exceeds the 2-line" in message for message in messages), messages)

    def test_dashboard_precheck_reports_invalid_companion(self) -> None:
        payload = self.payload()
        payload["source_artifact_sha256"] = "0" * 64
        map_path = self.paper / "audit" / "paper_statement_map.json"
        map_path.write_text(json.dumps(payload), encoding="utf-8")
        previous_root = review_dashboard.ROOT
        review_dashboard.ROOT = self.root
        self.addCleanup(setattr, review_dashboard, "ROOT", previous_root)
        errors = review_dashboard.paper_source_map_structural_errors(self.paper)
        self.assertTrue(
            any("source_text_companion" in error and "source_artifact_sha256" in error for error in errors),
            errors,
        )

    def test_structural_checkout_keeps_malformed_companion_errors(self) -> None:
        """Missing licensed bytes must not suppress companion schema checks."""

        payload = self.payload()
        self.text.unlink()
        companion_payload = payload["source_text_companion"]
        assert isinstance(companion_payload, dict)
        companion_payload["schema"] = 0
        visual = companion_payload["visual_primary_scan"]
        assert isinstance(visual, dict)
        visual["path"] = "../outside.pdf"
        page_map = companion_payload["page_map"]
        assert isinstance(page_map, list)
        first_page = page_map[0]
        assert isinstance(first_page, dict)
        first_page["line_start"] = 0

        previous_root = integrity.ROOT
        integrity.ROOT = self.root
        self.addCleanup(setattr, integrity, "ROOT", previous_root)
        findings = integrity.source_artifact_pin_findings(
            self.paper,
            "formalized",
            self.paper / "audit" / "paper_statement_map.json",
            payload,
            require_source_bytes=False,
        )

        self.assertTrue(
            any(
                finding.severity == "WARN"
                and "not release certification" in finding.message
                for finding in findings
            ),
            findings,
        )
        self.assertTrue(
            any(
                finding.severity == "WARN"
                and "canonical_text.path does not exist" in finding.message
                for finding in findings
            ),
            findings,
        )
        for fragment in (
            "source_text_companion.schema must equal",
            "visual_primary_scan.path path escapes",
            "page_map[0].line_start and source_text_companion.page_map[0].line_end",
        ):
            self.assertTrue(
                any(
                    finding.severity == "ERROR" and fragment in finding.message
                    for finding in findings
                ),
                findings,
            )


class UnnumberedDefinitionParserTests(unittest.TestCase):
    def test_visibly_headed_definition_has_a_bounded_sentence_span(self) -> None:
        source = (
            "DEFINITION.\n"
            "An assignment is unstable when a blocking pair exists.\n"
            "This later prose is not part of the first-sentence definition.\n"
            "Theorem 1. Every stable assignment exists.\n"
        )
        presentations = source_index.extract_text_named_result_presentations(source)
        self.assertEqual(
            [
                (item.kind, item.label, item.line_start, item.line_end, item.presentation)
                for item in presentations
            ],
            [
                ("definition", "Definition@1", 1, 2, "text_unnumbered_definition"),
                ("theorem", "Theorem 1", 4, 4, "text_heading"),
            ],
        )

    def test_lowercase_or_unbounded_definition_prose_is_not_promoted(self) -> None:
        source = (
            "Definition. This ordinary prose is not an all-caps headed block.\n"
            "DEFINITION. A scan fragment without a completed sentence\n"
            "continues one\n"
            "continues two\n"
            "continues three\n"
            "continues four\n"
            "continues five\n"
            "continues six\n"
            "continues seven\n"
            "continues eight.\n"
        )
        self.assertEqual(source_index.extract_text_named_result_presentations(source), [])


if __name__ == "__main__":
    unittest.main()
